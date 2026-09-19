(** Main typechecker module *)

open Syntax
open Defs
open Monads
open Kinds

(** Generate a fresh metavariable *)
let fresh_metavar (st : state) : typ * state =
  let n, st = fresh_id st in
  (TMetaVar n, st)

(** Apply the type and kind substitutions of [st] to a type *)
let rec zonk (st : state) (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TVar _ -> t
  | TMetaVar x -> (
      match lookup_subst st.tsubst x with Some t' -> zonk st t' | None -> t)
  | TArrow (t1, t2) -> TArrow (zonk st t1, zonk st t2)
  | TApp (t1, t2) -> TApp (zonk st t1, zonk st t2)
  | TForall (v, k, t') -> TForall (v, Option.map (kzonk st.ksubst) k, zonk st t')
  | TLam (v, k, t') -> TLam (v, Option.map (kzonk st.ksubst) k, zonk st t')

(** Whether a metavariable [x] occurs in a type [t] *)
let rec occurs (x : int) (t : typ) : bool =
  match t with
  | TMetaVar x' -> x = x'
  | TArrow (t1, t2) | TApp (t1, t2) -> occurs x t1 || occurs x t2
  | TForall (_, _, t') | TLam (_, _, t') -> occurs x t'
  | TUnit | TBool | TNat | TVar _ -> false

(** Whether a type mentions any metavariables *)
let rec has_metavars (t : typ) : bool =
  match t with
  | TMetaVar _ -> true
  | TArrow (t1, t2) | TApp (t1, t2) -> has_metavars t1 || has_metavars t2
  | TForall (_, _, t') | TLam (_, _, t') -> has_metavars t'
  | TUnit | TBool | TNat | TVar _ -> false

(** Every type variable name mentioned in [t], bound or free *)
let rec tnames (t : typ) : string list =
  match t with
  | TVar v -> [ v ]
  | TArrow (t1, t2) | TApp (t1, t2) -> tnames t1 @ tnames t2
  | TForall (v, _, t') | TLam (v, _, t') -> v :: tnames t'
  | TUnit | TBool | TNat | TMetaVar _ -> []

(** Normalize type expressions via beta reduction

    Assumes [t] is well-kinded to guarantee termination *)
let rec beta_reduce_typ (g : typctx) (t : typ) : typ =
  match t with
  | TVar v -> (
      match lookup_alias g v with
      | Some (t', _) -> beta_reduce_typ g t'
      | None -> t)
  | TApp (t1, t2) -> (
      match beta_reduce_typ g t1 with
      | TLam (x, _, body) -> beta_reduce_typ g (tcas body x t2)
      | t1' -> TApp (t1', t2))
  | _ -> t

(** Like [beta_reduce_typ], but leaves alias names (['x]) untouched. For
    normalizing a type that is about to be displayed to the user *)
let rec beta_reduce_typ_display (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TMetaVar _ | TVar _ -> t
  | TApp (t1, t2) -> (
      let t1_norm = beta_reduce_typ_display t1 in
      let t2_norm = beta_reduce_typ_display t2 in
      match t1_norm with
      | TLam (x, _, t') -> beta_reduce_typ_display (tcas t' x t2_norm)
      | _ -> TApp (t1_norm, t2_norm))
  | TArrow (t1, t2) ->
      TArrow (beta_reduce_typ_display t1, beta_reduce_typ_display t2)
  | TForall (x, k, t') -> TForall (x, k, beta_reduce_typ_display t')
  | TLam (x, k, t') -> TLam (x, k, beta_reduce_typ_display t')

(** Fail if the type variable [v] appears free in the type of any term in [g] *)
let check_escape (st : state) (g : typctx) (v : string) : (unit, string) result
    =
  match
    List.find_opt (fun (_, ty) -> List.mem v (tfree (zonk st ty))) g.terms
  with
  | None -> return ()
  | Some (x, ty) ->
      fail
        (Printf.sprintf
           "Type variable %s would escape its scope through the type of %s: %s"
           v x
           (string_of_typ (zonk st ty)))

(** Generate fresh rigid type variables for comparing the bodies of binders *)
let fresh_rigid (st : state) (base : string) : string * state =
  let n, st = fresh_id st in
  (Printf.sprintf "%s#%d" base n, st)

(** Unify [s] and [t] under [g], extending the current substitution *)
let rec unify (st : state) (g : typctx) (s : typ) (t : typ) :
    (state, string) result =
  let s = zonk st s and t = zonk st t in
  match (s, t) with
  | TMetaVar x, TMetaVar y when x = y -> return st
  | TMetaVar x, u | u, TMetaVar x ->
      if occurs x u then
        fail
          (Printf.sprintf "Type unification failure, %s <> %s"
             (string_of_typ (TMetaVar x))
             (string_of_typ u))
      else return { st with tsubst = (x, u) :: st.tsubst }
  | _ -> (
      match (beta_reduce_typ g s, beta_reduce_typ g t) with
      | TUnit, TUnit | TBool, TBool | TNat, TNat -> return st
      | TVar a, TVar b when a = b -> return st
      | TArrow (s1, s2), TArrow (t1, t2) ->
          let* st = unify st g s1 t1 in
          unify st g s2 t2
      | TApp (s1, s2), TApp (t1, t2) ->
          let* st = unify st g s1 t1 in
          unify st g s2 t2
      | TForall (a, k1, sb), TForall (b, k2, tb)
      | TLam (a, k1, sb), TLam (b, k2, tb) ->
          let k1, st = binder_kind st k1 in
          let k2, st = binder_kind st k2 in
          let* st = kunify st k1 k2 in
          let c, st = fresh_rigid st a in
          let* st = unify st g (tcas sb a (TVar c)) (tcas tb b (TVar c)) in
          let* () = check_escape st g c in
          return st
      | _ ->
          fail
            (Printf.sprintf "Type unification failure, %s <> %s"
               (string_of_typ s) (string_of_typ t)))

(** Infer the type of an [sterm] under context [g] *)
let rec infer (st : state) (g : typctx) (t : sterm) :
    (typ * state, string) result =
  match t with
  (* T-Var *)
  | SVar x -> (
      match lookup_term g x with
      | None -> fail (Printf.sprintf "Couldn't determine type of %s" x)
      | Some ty -> return (ty, st))
  | SUnit -> return (TUnit, st)
  | STrue | SFalse -> return (TBool, st)
  | SNat _ -> return (TNat, st)
  (* T-Abs *)
  | SLam (x, Some t1, e) ->
      let* t1', st = check_proper_type st g t1 in
      let* t2, st = infer st (update_term g x t1') e in
      return (TArrow (t1', t2), st)
  | SLam (x, None, e) ->
      let t1, st = fresh_metavar st in
      let* t2, st = infer st (update_term g x t1) e in
      return (TArrow (t1, t2), st)
  (* T-If *)
  | SIfthenelse (b, e1, e2) ->
      let* t1, st = infer st g b in
      let* st = unify st g t1 TBool in
      let* t2, st = infer st g e1 in
      let* t3, st = infer st g e2 in
      let* st = unify st g t2 t3 in
      return (t2, st)
  | SIseq (x1, x2) ->
      let* t1, st = infer st g x1 in
      let* st = unify st g t1 TNat in
      let* t2, st = infer st g x2 in
      let* st = unify st g t2 TNat in
      return (TBool, st)
  (* T-App *)
  | SApp (e1, e2) ->
      let* t1, st = infer st g e1 in
      let* t2, st = infer st g e2 in
      let x, st = fresh_metavar st in
      let* st = unify st g t1 (TArrow (t2, x)) in
      return (x, st)
  | SAnn (e, ty) ->
      let* ty', st = check_proper_type st g ty in
      let* t, st = infer st g e in
      let* st = unify st g ty' t in
      return (ty', st)
  | STLam (x, e) ->
      let kappa, st = fresh_kmetavar st in
      let avoid =
        List.concat_map
          (fun (_, ty) ->
            let ty = zonk st ty in
            if has_metavars ty then tnames ty else [])
          g.terms
      in
      let x' = fresh_tyvar_name ~avoid g x in
      let* t, st = infer st (update_tyvar g x x' kappa) e in
      let* () = check_escape st g x' in
      return (TForall (x', Some kappa, t), st)
  | SPolyApp (e, ty) -> (
      let* t, st = infer st g e in
      match beta_reduce_typ g (zonk st t) with
      | TForall (alpha, k, body) ->
          let* ty', k', st = check_type st g ty in
          let k, st = binder_kind st k in
          let* st = kunify st k' k in
          return (tcas body alpha ty', st)
      | TMetaVar _ ->
          fail
            (Printf.sprintf
               "Can't apply %s to a type, since its type is not yet known to \
                be polymorphic; try annotating it"
               (string_of_sterm e))
      | t' ->
          fail
            (Printf.sprintf "Expected a polymorphic type but got %s"
               (string_of_typ t')))
  | SLet (v, Some ty, e1, e2) -> infer st g (SLet (v, None, SAnn (e1, ty), e2))
  | SLet (v, None, e1, e2) ->
      let* t1, st = infer st g e1 in
      infer st (update_term g v t1) e2

(** Erase the types of an [sterm] *)
let rec erase (t : sterm) : term =
  match t with
  | SUnit -> Unit
  | STrue -> True
  | SFalse -> False
  | SNat n -> Nat n
  | SVar v -> Var v
  | SIfthenelse (b, e1, e2) -> Ifthenelse (erase b, erase e1, erase e2)
  | SIseq (x1, x2) -> Iseq (erase x1, erase x2)
  | SLam (s, _, e) -> Lam (s, erase e)
  | SApp (e1, e2) -> App (erase e1, erase e2)
  | SAnn (e, _) -> erase e
  | STLam (_, e) -> erase e
  | SPolyApp (e, _) -> erase e
  | SLet (v, _, e1, e2) -> App (Lam (v, erase e2), erase e1)

(** Apply substitutions, default unsolved kinds to [*], and prevent type
    variable escapes *)
let finalize (st : state) (g : typctx) (t : typ) : (typ, string) result =
  let t = map_kinds (kdefault st.ksubst) (zonk st t) in
  match List.find_opt (fun v -> lookup_alias g v = None) (tfree t) with
  | Some v ->
      fail
        (Printf.sprintf "Type variable %s escapes its scope in %s" v
           (string_of_typ t))
  | None -> return t

(** Typecheck an [sterm] in context [g] *)
let typecheck (g : typctx) (t : sterm) : (typed_term, string) result =
  let* ty, st = infer empty_state g t in
  let* ty = finalize st g ty in
  return (erase t, beta_reduce_typ_display ty)

(** Typecheck a top-level [sphrase] under [gamma], producing its type-erased
    [phrase], its [typ], and the context under which subsequent phrases should
    be typechecked. *)
let typecheck_phrase (gamma : typctx) (p : sphrase) :
    (typctx * phrase option * typ, string) result =
  match p with
  | SPTerm t ->
      let* t', ty = typecheck gamma t in
      return (gamma, Some (PTerm t'), ty)
  | SPDef (x, ann, e) ->
      let e = match ann with Some ty -> SAnn (e, ty) | None -> e in
      let* e', ty = typecheck gamma e in
      if has_metavars ty then
        fail
          (Printf.sprintf
             "The type of %s: (%s) is not fully determined. Try annotating it" x
             (string_of_typ ty))
      else return (update_term gamma x ty, Some (PDef (x, e')), ty)
  | SPTypedef (x, t) ->
      let* t', k, st = check_type empty_state gamma t in
      let* t' = finalize st gamma t' in
      return (update_alias gamma x t' (kdefault st.ksubst k), None, t')
