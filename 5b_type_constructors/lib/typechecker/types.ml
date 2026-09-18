(** Main typechecker module *)

open Syntax
open Monads
open Defs
open Kinds

(** Normalize type expressions *)
let rec beta_reduce_typ g (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TMetaVar _ -> t
  | TVar v -> (
      match lookup_alias g v with None -> t | Some t' -> beta_reduce_typ g t')
  | TApp (t1, t2) -> (
      let t1_norm = beta_reduce_typ g t1 in
      let t2_norm = beta_reduce_typ g t2 in
      match t1_norm with
      (* E-AppAbs *)
      | TLam (x, k, t') -> beta_reduce_typ g (tcas t' x t2_norm)
      (* Proper type applied to something *)
      | _ -> TApp (t1_norm, t2_norm))
  | TArrow (t1, t2) -> TArrow (beta_reduce_typ g t1, beta_reduce_typ g t2)
  | TForall (x, k, t') -> TForall (x, k, beta_reduce_typ g t')
  | TLam (x, k, t') -> TLam (x, k, beta_reduce_typ g t')

(** Like [beta_reduce_typ], but leaves alias names (['x]) untouched. For
    normalizing a type that is about to be displayed to the user *)
let rec beta_reduce_typ_display (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TMetaVar _ | TVar _ -> t
  | TApp (t1, t2) -> (
      let t1_norm = beta_reduce_typ_display t1 in
      let t2_norm = beta_reduce_typ_display t2 in
      match t1_norm with
      | TLam (x, k, t') -> beta_reduce_typ_display (tcas t' x t2_norm)
      | _ -> TApp (t1_norm, t2_norm))
  | TArrow (t1, t2) ->
      TArrow (beta_reduce_typ_display t1, beta_reduce_typ_display t2)
  | TForall (x, k, t') -> TForall (x, k, beta_reduce_typ_display t')
  | TLam (x, k, t') -> TLam (x, k, beta_reduce_typ_display t')

(** Assumes t1 and t2 are beta-reduced already *)
let rec types_eq (t1 : typ) (t2 : typ) : bool =
  match (t1, t2) with
  | TVar x, TVar y -> x = y
  | TMetaVar x, TMetaVar y -> x = y
  | TUnit, TUnit | TBool, TBool | TNat, TNat -> true
  | TArrow (lhs1, rhs1), TArrow (lhs2, rhs2) ->
      types_eq lhs1 lhs2 && types_eq rhs1 rhs2
  | TApp (f1, a1), TApp (f2, a2) -> types_eq f1 f2 && types_eq a1 a2
  | TLam (x1, k1, body1), TLam (x2, k2, body2) ->
      k1 = k2
      &&
      if x1 = x2 then types_eq body1 body2
      else
        let gamma = fresh "gamma" (tfree body1 @ tfree body2) in
        types_eq (tcas body1 x1 (TVar gamma)) (tcas body2 x2 (TVar gamma))
  | TForall (x1, k1, body1), TForall (x2, k2, body2) ->
      k1 = k2
      &&
      if x1 = x2 then types_eq body1 body2
      else
        let gamma = fresh "gamma" (tfree body1 @ tfree body2) in
        types_eq (tcas body1 x1 (TVar gamma)) (tcas body2 x2 (TVar gamma))
  | _, _ -> false

let type_wf (gamma : typctx) (t : typ) : (kind constr_set, string) result =
  let* k, c = get_kind_constraints gamma t in
  return (c @ [ (k, KProper) ])

(** Perform the type substitution s(t) *)
let rec type_subst (s : typ subst) (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TVar _ -> t
  | TArrow (t1, t2) -> TArrow (type_subst s t1, type_subst s t2)
  | TForall (x, k, t') -> TForall (x, k, type_subst s t')
  | TApp (t1, t2) -> TApp (type_subst s t1, type_subst s t2)
  | TLam (x, k, t') -> TLam (x, k, type_subst s t')
  | TMetaVar x -> (
      match lookup_subst s x with Some t -> t | None -> TMetaVar x)

module C = Counter (struct
  type v = typ

  let f x = TMetaVar x
end)

(** Generate fresh metavariables

    This function is monotonic and will never return a duplicate metavariable
    within a session *)
let fresh_metavar = C.fresh

(** Reset the metavariable counter, e.g. at the start of a new typechecking
    session *)
let reset_metavar_counter = C.reset

(** Generate a set of typing constraints and a type [ty] required for an [sterm]
    to have type [ty] under context [g] *)
let rec get_constraints (g : typctx) (t : sterm) :
    (typ * typ constr_set * kind constr_set, string) result =
  match t with
  (* CT-Var: x:T \in G => G |- x : T | {} *)
  | SVar x -> (
      match lookup_term g x with
      | None -> fail (Printf.sprintf "Couldn't determine type of %s" x)
      | Some ty' -> return (ty', [], []))
  | SUnit -> return (TUnit, [], [])
  | STrue | SFalse -> return (TBool, [], [])
  | SNat _ -> return (TNat, [], [])
  (* CT-Abs: G[x := t1] |- e : t2' | C => G |- \x:t1.t2 : t1' -> t2' | C *)
  | SLam (x, Some t1, e) ->
      let* tc = type_wf g t1 in
      let* t2, c, k = get_constraints (update_term g x t1) e in
      return (TArrow (t1, t2), c, tc @ k)
  | SLam (x, None, e) ->
      let t1 = fresh_metavar () in
      let* t2, c, k = get_constraints (update_term g x t1) e in
      return (TArrow (t1, t2), c, k)
  (* CT-If: *)
  | SIfthenelse (b, e1, e2) ->
      let* t1, c1, k1 = get_constraints g b in
      let* t2, c2, k2 = get_constraints g e1 in
      let* t3, c3, k3 = get_constraints g e2 in
      return (t2, c1 @ c2 @ c3 @ [ (t1, TBool); (t2, t3) ], k1 @ k2 @ k3)
  | SIseq (x1, x2) ->
      let* t1, c1, k1 = get_constraints g x1 in
      let* t2, c2, k2 = get_constraints g x2 in
      return (TBool, c1 @ c2 @ [ (t1, TNat); (t2, TNat) ], k1 @ k2)
  (* CT-App: G |- e1 : t1 | c1 => G |- e2 : T2 | C2 => G |- e1 e2 : x | C' *)
  | SApp (e1, e2) ->
      let* t1, c1, k1 = get_constraints g e1 in
      let* t2, c2, k2 = get_constraints g e2 in
      let x = fresh_metavar () in
      return (x, c1 @ c2 @ [ (t1, TArrow (t2, x)) ], k1 @ k2)
  | SAnn (e, ty) ->
      let* k1 = type_wf g ty in
      let* t, c, k2 = get_constraints g e in
      return (ty, c @ [ (ty, t) ], k1 @ k2)
  | STLam (x, None, e) ->
      let kappa = fresh_kmetavar () in
      let* t, c, k = get_constraints (update_tyvar g x kappa) e in
      return (TForall (x, kappa, t), c, k)
  | STLam (x, Some kappa, e) ->
      let* t, c, k = get_constraints (update_tyvar g x kappa) e in
      return (TForall (x, kappa, t), c, k)
  | SPolyApp (e, kappa) -> (
      let* t, c, ek = get_constraints g e in
      match beta_reduce_typ g t with
      | TForall (alpha, k, body) ->
          (* the instantiation's kind need not be [*]: it must match
             whatever kind [alpha] was bound at *)
          let* kappak, kc = get_kind_constraints g kappa in
          return (tcas body alpha kappa, c, ek @ kc @ [ (kappak, k) ])
      | _ ->
          fail
            (Printf.sprintf "expected a polymorphic type but got %s"
               (string_of_typ t)))
  | SLet (v, Some t, e1, e2) ->
      let* k1 = type_wf g t in
      let* t1, c1, kc1 = get_constraints g e1 in
      let* t2, c2, kc2 = get_constraints (update_term g v t) e2 in
      return (t2, c1 @ c2 @ [ (t, t1) ], k1 @ kc1 @ kc2)
  | SLet (v, None, e1, e2) ->
      let* t1, c1, kc1 = get_constraints g e1 in
      let* t2, c2, kc2 = get_constraints (update_term g v t1) e2 in
      return (t2, c1 @ c2, kc1 @ kc2)
  | _ -> return (TUnit, [], [])
(* | SPair (x, y) ->
      let* t1, c1 = get_constraints g x in
      let* t2, c2 = get_constraints g y in
      return (TProd (t1, t2), c1 @ c2)
  | SFst x ->
      let* t, c = get_constraints g x in
      let v1, v2 = (fresh_metavar (), fresh_metavar ()) in
      return (v1, c @ [ (t, TProd (v1, v2)) ])
  | SSnd x ->
      let* t, c = get_constraints g x in
      let v1, v2 = (fresh_metavar (), fresh_metavar ()) in
      return (v2, c @ [ (t, TProd (v1, v2)) ])
  | SInl x ->
      let* t, c = get_constraints g x in
      let v2 = fresh_metavar () in
      return (TSum (t, v2), c)
  | SInr x ->
      let* t, c = get_constraints g x in
      let v1 = fresh_metavar () in
      return (TSum (v1, t), c)
  | SMatch (x, y, e1, z, e2) ->
      let* tx, cx = get_constraints g x in
      let mv1, mv2 = (fresh_metavar (), fresh_metavar ()) in
      let* te1, ce1 = get_constraints (update_term g y mv1) e1 in
      let* te2, ce2 = get_constraints (update_term g z mv2) e2 in
      return (te1, cx @ ce1 @ ce2 @ [ (tx, TSum (mv1, mv2)); (te1, te2) ])
  | SNil ->
      let mv = fresh_metavar () in
      return (TList mv, [])
  | SCons (h, t) ->
      let* th, ch = get_constraints g h in
      let* tt, ct = get_constraints g t in
      return (TList th, ch @ ct @ [ (tt, TList th) ])
  | SListMatch (l, e1, h, t, e2) ->
      let* tl, cl = get_constraints g l in
      let elem = fresh_metavar () in
      let* te1, ce1 = get_constraints g e1 in
      let* te2, ce2 =
        get_constraints (update_term (update_term g h elem) t (TList elem)) e2
      in
      return (te1, cl @ ce1 @ ce2 @ [ (tl, TList elem); (te1, te2) ]) *)

(** Whether a metavariable [x] occurs in a type [t] *)
let rec occurs (x : int) (t : typ) : bool =
  match t with
  | TMetaVar x' when x = x' -> true
  | TArrow (t1, t2) | TApp (t1, t2) -> occurs x t1 || occurs x t2
  | TForall (_, _, t') | TLam (_, _, t') -> occurs x t'
  | _ -> false

let compose = Defs.compose type_subst
let constr_subst = Defs.constr_subst type_subst

(** Generate a solution to a set of type constraints through unification *)
let rec unify (g : typctx) (c : typ constr_set) : (typ subst, string) result =
  match c with
  | [] -> return []
  | (s, t) :: c' -> (
      let s = beta_reduce_typ g s and t = beta_reduce_typ g t in
      if types_eq s t then unify g c'
      else
        match (s, t) with
        | TMetaVar x, _ when not (occurs x t) ->
            let* c'' = unify g (constr_subst [ (x, t) ] c') in
            return (compose c'' [ (x, t) ])
        | _, TMetaVar x when not (occurs x s) ->
            let* c'' = unify g (constr_subst [ (x, s) ] c') in
            return (compose c'' [ (x, s) ])
        | TArrow (s1, s2), TArrow (t1, t2) ->
            unify g (c' @ [ (s1, t1); (s2, t2) ])
        | TApp (s1, s2), TApp (t1, t2) -> unify g (c' @ [ (s1, t1); (s2, t2) ])
        | TLam (a, k1, sb), TLam (b, k2, tb) ->
            if not (Kinds.kinds_eq k1 k2) then
              fail
                (Printf.sprintf "Kind mismatch in type-level lambda: %s vs %s"
                   (string_of_kind k1) (string_of_kind k2))
            else
              let c = fresh "c" (tfree sb @ tfree tb) in
              unify g ((tcas sb a (TVar c), tcas tb b (TVar c)) :: c')
        (* s = forall a.A, t = forall b.B

           This case only occurs when s and t are not alpha-equivalent,
           otherwise the types_eq would have returned true *)
        | TForall (a, k1, sb), TForall (b, k2, tb) ->
            if not (Kinds.kinds_eq k1 k2) then
              fail
                (Printf.sprintf "Kind mismatch in forall: %s vs %s"
                   (string_of_kind k1) (string_of_kind k2))
            else
              let c = fresh "c" (tfree sb @ tfree tb) in
              (* unify ({A[a := c] = B[b := c]} \cup c')*)
              unify g ((tcas sb a (TVar c), tcas tb b (TVar c)) :: c')
        | s, t ->
            fail
              (Printf.sprintf "Type unification failure, %s <> %s"
                 (string_of_typ s) (string_of_typ t)))

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
  | STLam (_, _, e) -> erase e
  | SPolyApp (e, _) -> erase e
  | SLet (v, _, e1, e2) -> App (Lam (v, erase e2), erase e1)
  (* pair a b = \f. f a b *)
  | SPair (a, b) -> Lam ("f", App (App (Var "f", erase a), erase b))
  (* fst p = p (\a.\b. a) *)
  | SFst p -> App (erase p, Lam ("a", Lam ("b", Var "a")))
  (* snd p = p (\a.\b. b) *)
  | SSnd p -> App (erase p, Lam ("a", Lam ("b", Var "b")))
  (* inl a = pair a true ;  inr a = pair a false
     (payload in fst, tag in snd) *)
  | SInl a -> Lam ("f", App (App (Var "f", erase a), True))
  | SInr a -> Lam ("f", App (App (Var "f", erase a), False))
  (* match s with inl y -> e1 | inr z -> e2  =
       if (snd s) then (\y. e1) (fst s) else (\z. e2) (fst s) *)
  | SMatch (s, y, e1, z, e2) ->
      let s' = erase s in
      let payload = App (s', Lam ("a", Lam ("b", Var "a"))) in
      (* fst s *)
      let tag = App (s', Lam ("a", Lam ("b", Var "b"))) in
      (* snd s *)
      Ifthenelse
        (tag, App (Lam (y, erase e1), payload), App (Lam (z, erase e2), payload))
  (* [] = \f. f () false
     h :: t = \f. f (pair h t) true *)
  | SNil -> Lam ("f", App (App (Var "f", Unit), False))
  | SCons (h, t) ->
      let ht = Lam ("g", App (App (Var "g", erase h), erase t)) in
      (* pair h t *)
      Lam ("f", App (App (Var "f", ht), True))
  (* match l with [] -> e1 | h::t -> e2  =
       if (snd l) then (\h.\t. e2) (fst (fst l)) (snd (fst l)) else e1 *)
  | SListMatch (l, e1, h, t, e2) ->
      let l' = erase l in
      let sel_fst = Lam ("a", Lam ("b", Var "a")) in
      let sel_snd = Lam ("a", Lam ("b", Var "b")) in
      let cell = App (l', sel_fst) in
      (* the (head,tail) pair, if cons *)
      let tag = App (l', sel_snd) in
      (* is-cons boolean *)
      let hd = App (cell, sel_fst) in
      let tl = App (cell, sel_snd) in
      Ifthenelse (tag, App (App (Lam (h, Lam (t, erase e2)), hd), tl), erase e1)

(** Typecheck an [sterm] in context [gamma]

    Kind constraints are solved first, and the resulting kind substitution is
    pushed into the kind annotations of [s] and [c] before type unification
    runs, so that [types_eq]'s structural kind comparison on [TForall]/[TLam]
    always sees fully-resolved kinds *)
let typecheck (g : typctx) (t : sterm) : (typed_term, string) result =
  let* s, c, kc = get_constraints g t in
  let* ksigma = Kinds.unify kc in
  let s' = kind_subst_typ ksigma s in
  let c' =
    List.map
      (fun (a, b) -> (kind_subst_typ ksigma a, kind_subst_typ ksigma b))
      c
  in
  let* sigma = unify g c' in
  return (erase t, beta_reduce_typ_display (type_subst sigma s'))

(** Typecheck a top-level [sphrase] under [gamma], producing its type-erased
    [phrase], its [typ], and the context under which subsequent phrases should
    be typechecked. *)
let typecheck_phrase (gamma : typctx) (p : sphrase) :
    (typctx * phrase option * typ, string) result =
  match p with
  | SPTerm t ->
      let* t', ty = typecheck gamma t in
      return (gamma, Some (PTerm t'), ty)
  | SPDef (x, Some ty, e) ->
      let* kc = type_wf gamma ty in
      let* _ = Kinds.unify kc in
      let* e', inferred = typecheck gamma e in
      let* _ = unify gamma [ (ty, inferred) ] in
      return (update_term gamma x ty, Some (PDef (x, e')), ty)
  | SPDef (x, None, e) ->
      let* e', ty = typecheck gamma e in
      return (update_term gamma x ty, Some (PDef (x, e')), ty)
  | SPTypedef (x, t) ->
      let* _k, kc = Kinds.get_kind_constraints gamma t in
      let* ksigma = Kinds.unify kc in
      return (update_alias gamma x (kind_subst_typ ksigma t), None, t)
