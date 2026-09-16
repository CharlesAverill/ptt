(** Unification-based typechecking and type erasure for System F *)

open Syntax
open Monads

exception TypeError of string
(** Type errors *)

type typctx = {
  terms : (string * typ) list;  (** Mapping from variables to their types *)
  tyvars : string list;  (** Set of bound type variables *)
}
(** Type context *)

(** The empty type context *)
let empty_typctx = { terms = []; tyvars = [] }

let update_term (g : typctx) x t = { g with terms = (x, t) :: g.terms }
let lookup_term (g : typctx) x = List.assoc_opt x g.terms

let remove_first (l : 'a list) (x : 'a) : 'a list =
  List.rev
    (snd
       (List.fold_left
          (fun (seen, l') i ->
            if seen then (true, i :: l')
            else if i = x then (true, l')
            else (false, i :: l'))
          (false, []) l))

let update_tyvar (f : typctx) x y =
  {
    terms = f.terms;
    tyvars = (if y then x :: f.tyvars else remove_first f.tyvars x);
  }

let rec types_eq (t1 : typ) (t2 : typ) : bool =
  match (t1, t2) with
  | TVar x, TVar y when x = y -> true
  | TUnit, TUnit | TBool, TBool | TNat, TNat -> true
  | TArrow (t1, t2), TArrow (t3, t4) -> types_eq t1 t3 && types_eq t2 t4
  | TForall (a, x), TForall (b, y) when a = b -> types_eq x y
  | TForall (a, x), TForall (b, y) ->
      let gamma = fresh "gamma" (tfree x @ tfree y) in
      types_eq (tcas x a (TVar gamma)) (tcas y b (TVar gamma))
  | _, _ -> false

let rec type_wf (gamma : typctx) (t : typ) : bool =
  match t with
  | TUnit | TBool | TNat | TMetaVar _ -> true
  | TVar v -> List.mem v gamma.tyvars
  | TArrow (t1, t2) -> type_wf gamma t1 && type_wf gamma t2
  | TForall (alpha, t') -> type_wf (update_tyvar gamma alpha true) t'

type subst = (int * typ) list
(** Type substitutions *)

(** Domain of a type substitution *)
let dom (s : subst) = List.map fst s

(** Range of a type substitution *)
let range (s : subst) = List.map snd s

(** Get the mapping of a type variable *)
let lookup_subst (s : subst) (x : int) : typ option = List.assoc_opt x s

(** Perform the type substitution s(t) *)
let rec type_subst (s : subst) (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TVar _ -> t
  | TArrow (t1, t2) -> TArrow (type_subst s t1, type_subst s t2)
  | TForall (x, t') -> TForall (x, type_subst s t')
  | TMetaVar x -> (
      match lookup_subst s x with Some t -> t | None -> TMetaVar x)

(** Perform a type substitution on a context *)
let ctx_type_subst (s : subst) (t : typctx) : typctx =
  {
    terms = List.map (fun (id, ty) -> (id, type_subst s ty)) t.terms;
    tyvars = t.tyvars;
  }

(** Perform a type substitution on an sterm *)
let rec sterm_type_subst (s : subst) (t : sterm) : sterm =
  match t with
  | SUnit | STrue | SFalse | SNat _ | SVar _ -> t
  | SIfthenelse (b, c1, c2) ->
      SIfthenelse
        (sterm_type_subst s b, sterm_type_subst s c1, sterm_type_subst s c2)
  | SIseq (x1, x2) -> SIseq (sterm_type_subst s x1, sterm_type_subst s x2)
  | SLam (x, None, e) -> SLam (x, None, sterm_type_subst s e)
  | SLam (x, Some ty, e) ->
      SLam (x, Some (type_subst s ty), sterm_type_subst s e)
  | SLet (x, Some t, e1, e2) ->
      SLet
        (x, Some (type_subst s t), sterm_type_subst s e1, sterm_type_subst s e2)
  | SLet (x, None, e1, e2) ->
      SLet (x, None, sterm_type_subst s e1, sterm_type_subst s e2)
  | SApp (x1, x2) -> SApp (sterm_type_subst s x1, sterm_type_subst s x2)
  | SAnn (e, ty) -> SAnn (sterm_type_subst s e, type_subst s ty)
  | STLam (x, e) -> STLam (x, sterm_type_subst s e)
  | SPolyApp (e1, ty) -> SPolyApp (sterm_type_subst s e1, type_subst s ty)

(** Composition of type substitutions *)
let compose (s : subst) (g : subst) : subst =
  List.map (fun (x, gt) -> (x, type_subst s gt)) g
  @ List.filter (fun (x, _) -> not (List.mem x (dom g))) s

type constr = typ * typ
(** Typing constraints *)

type constr_set = constr list
(** Sets of typing constraints *)

(** Whether a substitution unifies a constraint *)
let subst_unifies (s : subst) ((c1, c2) : constr) : bool =
  types_eq (type_subst s c1) (type_subst s c2)

(** Whether a substitution unifies all constraints *)
let subst_unifies_set (s : subst) (cs : constr_set) =
  List.fold_left (fun a c -> a && subst_unifies s c) true cs

(** Counter backing [fresh_metavar] *)
let metavar_counter : int ref = ref 0

(** Reset the metavariable counter, e.g. at the start of a new typechecking
    session *)
let reset_metavar_counter () : unit = metavar_counter := 0

(** Generate fresh metavariables

    This function is monotonic and will never return a duplicate metavariable
    within a session *)
let fresh_metavar () : typ =
  let n = !metavar_counter in
  metavar_counter := n + 1;
  TMetaVar n

(** Generate a set of typing constraints and a type [ty] required for an [sterm]
    to have type [ty] under context [g] *)
let rec get_constraints (g : typctx) (t : sterm) :
    (typ * constr_set, string) result =
  match t with
  (* CT-Var: x:T \in G => G |- x : T | {} *)
  | SVar x -> (
      match lookup_term g x with
      | None -> fail (Printf.sprintf "Couldn't determine type of %s" x)
      | Some ty' -> return (ty', []))
  | SUnit -> return (TUnit, [])
  | STrue | SFalse -> return (TBool, [])
  | SNat _ -> return (TNat, [])
  (* CT-Abs: G[x := t1] |- e : t2' | C => G |- \x:t1.t2 : t1' -> t2' | C *)
  | SLam (x, Some t1, e) ->
      if type_wf g t1 then
        let* t2, c = get_constraints (update_term g x t1) e in
        return (TArrow (t1, t2), c)
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ t1))
  | SLam (x, None, e) ->
      let t1 = fresh_metavar () in
      let* t2, c = get_constraints (update_term g x t1) e in
      return (TArrow (t1, t2), c)
  (* CT-If: *)
  | SIfthenelse (b, e1, e2) ->
      let* t1, c1 = get_constraints g b in
      let* t2, c2 = get_constraints g e1 in
      let* t3, c3 = get_constraints g e2 in
      return (t2, c1 @ c2 @ c3 @ [ (t1, TBool); (t2, t3) ])
  | SIseq (x1, x2) ->
      let* t1, c1 = get_constraints g x1 in
      let* t2, c2 = get_constraints g x2 in
      return (TBool, c1 @ c2 @ [ (t1, TNat); (t2, TNat) ])
  (* CT-App: G |- e1 : t1 | c1 => G |- e2 : T2 | C2 => G |- e1 e2 : x | C' *)
  | SApp (e1, e2) ->
      let* t1, c1 = get_constraints g e1 in
      let* t2, c2 = get_constraints g e2 in
      let x = fresh_metavar () in
      return (x, c1 @ c2 @ [ (t1, TArrow (t2, x)) ])
  | SAnn (e, ty) ->
      if type_wf g ty then
        let* t, c = get_constraints g e in
        return (ty, c @ [ (ty, t) ])
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ ty))
  | STLam (x, e) ->
      let* t, c = get_constraints (update_tyvar g x true) e in
      return (TForall (x, t), c)
  | SPolyApp (e, kappa) -> (
      let* t, c = get_constraints g e in
      match t with
      | TForall (alpha, body) ->
          if type_wf g kappa then (* instantiate: body[kappa/alpha] *)
            return (tcas body alpha kappa, c)
          else
            fail
              (Printf.sprintf "type %s is not well-formed" (string_of_typ kappa))
      | _ ->
          fail
            (Printf.sprintf "expected a polymorphic type but got %s"
               (string_of_typ t)))
  | SLet (v, Some t, e1, e2) ->
      if type_wf g t then
        let* t1, c1 = get_constraints g e1 in
        let* t2, c2 = get_constraints (update_term g v t) e2 in
        return (t2, c1 @ c2 @ [ (t, t1) ])
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ t))
  | SLet (v, None, e1, e2) ->
      let* t1, c1 = get_constraints g e1 in
      let* t2, c2 = get_constraints (update_term g v t1) e2 in
      return (t2, c1 @ c2)

(** Whether a metavariable [x] occurs in a type [t] *)
let rec occurs (x : int) (t : typ) : bool =
  match t with
  | TMetaVar x' when x = x' -> true
  | TArrow (t1, t2) -> occurs x t1 || occurs x t2
  | TForall (_, t') -> occurs x t'
  | _ -> false

(** Perform a type substitution in a constraint set *)
let constr_subst (s : subst) (cs : constr_set) : constr_set =
  List.map (fun (a, b) -> (type_subst s a, type_subst s b)) cs

(** Generate a solution to a set of constraints through unification *)
let rec unify (c : constr_set) : (subst, string) result =
  match c with
  | [] -> return []
  | (s, t) :: c' -> (
      if types_eq s t then unify c'
      else
        match (s, t) with
        | TMetaVar x, _ when not (occurs x t) ->
            let* c'' = unify (constr_subst [ (x, t) ] c') in
            return (compose c'' [ (x, t) ])
        | _, TMetaVar x when not (occurs x s) ->
            let* c'' = unify (constr_subst [ (x, s) ] c') in
            return (compose c'' [ (x, s) ])
        | TArrow (s1, s2), TArrow (t1, t2) -> unify (c' @ [ (s1, t1); (s2, t2) ])
        (* s = forall a.A, t = forall b.B

           This case only occurs when s and t are not alpha-equivalent,
           otherwise the types_eq would have returned true *)
        | TForall (a, sb), TForall (b, tb) ->
            let c = fresh "c" (tfree sb @ tfree tb) in
            (* unify ({A[a := c] = B[b := c]} \cup c')*)
            unify ((tcas sb a (TVar c), tcas tb b (TVar c)) :: c')
        | s, t ->
            fail
              (Printf.sprintf "Unification failure, %s <> %s" (string_of_typ s)
                 (string_of_typ t)))

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
  (* pair x y = \x.\y.\f. f x y*)
  | SPair (x, y) -> Lam ("x", Lam ("y", Lam ("f", Ifthenelse (Var "f", erase x, erase y))))
  (* fst x = \x.x true *)
  | SFst x -> Lam ("x", App (Var "x", True))
  (* snd x = \x.x false *)
  | SSnd x -> Lam ("x", App (Var "x", False))
  (* inl x = *)

(** Typecheck an [sterm] in context [gamma] *)
let typecheck (g : typctx) (t : sterm) : (typed_term, string) result =
  let* s, c = get_constraints g t in
  let* sigma = unify c in
  return (erase t, type_subst sigma s)

(** Typecheck a top-level [sphrase] under [gamma], producing its type-erased
    [phrase], its [typ], and the context under which subsequent phrases should
    be typechecked. *)
let typecheck_phrase (gamma : typctx) (p : sphrase) :
    (typctx * phrase * typ, string) result =
  match p with
  | SPTerm t ->
      let* t', ty = typecheck gamma t in
      return (gamma, PTerm t', ty)
  | SPDef (x, Some ty, e) ->
      if type_wf gamma ty then
        let* e', inferred = typecheck gamma e in
        let* _ = unify [ (ty, inferred) ] in
        return (update_term gamma x ty, PDef (x, e'), ty)
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ ty))
  | SPDef (x, None, e) ->
      let* e', ty = typecheck gamma e in
      return (update_term gamma x ty, PDef (x, e'), ty)
