(** Kindchecking *)

open Syntax
open Monads
open Defs

module C = Counter (struct
  type v = kind

  let f x = KMetaVar x
end)

(** Generate fresh kind metavariables

    This function is monotonic and will never return a duplicate kind
    metavariable within a session *)
let fresh_kmetavar = C.fresh

(** Reset the kind metavariable counter, e.g. at the start of a new typechecking
    session *)
let reset_kmetavar_counter = C.reset

let rec get_kind_constraints (g : typctx) (t : typ) :
    (kind * kind constr_set, string) result =
  match t with
  | TUnit | TBool | TNat -> return (KProper, [])
  | TVar v -> (
      match lookup_alias g v with
      | None -> (
          match lookup_tyvar g v with
          | None -> fail (Printf.sprintf "Couldn't determine kind of %s" v)
          | Some k -> return (k, []))
      | Some t -> get_kind_constraints g t)
  (* TODO: every [TMetaVar] currently gets kind [KProper] unconditionally,
     which is correct today since one is only ever minted for the type of a
     term (always kind [*]). If a metavariable can ever get solved to a type
     operator (e.g. [?f := list]), it needs its own fresh kind metavariable
     tracked per metavariable id instead *)
  | TMetaVar _ -> return (KProper, [])
  | TArrow (t1, t2) ->
      let* k1, c1 = get_kind_constraints g t1 in
      let* k2, c2 = get_kind_constraints g t2 in
      return (KProper, c1 @ c2 @ [ (k1, KProper); (k2, KProper) ])
  | TLam (v, k1, t) ->
      let* k2, c = get_kind_constraints (update_tyvar g v k1) t in
      return (KOperator (k1, k2), c)
  | TApp (t1, t2) ->
      let* k1, c1 = get_kind_constraints g t1 in
      let* k2, c2 = get_kind_constraints g t2 in
      let k3 = fresh_kmetavar () in
      return (k3, c1 @ c2 @ [ (k1, KOperator (k2, k3)) ])
  | TForall (v, k, t) ->
      let* k', c = get_kind_constraints (update_tyvar g v k) t in
      return (KProper, c @ [ (k', KProper) ])

(** Perform the kind substitution s(t) *)
let rec kind_subst (s : kind subst) (k : kind) : kind =
  match k with
  | KProper -> KProper
  | KOperator (k1, k2) -> KOperator (kind_subst s k1, kind_subst s k2)
  | KMetaVar x -> (
      match lookup_subst s x with Some k -> k | None -> KMetaVar x)

let rec kinds_eq (k1 : kind) (k2 : kind) : bool =
  match (k1, k2) with
  | KProper, KProper -> true
  | KOperator (ka, kb), KOperator (kc, kd) -> kinds_eq ka kc && kinds_eq kb kd
  | KMetaVar x, KMetaVar y -> x = y
  | _, _ -> false

(** Whether a kind metavariable [x] occurs in a kind [k] *)
let rec occurs (x : int) (k : kind) : bool =
  match k with
  | KMetaVar x' when x = x' -> true
  | KOperator (k1, k2) -> occurs x k1 || occurs x k2
  | _ -> false

let compose = compose kind_subst
let constr_subst = constr_subst kind_subst

(** Generate a solution to a set of kind constraints through unification *)
let rec unify (c : kind constr_set) : (kind subst, string) result =
  match c with
  | [] -> return []
  | (s, t) :: c' -> (
      if kinds_eq s t then unify c'
      else
        match (s, t) with
        | KMetaVar x, _ when not (occurs x t) ->
            let* c'' = unify (constr_subst [ (x, t) ] c') in
            return (compose c'' [ (x, t) ])
        | _, KMetaVar x when not (occurs x s) ->
            let* c'' = unify (constr_subst [ (x, s) ] c') in
            return (compose c'' [ (x, s) ])
        | KOperator (s1, s2), KOperator (t1, t2) ->
            unify (c' @ [ (s1, t1); (s2, t2) ])
        | s, t ->
            fail
              (Printf.sprintf "Kind unification failure, %s <> %s"
                 (string_of_kind s) (string_of_kind t)))

(** Apply a kind substitution to the kind annotations embedded in a [typ] *)
let rec kind_subst_typ (s : kind subst) (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TVar _ | TMetaVar _ -> t
  | TArrow (t1, t2) -> TArrow (kind_subst_typ s t1, kind_subst_typ s t2)
  | TApp (t1, t2) -> TApp (kind_subst_typ s t1, kind_subst_typ s t2)
  | TForall (v, k, t') -> TForall (v, kind_subst s k, kind_subst_typ s t')
  | TLam (v, k, t') -> TLam (v, kind_subst s k, kind_subst_typ s t')
