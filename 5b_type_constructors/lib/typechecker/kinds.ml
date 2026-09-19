(** Kindchecking *)

open Syntax
open Monads
open Defs

(** Generate a fresh kind metavariable *)
let fresh_kmetavar (st : state) : kind * state =
  let n, st = fresh_id st in
  (KMetaVar n, st)

(** The kind of a type-level binder *)
let binder_kind (st : state) (k : kind option) : kind * state =
  match k with Some k -> (k, st) | None -> fresh_kmetavar st

(** Apply a kind substitution to a kind *)
let rec kzonk (s : kind subst) (k : kind) : kind =
  match k with
  | KProper -> KProper
  | KOperator (k1, k2) -> KOperator (kzonk s k1, kzonk s k2)
  | KMetaVar x -> (
      match lookup_subst s x with Some k' -> kzonk s k' | None -> k)

(** Whether a kind metavariable [x] occurs in a kind [k] *)
let rec occurs (x : int) (k : kind) : bool =
  match k with
  | KMetaVar x' -> x = x'
  | KOperator (k1, k2) -> occurs x k1 || occurs x k2
  | KProper -> false

(** Unify two kinds, extending the kind substitution of [st] *)
let rec kunify (st : state) (k1 : kind) (k2 : kind) : (state, string) result =
  match (kzonk st.ksubst k1, kzonk st.ksubst k2) with
  | KProper, KProper -> return st
  | KMetaVar x, KMetaVar y when x = y -> return st
  | KMetaVar x, k | k, KMetaVar x ->
      if occurs x k then
        fail
          (Printf.sprintf "Infinite kind: %s occurs in %s"
             (string_of_kind (KMetaVar x))
             (string_of_kind k))
      else return { st with ksubst = (x, k) :: st.ksubst }
  | KOperator (a1, b1), KOperator (a2, b2) ->
      let* st = kunify st a1 a2 in
      kunify st b1 b2
  | k1, k2 ->
      fail
        (Printf.sprintf "Kind unification failure, %s <> %s" (string_of_kind k1)
           (string_of_kind k2))

(** Apply a kind substitution to a kind, defaulting every metavariable that is
    still unsolved to [*] *)
let rec kdefault (s : kind subst) (k : kind) : kind =
  match kzonk s k with
  | KMetaVar _ -> KProper
  | KOperator (k1, k2) -> KOperator (kdefault s k1, kdefault s k2)
  | KProper -> KProper

(** Map [f] over kind annotations in [t] *)
let rec map_kinds (f : kind -> kind) (t : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TVar _ | TMetaVar _ -> t
  | TArrow (t1, t2) -> TArrow (map_kinds f t1, map_kinds f t2)
  | TApp (t1, t2) -> TApp (map_kinds f t1, map_kinds f t2)
  | TForall (v, k, t') -> TForall (v, Option.map f k, map_kinds f t')
  | TLam (v, k, t') -> TLam (v, Option.map f k, map_kinds f t')

(** Choose the internal name for a new type variable binder written as [v] *)
let fresh_tyvar_name ?(avoid = []) (g : typctx) (v : string) : string =
  let taken =
    avoid @ List.map (fun (_, (v', _)) -> v') g.tyvars @ List.map fst g.aliases
  in
  fresh v taken

(** Kind-check a type [t] written by the user, under [g] *)
let rec check_type (st : state) (g : typctx) (t : typ) :
    (typ * kind * state, string) result =
  match t with
  (* K-Prim *)
  | TUnit | TBool | TNat -> return (t, KProper, st)
  (* Metavariables only ever stand in for the types of terms *)
  | TMetaVar _ -> return (t, KProper, st)
  (* K-Var *)
  | TVar v -> (
      match lookup_tyvar g v with
      | Some (v', k) -> return (TVar v', k, st)
      | None -> (
          match lookup_alias g v with
          | Some (_, k) -> return (t, k, st)
          | None -> fail (Printf.sprintf "Unbound type variable %s" v)))
  (* K-Arrow *)
  | TArrow (t1, t2) ->
      let* t1', k1, st = check_type st g t1 in
      let* st = kunify st k1 KProper in
      let* t2', k2, st = check_type st g t2 in
      let* st = kunify st k2 KProper in
      return (TArrow (t1', t2'), KProper, st)
  (* K-App *)
  | TApp (t1, t2) ->
      let* t1', k1, st = check_type st g t1 in
      let* t2', k2, st = check_type st g t2 in
      let k3, st = fresh_kmetavar st in
      let* st = kunify st k1 (KOperator (k2, k3)) in
      return (TApp (t1', t2'), k3, st)
  (* K-All *)
  | TForall (v, k, body) ->
      let k, st = binder_kind st k in
      let v' = fresh_tyvar_name g v in
      let* body', kb, st = check_type st (update_tyvar g v v' k) body in
      let* st = kunify st kb KProper in
      return (TForall (v', Some k, body'), KProper, st)
  (* K-Abs *)
  | TLam (v, k, body) ->
      let k, st = binder_kind st k in
      let v' = fresh_tyvar_name g v in
      let* body', kb, st = check_type st (update_tyvar g v v' k) body in
      return (TLam (v', Some k, body'), KOperator (k, kb), st)

(** Kind-check a type [t] written by the user that must classify terms, i.e.
    must have kind [*] *)
let check_proper_type (st : state) (g : typctx) (t : typ) :
    (typ * state, string) result =
  let* t', k, st = check_type st g t in
  match kunify st k KProper with
  | Ok st -> return (t', st)
  | Error _ ->
      fail
        (Printf.sprintf
           "%s has kind %s, but only types of kind * can classify terms"
           (string_of_typ t)
           (string_of_kind (kzonk st.ksubst k)))
