(** Typechecking and type erasure for STLC *)

open Syntax
open Monads

exception TypeError of string

type typctx = string -> typ option
(** Mapping from variables to their types *)

(** Functional update *)
let update f x y = fun x' -> if x = x' then y else f x'

(** Compute the type of a [sterm] under context [gamma], producing both its
    [typ] and its type-erased [term] on success. *)
let rec typeof (gamma : typctx) (t : sterm) : (typed_term, string) result =
  match t with
  (* |- () : unit *)
  | SUnit -> return (Unit, TUnit)
  (* |- true,false : bool *)
  | STrue -> return (True, TBool)
  | SFalse -> return (False, TBool)
  (* G |- b : bool => G |- c1, c2 : T => |- if b then c1 else c2 : T *)
  | SIfthenelse (b, c1, c2) ->
      let* b', btyp = typeof gamma b in
      if btyp = TBool then
        let* c1', c1typ = typeof gamma c1 in
        let* c2', c2typ = typeof gamma c2 in
        if c1typ = c2typ then return (Ifthenelse (b', c1', c2'), c1typ)
        else
          fail
            (Printf.sprintf "Expected type %s but got %s" (string_of_typ c1typ)
               (string_of_typ c2typ))
      else fail (Printf.sprintf "Branch parameters must be of type bool")
  (* |- n : nat *)
  | SNat n -> return (Nat n, TNat)
  (* |- n, m : nat => |- n == m : bool *)
  | SIseq (x, y) ->
      let* x', xtyp = typeof gamma x in
      let* y', ytyp = typeof gamma y in
      if xtyp = TNat && ytyp = TNat then return (Iseq (x', y'), TBool)
      else
        fail
          (Printf.sprintf "Expected nats but got %s,%s" (string_of_typ xtyp)
             (string_of_typ ytyp))
  (* G |- v : G v *)
  | SVar v -> (
      match gamma v with
      | Some ty -> return (Var v, ty)
      | None -> fail (Printf.sprintf "unbound variable %s" v))
  (* G[v := t1] |- body : T1 => G |- \v:T2.body : T2 -> T1 *)
  | SLam (v, Some t1, body) ->
      let* body', t2 = typeof (update gamma v (Some t1)) body in
      return (Lam (v, body'), TArrow (t1, t2))
  (* G |- E1 : (T2 -> T1) => G |- E2 : T2 => G |- e1 e2 : T1 *)
  | SApp (e1, e2) -> (
      let* e1', t1 = typeof gamma e1 in
      let* e2', t2 = typeof gamma e2 in
      match t1 with
      | TArrow (targ, tres) when targ = t2 -> return (App (e1', e2'), tres)
      | TArrow (targ, _) ->
          fail
            (Printf.sprintf "expected argument of type %s but got %s"
               (string_of_typ targ) (string_of_typ t2))
      | _ ->
          fail
            (Printf.sprintf "cannot apply non-function of type %s"
               (string_of_typ t1)))
  | _ ->
      fail
        (Printf.sprintf "Type checking failed for term %s" (string_of_sterm t))

(** Typecheck a closed [sterm] and produce a type-erased [term] and its [typ] *)
let typecheck (t : sterm) : (typed_term, string) result =
  typeof (fun _ -> None) t

(** Typecheck and erase a closed [sterm], raising [TypeError] if it is ill-typed
*)
let erase (t : sterm) : term =
  match typecheck t with Ok (t', _) -> t' | Error e -> raise (TypeError e)
