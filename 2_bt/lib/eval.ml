(** Interpreter for the untyped lambda calculus *)

open Syntax
open Monads

(** Define {b values}, which cannot reduce any further *)
let is_value (t : term) : bool =
  match t with Lam _ | Unit | True | False | Nat _ -> true | _ -> false

(** Perform one small step of CBV evaluation *)
let rec step (t : term) : (term, string) result =
  match t with
  (* Values *)
  | Var _ | Unit | True | False | Nat _ | Lam _ -> fail ""
  (* Beta reduction when [arg] is a value *)
  | App (Lam (x, body), arg) when is_value arg -> return (cas body x arg)
  (* Reduce RHS if LHS is a value *)
  | App (v1, t2) when is_value v1 ->
      let* t2' = step t2 in
      return (App (v1, t2'))
  (* Reduce LHS *)
  | App (t1, t2) ->
      let* t1' = step t1 in
      return (App (t1', t2))
  (* Reduce ifthenelse *)
  | Ifthenelse (x1, x2, x3) when is_value x1 ->
      return (if x1 = True then x2 else x3)
  | Ifthenelse (x1, x2, x3) ->
      let* x1' = step x1 in
      return (Ifthenelse (x1', x2, x3))
  (* Reduce iseq *)
  | Iseq (x1, x2) when is_value x1 && is_value x2 ->
      return (if x1 = x2 then True else False)
  | Iseq (x1, x2) when is_value x1 ->
      let* x2' = step x2 in
      return (Iseq (x1, x2'))
  | Iseq (x1, x2) ->
      let* x1' = step x1 in
      return (Iseq (x1', x2))

(** Evaluate a term until it cannot be reduced further *)
let rec eval (t : term) : term =
  match step t with Ok t' -> eval t' | Error _ -> t
