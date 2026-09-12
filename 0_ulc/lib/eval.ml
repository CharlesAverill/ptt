(** Interpreter for the untyped lambda calculus *)

open Syntax
open Monads

(** Define {b values}, which cannot reduce any further *)
let is_value (t : term) : bool = match t with Lam _ -> true | _ -> false

(** Perform one small step of CBV evaluation *)
let rec step (t : term) : (term, string) result =
  match t with
  (* Values *)
  | Var _ | Lam _ -> fail ""
  (* Beta reduction when [arg] is a value *)
  | App (Lam (x, body), arg) when is_value arg -> return (cas body x arg)
  (* Reduce RHS if LHS is a value *)
  | App (v1, t2) when is_value v1 ->
      let* t2' = step t2 in
      Ok (App (v1, t2'))
  (* Reduce LHS *)
  | App (t1, t2) ->
      let* t1' = step t1 in
      Ok (App (t1', t2))

(** Evaluate a term until it cannot be reduced further *)
let rec eval (t : term) : term =
  match step t with Ok t' -> eval t' | Error _ -> t
