(** Syntax definitions for the untyped lambda calculus *)

(** Syntax tree *)
type term =
  (* v *)
  | Var of string
  (* \v. x *)
  | Lam of string * term
  (* x1 x2 *)
  | App of term * term

(** Convert a term to a printable string *)
let rec string_of_term (t : term) : string =
  match t with
  | Var v -> v
  | Lam (v, x) -> "\\" ^ v ^ ".(" ^ string_of_term x ^ ")"
  | App (x1, x2) -> string_of_term x1 ^ " " ^ string_of_term x2

(** Determine the free variables of a term *)
let rec free (t : term) : string list =
  match t with
  | Var x -> [ x ]
  | Lam (v, x) -> List.filter (fun v' -> v <> v') (free x)
  | App (x1, x2) -> free x1 @ free x2

(** Pick a fresh name not in [avoid] *)
let fresh (base : string) (avoid : string list) : string =
  let rec go i =
    let candidate = base ^ string_of_int i in
    if List.mem candidate avoid then go (i + 1) else candidate
  in
  if List.mem base avoid then go 0 else base

(** Capture-avoiding substitution [t[t'/s]]

    Replace all free instances of [s] in [t] with [t'] *)
let rec cas (t : term) (s : string) (t' : term) : term =
  match t with
  | Var v -> if v <> s then t else t'
  | Lam (v, x) ->
      (* Binder shadows the variable to replace, so no free [s] can occur in [x] *)
      if v = s then t
        (* [v] is not free in [t'], so we can naively continue substituting in the body *)
      else if not (List.mem v (free t')) then Lam (v, cas x s t')
      (* [v] is free in [t'], so we have to rename the binder and its ocurrences in [x] *)
        else
        let v' = fresh v ((s :: free t') @ free x) in
        Lam (v', cas (cas x v (Var v')) s t')
  | App (x1, x2) -> App (cas x1 s t', cas x2 s t')
