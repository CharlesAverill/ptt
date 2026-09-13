(** Syntax definitions for the simply-typed lambda calculus *)

(** Types of [term]s *)
type typ = TUnit | TBool | TNat | TArrow of (typ * typ)

(** Convert a [typ] to a printable [string] *)
let rec string_of_typ (t : typ) : string =
  match t with
  | TUnit -> "unit"
  | TBool -> "bool"
  | TNat -> "nat"
  | TArrow (t1, t2) -> string_of_typ t1 ^ " -> " ^ string_of_typ t2

(** Concrete syntax tree

    Abstractions can optionally carry type annotations. Currently, the parser
    enforces that they must carry annotations, but later we will want to
    implement inference so that annotations are not mandatory. *)
type sterm =
  (* v *)
  | SVar of string
  (* () *)
  | SUnit
  (* true *)
  | STrue
  (* false *)
  | SFalse
  (* if then else *)
  | SIfthenelse of (sterm * sterm * sterm)
  (* nat *)
  | SNat of int
  (* x == y *)
  | SIseq of sterm * sterm
  (* \v:T.x *)
  | SLam of string * (typ option) * sterm
  (* x1 x2 *)
  | SApp of sterm * sterm
  (* e : T *)
  | SAnn of sterm * typ

(** Convert a [sterm] to a printable [string] *)
let rec string_of_sterm (t : sterm) : string =
  match t with
  | SVar v -> v
  | SUnit -> "()"
  | STrue -> "true"
  | SFalse -> "false"
  | SIfthenelse (x, y, z) ->
      "if " ^ string_of_sterm x ^ " then " ^ string_of_sterm y ^ " else "
      ^ string_of_sterm z
  | SNat n -> string_of_int n
  | SIseq (n, m) -> string_of_sterm n ^ " == " ^ string_of_sterm m
  | SLam (v, ty, x) ->
      let ty_str =
        match ty with None -> "" | Some t -> ":" ^ string_of_typ t
      in
      "\\" ^ v ^ ty_str ^ ".(" ^ string_of_sterm x ^ ")"
  | SApp (x1, x2) -> string_of_sterm x1 ^ " " ^ string_of_sterm x2
  | SAnn (e, t) -> "(" ^ string_of_sterm e ^ " : " ^ string_of_typ t ^ ")"

(** Syntax tree after type erasure *)
type term =
  (* v *)
  | Var of string
  (* () *)
  | Unit
  (* true *)
  | True
  (* false *)
  | False
  (* if then else *)
  | Ifthenelse of (term * term * term)
  (* nat *)
  | Nat of int
  (* == *)
  | Iseq of (term * term)
  (* \v. x *)
  | Lam of string * term
  (* x1 x2 *)
  | App of term * term

type typed_term = term * typ
(** A [term] paired with its [typ] *)

(** Convert a [term] to a printable [string] *)
let rec string_of_term (t : term) : string =
  match t with
  | Var v -> v
  | Unit -> "()"
  | True -> "true"
  | False -> "false"
  | Ifthenelse (x, y, z) ->
      "if " ^ string_of_term x ^ " then " ^ string_of_term y ^ " else "
      ^ string_of_term z
  | Iseq (n, m) -> string_of_term n ^ " == " ^ string_of_term m
  | Nat n -> string_of_int n
  | Lam (v, x) -> "\\" ^ v ^ ".(" ^ string_of_term x ^ ")"
  | App (x1, x2) -> string_of_term x1 ^ " " ^ string_of_term x2

(** Determine the free variables of a [term] *)
let rec free (t : term) : string list =
  match t with
  | Var x -> [ x ]
  | Unit | True | False | Nat _ -> []
  | Lam (v, x) -> List.filter (fun v' -> v <> v') (free x)
  | Ifthenelse (x1, x2, x3) -> free x1 @ free x2 @ free x3
  | App (x1, x2) | Iseq (x1, x2) -> free x1 @ free x2

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
  | Unit | True | False | Nat _ -> t
  | Lam (v, x) ->
      (* Binder shadows the variable to replace, so no free [s] can occur in [x] *)
      if v = s then t
        (* [v] is not free in [t'], so we can naively continue substituting in the body *)
      else if not (List.mem v (free t')) then Lam (v, cas x s t')
      (* [v] is free in [t'], so we have to rename the binder and its ocurrences in [x] *)
        else
        let v' = fresh v ((s :: free t') @ free x) in
        Lam (v', cas (cas x v (Var v')) s t')
  | Ifthenelse (x1, x2, x3) -> Ifthenelse (cas x1 s t', cas x2 s t', cas x3 s t')
  | App (x1, x2) | Iseq (x1, x2) -> App (cas x1 s t', cas x2 s t')
