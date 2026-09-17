(** Syntax definitions for the simply-typed lambda calculus *)

(** Types of [term]s *)
type typ =
  (* Primitives *)
  | TUnit
  | TBool
  | TNat
  (* Type variables *)
  | TVar of string
  (* Unification variables *)
  | TMetaVar of int
  (* Functions *)
  | TArrow of (typ * typ)
  (* Type abstractions *)
  | TForall of (string * typ)
  (* Pairs *)
  | TProd of (typ * typ)
  (* Variants *)
  | TSum of (typ * typ)
  (* Lists *)
  | TList of typ

let letter i =
  if i < 26 then String.make 1 (Char.chr (Char.code 'a' + i))
  else Printf.sprintf "t%d" i

(** Convert a [typ] to a printable [string] *)
let rec string_of_typ (t : typ) : string =
  match t with
  | TUnit -> "unit"
  | TBool -> "bool"
  | TNat -> "nat"
  | TArrow (t1, t2) ->
      Printf.sprintf "%s -> %s" (string_of_typ t1) (string_of_typ t2)
  | TVar s -> s
  | TMetaVar x -> Printf.sprintf "?%s" (letter x)
  | TForall (s, t) -> Printf.sprintf "forall %s.(%s)" s (string_of_typ t)
  | TProd (x, y) -> Printf.sprintf "%s * %s" (string_of_typ x) (string_of_typ y)
  | TSum (x, y) -> Printf.sprintf "%s + %s" (string_of_typ x) (string_of_typ y)
  | TList x -> Printf.sprintf "%s list" (string_of_typ x)

(** Concrete syntax tree *)
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
  (* \v[:T].x *)
  | SLam of string * typ option * sterm
  (* x1 x2 *)
  | SApp of sterm * sterm
  (* e : T *)
  | SAnn of sterm * typ
  (* /\'a.e *)
  | STLam of (string * sterm)
  (* e1 [t] *)
  | SPolyApp of (sterm * typ)
  (* let v [: t] = e1 in e2 *)
  | SLet of (string * typ option * sterm * sterm)
  (* (x, y) *)
  | SPair of (sterm * sterm)
  (* fst (x, y) *)
  | SFst of sterm
  (* snd (x, y) *)
  | SSnd of sterm
  (* inl x *)
  | SInl of sterm
  (* inr x *)
  | SInr of sterm
  (* match x with inl y -> e1 | inr z -> e2 *)
  | SMatch of (sterm * string * sterm * string * sterm)
  (* [] *)
  | SNil
  (* h :: t *)
  | SCons of (sterm * sterm)
  (* match l with [] -> e1 | h :: t -> e2 *)
  | SListMatch of (sterm * sterm * string * string * sterm)

(** Convert a [sterm] to a printable [string] *)
let rec string_of_sterm (t : sterm) : string =
  match t with
  | SVar v -> v
  | SUnit -> "()"
  | STrue -> "true"
  | SFalse -> "false"
  | SIfthenelse (x, y, z) ->
      Printf.sprintf "if %s then %s else %s" (string_of_sterm x)
        (string_of_sterm y) (string_of_sterm z)
  | SNat n -> string_of_int n
  | SIseq (n, m) ->
      Printf.sprintf "%s == %s" (string_of_sterm n) (string_of_sterm m)
  | SLam (v, ty, x) ->
      Printf.sprintf "\\%s%s.(%s)" v
        (match ty with None -> "" | Some t -> ":" ^ string_of_typ t)
        (string_of_sterm x)
  | SApp (x1, x2) ->
      Printf.sprintf "%s %s" (string_of_sterm x1) (string_of_sterm x2)
  | SAnn (e, t) ->
      Printf.sprintf "(%s : %s)" (string_of_sterm e) (string_of_typ t)
  | STLam (s, t) -> Printf.sprintf "/\\%s.(%s)" s (string_of_sterm t)
  | SPolyApp (e, t) ->
      Printf.sprintf "%s [%s]" (string_of_sterm e) (string_of_typ t)
  | SLet (v, Some t, e1, e2) ->
      Printf.sprintf "let %s : %s = %s in %s" v (string_of_typ t)
        (string_of_sterm e1) (string_of_sterm e2)
  | SLet (v, None, e1, e2) ->
      Printf.sprintf "let %s = %s in %s" v (string_of_sterm e1)
        (string_of_sterm e2)
  | SPair (x, y) ->
      Printf.sprintf "(%s, %s)" (string_of_sterm x) (string_of_sterm y)
  | SFst x -> Printf.sprintf "fst %s" (string_of_sterm x)
  | SSnd x -> Printf.sprintf "snd %s" (string_of_sterm x)
  | SInl x -> Printf.sprintf "inl %s" (string_of_sterm x)
  | SInr x -> Printf.sprintf "inr %s" (string_of_sterm x)
  | SMatch (t, x, e1, y, e2) ->
      Printf.sprintf "match %s with inl %s => %s | inr %s => %s end"
        (string_of_sterm t) x (string_of_sterm e1) y (string_of_sterm e2)
  | SNil -> "[]"
  | SCons (h, t) ->
      Printf.sprintf "%s :: %s" (string_of_sterm h) (string_of_sterm t)
  | SListMatch (l, e1, h, t, e2) ->
      Printf.sprintf "match %s with [] => %s | %s :: %s => %s end"
        (string_of_sterm l) (string_of_sterm e1) h t (string_of_sterm e2)

(** Top-level concrete syntax trees *)
type sphrase =
  | SPTerm of sterm
  (* def x [: T] = e *)
  | SPDef of string * typ option * sterm

(** Printable string form of [sphrase] *)
let string_of_sphrase (s : sphrase) : string =
  match s with
  | SPTerm t -> string_of_sterm t
  | SPDef (x, ty, e) ->
      Printf.sprintf "def %s%s = %s" x
        (match ty with None -> "" | Some t -> " : " ^ string_of_typ t)
        (string_of_sterm e)

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
  | Ifthenelse of term * term * term
  (* nat *)
  | Nat of int
  (* == *)
  | Iseq of term * term
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
      Printf.sprintf "if %s then %s else %s" (string_of_term x)
        (string_of_term y) (string_of_term z)
  | Iseq (n, m) ->
      Printf.sprintf "%s == %s" (string_of_term n) (string_of_term m)
  | Nat n -> string_of_int n
  | Lam (v, x) -> Printf.sprintf "\\%s.(%s)" v (string_of_term x)
  | App (x1, x2) ->
      Printf.sprintf "%s %s" (string_of_term x1) (string_of_term x2)

(** Top-level type-free syntax trees *)
type phrase = PTerm of term | PDef of string * term

(** Printable string form of [phrase] *)
let string_of_phrase (p : phrase) : string =
  match p with
  | PTerm t -> string_of_term t
  | PDef (x, e) -> Printf.sprintf "def %s = %s" x (string_of_term e)

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
  | App (x1, x2) -> App (cas x1 s t', cas x2 s t')
  | Iseq (x1, x2) -> Iseq (cas x1 s t', cas x2 s t')

(** Determine the free variables of a [typ] *)
let rec tfree (t : typ) : string list =
  match t with
  | TVar x -> [ x ]
  | TMetaVar _ -> []
  | TUnit | TBool | TNat -> []
  | TForall (v, x) -> List.filter (fun v' -> v <> v') (tfree x)
  | TArrow (t1, t2) | TProd (t1, t2) | TSum (t1, t2) -> tfree t1 @ tfree t2
  | TList t' -> tfree t'

(** Type-level capture avoiding substitution *)
let rec tcas (t : typ) (s : string) (t' : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TMetaVar _ -> t
  | TVar v -> if v <> s then t else t'
  | TArrow (t1, t2) -> TArrow (tcas t1 s t', tcas t2 s t')
  | TProd (t1, t2) -> TProd (tcas t1 s t', tcas t2 s t')
  | TSum (t1, t2) -> TSum (tcas t1 s t', tcas t2 s t')
  | TList t'' -> TList (tcas t'' s t')
  | TForall (v, x) ->
      if v = s then t
      else if not (List.mem v (tfree t')) then TForall (v, tcas x s t')
      else
        let v' = fresh v ((s :: tfree t') @ tfree x) in
        TForall (v', tcas (tcas x v (TVar v')) s t')
