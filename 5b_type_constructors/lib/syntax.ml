(** Syntax definitions for the System F omega *)

open Utils

(** Kinds of [typ]s *)
type kind =
  (* * *)
  | KProper
  (* * => * *)
  | KOperator of (kind * kind)
  (* Unification variables *)
  | KMetaVar of int

let letter i =
  if i < 26 then String.make 1 (Char.chr (Char.code 'a' + i))
  else Printf.sprintf "t%d" i

let rec string_of_kind (k : kind) : string =
  match k with
  | KProper -> "*"
  | KOperator (k1, k2) ->
      Printf.sprintf "%s => %s" (paren (string_of_kind k1)) (string_of_kind k2)
  | KMetaVar x -> Printf.sprintf "?k%d" x

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
  (* Polymorphic types *)
  | TForall of (string * kind option * typ)
  (* Type abstractions *)
  | TLam of (string * kind option * typ)
  (* Applications of type abstractions *)
  | TApp of (typ * typ)

let string_of_binder (v : string) (k : kind option) : string =
  match k with None -> v | Some k -> v ^ ":" ^ string_of_kind k

(** Convert a [typ] to a printable [string] *)
let rec string_of_typ (t : typ) : string =
  match t with
  | TUnit -> "unit"
  | TBool -> "bool"
  | TNat -> "nat"
  | TArrow (t1, t2) ->
      Printf.sprintf "%s -> %s" (paren (string_of_typ t1)) (string_of_typ t2)
  | TVar s -> s
  | TMetaVar x -> Printf.sprintf "?%s" (letter x)
  | TForall (v, k, t') ->
      Printf.sprintf "forall %s. %s" (string_of_binder v k) (string_of_typ t')
  | TLam (v, k, t') ->
      Printf.sprintf "\\%s. %s" (string_of_binder v k) (string_of_typ t')
  | TApp (t1, t2) ->
      Printf.sprintf "%s %s"
        (paren (string_of_typ t1))
        (paren (string_of_typ t2))

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

(** Convert a [sterm] to a printable [string] *)
let rec string_of_sterm (t : sterm) : string =
  match t with
  | SVar v -> v
  | SUnit -> "()"
  | STrue -> "true"
  | SFalse -> "false"
  | SNat n -> string_of_int n
  | SIfthenelse (x, y, z) ->
      Printf.sprintf "if %s then %s else %s" (string_of_sterm x)
        (string_of_sterm y) (string_of_sterm z)
  | SIseq (n, m) ->
      Printf.sprintf "%s == %s"
        (paren (string_of_sterm n))
        (paren (string_of_sterm m))
  | SLam (v, None, x) -> Printf.sprintf "\\%s. %s" v (string_of_sterm x)
  | SLam (v, Some ty, x) ->
      Printf.sprintf "\\%s:%s. %s" v (string_of_typ ty) (string_of_sterm x)
  | SApp (x1, x2) ->
      Printf.sprintf "%s %s"
        (paren (string_of_sterm x1))
        (paren (string_of_sterm x2))
  | SAnn (e, ty) ->
      Printf.sprintf "(%s : %s)" (string_of_sterm e) (string_of_typ ty)
  | STLam (v, x) -> Printf.sprintf "/\\%s. %s" v (string_of_sterm x)
  | SPolyApp (e, ty) ->
      Printf.sprintf "%s [%s]" (paren (string_of_sterm e)) (string_of_typ ty)
  | SLet (v, None, e1, e2) ->
      Printf.sprintf "let %s = %s in %s" v (string_of_sterm e1)
        (string_of_sterm e2)
  | SLet (v, Some ty, e1, e2) ->
      Printf.sprintf "let %s : %s = %s in %s" v (string_of_typ ty)
        (string_of_sterm e1) (string_of_sterm e2)

(** Top-level concrete syntax trees *)
type sphrase =
  | SPTerm of sterm
  (* def x [: T] = e *)
  | SPDef of string * typ option * sterm
  (* type x = t *)
  | SPTypedef of string * typ

(** Printable string form of [sphrase] *)
let string_of_sphrase (s : sphrase) : string =
  match s with
  | SPTerm t -> string_of_sterm t
  | SPDef (x, ty, e) ->
      Printf.sprintf "def %s%s = %s" x
        (match ty with None -> "" | Some t -> " : " ^ string_of_typ t)
        (string_of_sterm e)
  | SPTypedef (x, t) -> Printf.sprintf "type %s = %s" x (string_of_typ t)

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
  | Nat n -> string_of_int n
  | Ifthenelse (x, y, z) ->
      Printf.sprintf "if %s then %s else %s" (string_of_term x)
        (string_of_term y) (string_of_term z)
  | Iseq (n, m) ->
      Printf.sprintf "%s == %s"
        (paren (string_of_term n))
        (paren (string_of_term m))
  | Lam (v, x) -> Printf.sprintf "\\%s. %s" v (string_of_term x)
  | App (x1, x2) ->
      Printf.sprintf "%s %s"
        (paren (string_of_term x1))
        (paren (string_of_term x2))

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
  | TForall (v, k, x) -> List.filter (fun v' -> v <> v') (tfree x)
  | TLam (v, k, x) -> List.filter (fun v' -> v <> v') (tfree x)
  | TArrow (t1, t2) | TApp (t1, t2) -> tfree t1 @ tfree t2

(** Type-level capture avoiding substitution *)
let rec tcas (t : typ) (s : string) (t' : typ) : typ =
  match t with
  | TUnit | TBool | TNat | TMetaVar _ -> t
  | TVar v -> if v <> s then t else t'
  | TArrow (t1, t2) -> TArrow (tcas t1 s t', tcas t2 s t')
  | TForall (v, k, x) ->
      if v = s then t
      else if not (List.mem v (tfree t')) then TForall (v, k, tcas x s t')
      else
        let v' = fresh v ((s :: tfree t') @ tfree x) in
        TForall (v', k, tcas (tcas x v (TVar v')) s t')
  | TLam (v, k, x) ->
      if v = s then t
      else if not (List.mem v (tfree t')) then TLam (v, k, tcas x s t')
      else
        let v' = fresh v ((s :: tfree t') @ tfree x) in
        TLam (v', k, tcas (tcas x v (TVar v')) s t')
  | TApp (t1, t2) -> TApp (tcas t1 s t', tcas t2 s t')
