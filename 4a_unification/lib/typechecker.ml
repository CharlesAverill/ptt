(** Bidirectional Typechecking and type erasure for STLC *)

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
  | SApp (x1, x2) -> SApp (sterm_type_subst s x1, sterm_type_subst s x2)
  | SAnn (e, ty) -> SAnn (sterm_type_subst s e, type_subst s ty)
  | STLam (x, e) -> STLam (x, sterm_type_subst s e)
  | SPolyApp (e1, Some ty) ->
      SPolyApp (sterm_type_subst s e1, Some (type_subst s ty))
  | SPolyApp (e1, None) -> SPolyApp (sterm_type_subst s e1, None)

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

(** Generate a set of typing constraints required for an [sterm] to have type
    [ty] under context [g] *)
let rec get_constraints (g : typctx) (t : sterm) (ty : typ) :
    (constr_set, string) result =
  match (t, ty) with
  (* CT-Var: x:T \in G => G |- x : T | {} *)
  | SVar x, ty -> (
      match lookup_term g x with
      | None -> fail (Printf.sprintf "Couldn't determine type of %s" x)
      | Some ty' ->
          if types_eq ty ty' then return []
          else
            fail
              (Printf.sprintf "Expected type %s but got %s" (string_of_typ ty)
                 (string_of_typ ty')))
  | SUnit, TUnit | STrue, TBool | SFalse, TBool | SNat _, TNat -> return []
  (* CT-Abs: G[x := t1] |- e : t2' | C => G |- \x:t1.t2 : t1' -> t2' | C *)
  | SLam (x, Some t1, e), TArrow (t1', t2') ->
      if types_eq t1 t1' then get_constraints (update_term g x t1) e t2'
      else
        fail
          (Printf.sprintf "Expected type %s but got %s" (string_of_typ t1)
             (string_of_typ t1'))
  (* CT-If: *)
  | SIfthenelse (b, e1, e2) -> 

(* 
(** Typecheck an [sterm] and produce a type-erased [term] and its [typ] *)
let typecheck = synth

(** Typecheck a top-level [sphrase] under [gamma], producing its type-erased
    [phrase], its [typ], and the context under which subsequent phrases should
    be typechecked. *)
let typecheck_phrase (gamma : typctx) (p : sphrase) :
    (typctx * phrase * typ, string) result =
  match p with
  | SPTerm t ->
      let* t', ty = synth gamma t in
      return (gamma, PTerm t', ty)
  | SPDef (x, Some ty, e) ->
      if type_wf gamma ty then
        let* e' = check gamma e ty in
        return (update_term gamma x (Some ty), PDef (x, e'), ty)
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ ty))
  | SPDef (x, None, e) ->
      let* e', ty = synth gamma e in
      return (update_term gamma x (Some ty), PDef (x, e'), ty) *)
