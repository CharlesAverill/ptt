(** Definitions for types used in the typechecker *)

open Syntax

exception TypeError of string
(** Type errors *)

type typctx = {
  terms : (string * typ) list;  (** Mapping from variables to their types *)
  tyvars : (string * (string * kind)) list;
      (** Mapping from type variables (as written by the user) to internal names
          and their kinds *)
  aliases : (string * (typ * kind)) list;
      (** Map of type aliases (stdlib- or user-defined) to their bodies and
          kinds *)
}
(** Type context *)

(** The empty type context *)
let empty_typctx = { terms = []; tyvars = []; aliases = [] }

let update_term (g : typctx) x t = { g with terms = (x, t) :: g.terms }
let lookup_term (g : typctx) x = List.assoc_opt x g.terms

let update_tyvar (g : typctx) x x' k =
  { g with tyvars = (x, (x', k)) :: g.tyvars }

let lookup_tyvar (g : typctx) x = List.assoc_opt x g.tyvars

let update_alias (g : typctx) x t k =
  { g with aliases = (x, (t, k)) :: g.aliases }

let lookup_alias (g : typctx) x = List.assoc_opt x g.aliases

type 'a subst = (int * 'a) list
(** Generic substitutions *)

(** Get the mapping of a generic variable *)
let lookup_subst (s : 'a subst) (x : int) : 'a option = List.assoc_opt x s

type state = {
  tsubst : typ subst;  (** Solutions found so far for type metavariables *)
  ksubst : kind subst;  (** Solutions found so far for kind metavariables *)
  next : int;
      (** Counter for generating fresh names for type and kind metavariables *)
}
(** The typechecker's state while checking a single phrase *)

let empty_state = { tsubst = []; ksubst = []; next = 0 }

(** Generate a number that hasn't been used yet in this phrase *)
let fresh_id (st : state) : int * state =
  (st.next, { st with next = st.next + 1 })
