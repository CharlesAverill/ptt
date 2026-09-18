(** Definitions for types used in the typechecker *)

open Syntax
open Monads

exception TypeError of string
(** Type errors *)

type typctx = {
  terms : (string * typ) list;  (** Mapping from variables to their types *)
  tyvars : (string * kind) list;
      (** Mapping from type variables to their kinds *)
  aliases : (string * typ) list;
      (** Map of type aliases (stdlib- or user-defined) *)
}
(** Type context *)

(** The empty type context *)
let empty_typctx = { terms = []; tyvars = []; aliases = [] }

let update_term (g : typctx) x t = { g with terms = (x, t) :: g.terms }
let lookup_term (g : typctx) x = List.assoc_opt x g.terms
let update_tyvar (g : typctx) x k = { g with tyvars = (x, k) :: g.tyvars }
let lookup_tyvar (g : typctx) x = List.assoc_opt x g.tyvars
let update_alias (g : typctx) x t = { g with aliases = (x, t) :: g.aliases }
let lookup_alias g x = List.assoc_opt x g.aliases

type 'a subst = (int * 'a) list
(** Generic substitutions *)

(** Domain of a generic substitution *)
let dom (s : 'a subst) = List.map fst s

(** Range of a generic substitution *)
let range (s : 'a subst) = List.map snd s

(** Get the mapping of a generic variable *)
let lookup_subst (s : 'a subst) (x : int) : 'a option = List.assoc_opt x s

(** Composition of generic substitutions, with [f] being the individual
    substutition function *)
let compose (f : 'a subst -> 'a -> 'a) (s : 'a subst) (g : 'a subst) : 'a subst
    =
  List.map (fun (x, gt) -> (x, f s gt)) g
  @ List.filter (fun (x, _) -> not (List.mem x (dom g))) s

(** Generic counter module *)
module Counter (M : sig
  type v

  val f : int -> v
end) =
struct
  let counter = ref 0
  let reset () = counter := 0

  let fresh () : M.v =
    let n = !counter in
    counter := !counter + 1;
    M.f n
end

type 'a constr = 'a * 'a
(** Generic constraints *)

type 'a constr_set = 'a constr list
(** Sets of generic constraints *)

(** Perform a type substitution in a constraint set, with [f] being the
    individual substitution function *)
let constr_subst (f : 'a subst -> 'a -> 'a) (s : 'a subst) (cs : 'a constr_set)
    : 'a constr_set =
  List.map (fun (a, b) -> (f s a, f s b)) cs
