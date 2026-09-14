(** Bidirectional Typechecking and type erasure for STLC *)

open Syntax
open Monads

exception TypeError of string

type typctx = string -> typ option
(** Mapping from variables to their types *)

(** Functional update *)
let update f x y = fun x' -> if x = x' then y else f x'

(** Synthesize the type of a [sterm] under context [gamma], producing both its
    [typ] and its type-erased [term] on success. *)
let rec synth (gamma : typctx) (t : sterm) : (typed_term, string) result =
  match t with
  (* Var: G v = T => G |- v => T *)
  | SVar v -> (
      match gamma v with
      | Some ty -> return (Var v, ty)
      | None -> fail (Printf.sprintf "unbound variable %s" v))
  (* Anno: G |- e <= T => G |- (e : T) => T *)
  | SAnn (e, ty) ->
      let* e' = check gamma e ty in
      return (e', ty)
  (* ->E: G |- E1 => (T2 -> T1) => G |- E2 <= T2 => G |- e1 e2 => T1 *)
  | SApp (e1, e2) -> (
      let* e1', t1 = synth gamma e1 in
      match t1 with
      | TArrow (targ, tres) ->
          let* e2' = check gamma e2 targ in
          return (App (e1', e2'), tres)
      | _ ->
          fail
            (Printf.sprintf "cannot apply non-function of type %s"
               (string_of_typ t1)))
  (* G[x := t2] |- body => t1 => \x:t2.body => t2 -> t1 *)
  | SLam (x, Some t2, body) ->
      let* body', t1 = synth (update gamma x (Some t2)) body in
      return (Lam (x, body'), TArrow (t2, t1))
  (* G |- n, m : nat => G |- n == m : bool *)
  | SIseq (x, y) ->
      let* x' = check gamma x TNat in
      let* y' = check gamma y TNat in
      return (Iseq (x', y'), TBool)
  | _ ->
      fail
        (Printf.sprintf "Cannot synthesize type for term %s" (string_of_sterm t))

(** Check that the type of [t] matches [ty] under [gamma], and return the
    type-erased version if so *)
and check (gamma : typctx) (t : sterm) (ty : typ) : (term, string) result =
  match (t, ty) with
  (* primitive types *)
  | SUnit, TUnit -> return Unit
  | STrue, TBool -> return True
  | SFalse, TBool -> return False
  | SNat n, TNat -> return (Nat n)
  (* ->|: G[x := a1] |- e <= a2 => G |- \x.e <= a1 -> a2 *)
  | SLam (x, None, e), TArrow (a1, a2) ->
      let* e' = check (update gamma x (Some a1)) e a2 in
      return (Lam (x, e'))
  (* G |- b <= bool => G |- c1, c2 <= T => |- if b then c1 else c2 <= T *)
  | SIfthenelse (b, c1, c2), _ ->
      let* b' = check gamma b TBool in
      let* c1' = check gamma c1 ty in
      let* c2' = check gamma c2 ty in
      return (Ifthenelse (b', c1', c2'))
  (* Sub: G |- e => A => A = B => G |- e <= B *)
  | e, b ->
      let* e', a = synth gamma e in
      if a = b then return e'
      else
        fail
          (Printf.sprintf "type mismatch: expected %s but got %s"
             (string_of_typ a) (string_of_typ b))

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
      let* e' = check gamma e ty in
      return (update gamma x (Some ty), PDef (x, e'), ty)
  | SPDef (x, None, e) ->
      let* e', ty = synth gamma e in
      return (update gamma x (Some ty), PDef (x, e'), ty)
