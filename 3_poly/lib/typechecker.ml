(** Bidirectional Typechecking and type erasure for System F *)

open Syntax
open Monads

exception TypeError of string
(** Type errors *)

type typctx = {
  terms : string -> typ option;  (** Mapping from variables to their types *)
  tyvars : string list;  (** Set of bound type variables *)
}
(** Type context *)

(** The empty type context *)
let empty_typctx = { terms = (fun _ -> None); tyvars = [] }

let update_term (f : typctx) x y =
  { terms = (fun x' -> if x = x' then y else f.terms x'); tyvars = f.tyvars }

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

let rec type_wf (gamma : typctx) (t : typ) : bool =
  match t with
  | TUnit | TBool | TNat -> true
  | TVar v -> List.mem v gamma.tyvars
  | TArrow (t1, t2) -> type_wf gamma t1 && type_wf gamma t2
  | TForall (alpha, t') -> type_wf (update_tyvar gamma alpha true) t'

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

(** Synthesize the type of a [sterm] under context [gamma], producing both its
    [typ] and its type-erased [term] on success. *)
let rec synth (gamma : typctx) (t : sterm) : (typed_term, string) result =
  match t with
  (* Var: G v = T => G |- v => T *)
  | SVar v -> (
      match gamma.terms v with
      | Some ty -> return (Var v, ty)
      | None -> fail (Printf.sprintf "unbound variable %s" v))
  (* Anno: G |- e <= T => G |- (e : T) => T *)
  | SAnn (e, ty) ->
      if type_wf gamma ty then
        let* e' = check gamma e ty in
        return (e', ty)
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ ty))
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
      if type_wf gamma t2 then
        let* body', t1 = synth (update_term gamma x (Some t2)) body in
        return (Lam (x, body'), TArrow (t2, t1))
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ t2))
  (* G |- n, m : nat => G |- n == m : bool *)
  | SIseq (x, y) ->
      let* x' = check gamma x TNat in
      let* y' = check gamma y TNat in
      return (Iseq (x', y'), TBool)
  (*G['a := true] |- e' => b => /\'a.e => forall 'a. b*)
  | STLam (alpha, e) ->
      let* e', b = synth (update_tyvar gamma alpha true) e in
      return (e', TForall (alpha, b))
  (* G |- e => forall 'a.'b => G |- 'k type => G |- e['k] => 'b['a := 'k] *)
  | SPolyApp (e, Some kappa) -> (
      let* e', ety = synth gamma e in
      match ety with
      | TForall (alpha, beta) ->
          if type_wf gamma kappa then return (e', tcas beta alpha kappa)
          else
            fail
              (Printf.sprintf "Type [%s] is not well-formed"
                 (string_of_typ kappa))
      | _ ->
          fail
            (Printf.sprintf "Expected polymorphic type but got %s"
               (string_of_typ ety)))
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
      let* e' = check (update_term gamma x (Some a1)) e a2 in
      return (Lam (x, e'))
  (* G |- b <= bool => G |- c1, c2 <= T => |- if b then c1 else c2 <= T *)
  | SIfthenelse (b, c1, c2), _ ->
      let* b' = check gamma b TBool in
      let* c1' = check gamma c1 ty in
      let* c2' = check gamma c2 ty in
      return (Ifthenelse (b', c1', c2'))
      (* G['a := true] |- e <= B => G |- /\'a.e <= forall 'a. B *)
  | STLam (alpha, e), TForall (alpha', b) ->
      let b' = if alpha = alpha' then b else tcas b alpha' (TVar alpha) in
      let* e' = check (update_tyvar gamma alpha true) e b' in
      return e'
  (* Sub: G |- e => A => A = B => G |- e <= B *)
  | e, b ->
      let* e', a = synth gamma e in
      if types_eq a b then return e'
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
      if type_wf gamma ty then
        let* e' = check gamma e ty in
        return (update_term gamma x (Some ty), PDef (x, e'), ty)
      else fail (Printf.sprintf "Type %s is not well-formed" (string_of_typ ty))
  | SPDef (x, None, e) ->
      let* e', ty = synth gamma e in
      return (update_term gamma x (Some ty), PDef (x, e'), ty)
