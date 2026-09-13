# Bidirectional Typing

[Bidirectional Typing](https://arxiv.org/abs/1908.05839) - Dunfield and Krishnaswami

In the last chapter, we added a simple type system to our interpreter.
In the process, we ended up requiring type annotations for lambda functions:

```
>> \x:unit.x;;
\x.(x) : unit -> unit
```

But sometimes this information feels extraneous.
In the above example, the annotation is necessary because there is no other typing information in the term to indicate what the type of `x` should be, let alone the function.
However, in the following example, there **is** typing information that implies the type of an un-annotated function:

```
>> (\f:unit->unit. f ()) (\x.x);;
() : unit
```

Ideally, we would like to **infer** the types of functions and other terms wherever possible, freeing up the user to choose not to annotate terms with types as they see fit.
In this course we will look at two levels of this concept:
1. **Bidirectional Typing** - inferring types from the existence of **type annotations**
2. **Hindley-Milner Type Inference** - inferring types from **constraints** on the usages of terms without annotations

An example of where HM inference succeeds but BT does not:

```
>> (\x.x) true;;
```

Here, there is no **explicit** type annotation for BT to succeed.
We could manually add in a rule to our type checker that says application LHSs can receive typing information from their RHSs, but this is getting messy and farther away from theoretical foundations, and does not scale up to terms that are not just literals.
HM can infer that the type of `x` must be `bool` due to the **constraint** placed on it by accepting `true` as an argument.

## Synthesizing vs. Checking

As a reminder, here's the last version of our typechecker:

```ocaml
(** Compute the type of a [sterm] under context [gamma], producing both its
    [typ] and its type-erased [term] on success. *)
let rec typeof (gamma : typctx) (t : sterm) : (typed_term, string) result =
  match t with
  (* |- () : unit *)
  | SUnit -> return (Unit, TUnit)
  (* |- true,false : bool *)
  | STrue -> return (True, TBool)
  | SFalse -> return (False, TBool)
  (* G |- b : bool => G |- c1, c2 : T => |- if b then c1 else c2 : T *)
  | SIfthenelse (b, c1, c2) ->
      let* b', btyp = typeof gamma b in
      if btyp = TBool then
        let* c1', c1typ = typeof gamma c1 in
        let* c2', c2typ = typeof gamma c2 in
        if c1typ = c2typ then return (Ifthenelse (b', c1', c2'), c1typ)
        else
          fail
            (Printf.sprintf "Expected type %s but got %s" (string_of_typ c1typ)
               (string_of_typ c2typ))
      else fail (Printf.sprintf "Branch parameters must be of type bool")
  (* |- n : nat *)
  | SNat n -> return (Nat n, TNat)
  (* |- n, m : nat => |- n == m : bool *)
  | SIseq (x, y) ->
      let* x', xtyp = typeof gamma x in
      let* y', ytyp = typeof gamma y in
      if xtyp = TNat && ytyp = TNat then return (Iseq (x', y'), TBool)
      else
        fail
          (Printf.sprintf "Expected nats but got %s,%s" (string_of_typ xtyp)
             (string_of_typ ytyp))
  (* G v = T => G |- v : T *)
  | SVar v -> (
      match gamma v with
      | Some ty -> return (Var v, ty)
      | None -> fail (Printf.sprintf "unbound variable %s" v))
  (* G[v := t2] |- body : T1 => G |- \v:T2.body : T2 -> T1 *)
  | SLam (v, t2, body) ->
      let* body', t1 = typeof (update gamma v (Some t2)) body in
      return (Lam (v, body'), TArrow (t2, t1))
  (* G |- E1 : (T2 -> T1) => G |- E2 : T2 => G |- e1 e2 : T1 *)
  | SApp (e1, e2) -> (
      let* e1', t1 = typeof gamma e1 in
      let* e2', t2 = typeof gamma e2 in
      match t1 with
      | TArrow (targ, tres) when targ = t2 -> return (App (e1', e2'), tres)
      | TArrow (targ, _) ->
          fail
            (Printf.sprintf "expected argument of type %s but got %s"
               (string_of_typ targ) (string_of_typ t2))
      | _ ->
          fail
            (Printf.sprintf "cannot apply non-function of type %s"
               (string_of_typ t1)))
```

We have a mix of techniques going on here, but the `typeof` function is largely performing **type synthesis**: given a term, it produces the type the term inhabits.
If we can synthesize a type for a term, it typechecks, otherwise it is not well-typed.
The notation for synthesis is $\Gamma \vdash e \Rightarrow T$, or "Gamma proves that e synthesizes T."

The direction of the arrow is important, it reads like we are extracting types from terms.
Bidirectional Typing adds a second component that flips the arrow ($\Gamma \vdash e \Leftarrow T$) and is un-creatively named **type checking**.
Instead of trying to pull an unknown type out of a term, it tries to push a known type into a term.
We will combine these two approaches to make our typechecker more powerful.

But first, let's return to an example and see how checking can solve problems synthesis can't.
In this example from before:

$$
(\lambda f : \texttt{unit} \to \texttt{unit}. f ()) (\lambda x.x)
$$

we can observe that plain synthesis fails by passing the term to our type checker.
Let's pretend that typing annotations are optional, and our previous rule for lambdas:

```ocaml
  (* G[v := t2] |- body : T1 => G |- \v:T2.body : T2 -> T1 *)
  | SLam (v, t2, body) ->
      let* body', t1 = typeof (update gamma v (Some t2)) body in
      return (Lam (v, body'), TArrow (t2, t1))
```

no longer applies because it expects a typing annotation.
Thus, there is no type to bind to `v`, and so we have no rule in our type synthesizer to determine the type of $\lambda x.x$.

When we add checking, we gain a rule about applications that instructs our type checker to **synthesize** the type for the LHS and **check** the RHS against the **domain** of the LHS.
We can indeed synthesize the LHS's type as $(\texttt{unit} \to \texttt{unit}) \to \texttt{unit}$.
This gives checking ammunition: it knows that the RHS must be a $\texttt{unit} \to \texttt{unit}$ function, so it can impose the $\texttt{unit}$ type onto the lambda binder `x`.
It then recursively checks the body of the RHS, which indeed returns `x`, a $\texttt{unit}$.
Thus, checking succeeds and this expression is well-typed.

## The new typechecker

Looking at [typechecker.ml](./lib/typechecker.ml), we can see that there are now two co-recursive functions `synth` and `check`, which synthesize types from a term and check that a term matches a type, respectively.
We've also added general typing annotations `(x : t)` that allow a user to explicitly type any term, not just lambda binders.
Let's look at the rules inspired by Figure 1 in the paper linked at the very top of this document:

```ocaml
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

(* ... *)

and check (gamma : typctx) (t : sterm) (ty : typ) : (term, string) result =
  match t, ty with
  (* primitive types *)
  | SUnit, TUnit -> return Unit
  | STrue, TBool -> return True
  | SFalse, TBool -> return False
  | SNat n, TNat -> return (Nat n)
  (* ->|: G[x := a1] |- e <= a2 => G |- \x.e <= a1 -> a2 *)
  | SLam (x, None, e), TArrow (a1, a2) ->
    let* e' = check (update gamma x (Some a1)) e a2 in
    return (Lam (x, e'))
  (* Sub: G |- e => A => A = B => G |- e <= B *)
  | e, b ->
    let* e', a = synth gamma e in
    if a = b then
      return e'
    else
      fail (Printf.sprintf "type mismatch: expected %s but got %s" (string_of_typ a) (string_of_typ b))
```

Notice that there is no syntactic structure that has both a rule in `synth` and `check`, each is only in one or the other.
Why is this?
Before reading on, try and spot the differences between the kind of terms that you see in `synth` and the kind you see in `check`.
Here's the split without all of the noise:

```
Terms with synth rules
----------------------
v (variables)
(x : t)
e1 e2


Terms with check rules
----------------------
unit
true, false
n (numbers)
\x.e
```

The split is between **elimination** and **introduction** forms.
These terms get thrown around a lot in PL and formal logic, but here 
elimination forms are composite terms that contain their own typing information, and introduction forms construct new terms.
In other words, introduction forms *introduce* logical connectives (`\x.e` introduces `->`, and `true`, `()`, `5` introduce their base types), and elimination forms *eliminate* logical connectives (`e1 e2` eliminates an `->`).
The rules for variables and annotations are technically neither introduction nor elimination rules, but fit in better with eliminations (variables carry their own typing via the typing context, annotations carry their own typing via the annotation).

This divide might seem immediately ambiguous, given that, `unit`, `true`, `false`, and `n` all trivially relate to the types they inhabit, and so should have synth rules.
Indeed, giving them check rules introduces the following strange behavior in our interpreter:

```
$ dune exec bt
>> 5;;                             
[ERROR] Cannot synthesize type for term 5
>> (5 : nat);;
5 : nat
```

I've chosen to build the typechecker this way solely to resemble the presentation in our reading as closely as possible, but the paper recognizes that making these terms have synth rules [recovers limited forms of some of the nice properties of bidirectional typing](https://arxiv.org/pdf/1908.05839#page=25).

Note that we also have rules for the other structures we've included in our language:
```ocaml
let rec synth (gamma : typctx) (t : sterm) : (typed_term, string) result =
  match t with
  (* ... *)
  (* G[x := t2] |- body => t1 => \x:t2.body => t2 -> t1 *)
  | SLam (x, Some t2, body) ->
    let* body', t1 = synth (update gamma x (Some t2)) body in
    return (Lam (x, body'), TArrow (t2, t1))
  (* G |- n, m : nat => G |- n == m : bool *)
  | SIseq (x, y) ->
      let* x' = check gamma x TNat in
      let* y' = check gamma y TNat in
      return (Iseq (x', y'), TBool)

and check (gamma : typctx) (t : sterm) (ty : typ) : (term, string) result =
  match t, ty with
  (* ... *)
  (* G |- b <= bool => G |- c1, c2 <= T => |- if b then c1 else c2 <= T *)
  | SIfthenelse (b, c1, c2), _ ->
      let* b' = check gamma b TBool in
      let* c1' = check gamma c1 ty in
      let* c2' = check gamma c2 ty in
      return (Ifthenelse (b', c1', c2'))
```
The equality synthesis rule is straightforward: we know that the arguments must be `nat`s, and we're synthesizing the return type of `bool`.
Note that we have a second rule for lambdas here!
It is not a duplicate of the check rule, it handles lambdas with binder annotations.
Similar to the last chapter, we can now synthesize the codomain by synthesizing the type of the body.
Finally, we have a check rule for `if b then c1 else c2` because we know that `b` must be a bool and `c1` and `c2` must have the type of the entire expression.

## Why?

So why are we even willing to sacrifice trivial typechecking behaviors?
There are at least two answers.

1. **We don't have to sacrifice.** In some bidirectional type systems, the typechecker falls back on synthesis when checking cannot succeed. This is not a general-purpose inference like Hindley-Milner, but is good enough that we can do things like
```coq
(* no expected type here, so synthesization is necessary *)
Definition x := 5.
Check x. (* x : nat *)
```
2. **Type inference is undecidable for some type systems.** The type system we'd like to implement by the end of this course, **dependent typing**, does not have decidable type inference in the general case. Thus, these systems must fall back on checking, which is decidable, and synthesis, which helps reduce manual annotation count.
