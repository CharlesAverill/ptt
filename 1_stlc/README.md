# Simply-Typed Lambda Calculus

In this chapter we introduce the STLC and a basic typechecker, along with several pleasant constructs for the language.
Our goal is to write a type checker that can run before any code executes, reporting to the programmer if the program's type is sound.

```
$ dune exec -- stlc
>> 99;;                             
99 : nat
>> ();;
() : unit
>> true;;
true : bool
>> (\x:bool.x) 99;;
[ERROR] expected argument of type bool but got nat
>> if 5 == 6 then false else true;;
true : bool
>> if true then (\x:unit.x) else (\y:unit.y);;
\x.(x) : unit -> unit
>> (\x:bool.99) true;;
99 : nat
```

## Type checking

Let's define some basic typing rules for our language now.
We first introduce the concept of **typing judgements**:
$$
\Gamma \vdash e : T
$$
Or, "in **typing context** Gamma, e has type T."
A typing context is simply a map from variables to the types that they posess.
Using this notation, let's define a set of typing rules for the language:\

$$
\frac{}{\Gamma \vdash () : \texttt{unit}}(\texttt{unit})
$$
$$
\frac{}{\Gamma \vdash n : \texttt{nat}}(\texttt{nat})
$$
$$
\frac{}{\Gamma \vdash \texttt{true}, \texttt{false} : \texttt{bool}}(\texttt{bool})
$$
$$
\frac{\Gamma\ v = T}{\Gamma \vdash v : T}(var)
$$
$$
\frac{\Gamma[v \gets T_2] \vdash E_1 : T_1}{\Gamma\ (\lambda v : T_2. E_1) : T_2 \to T_1}(abs)
$$
$$
\frac{\Gamma \vdash E_1 : T_2 \to T_1 \quad \Gamma \vdash E_2 : T_2}{\Gamma \vdash E_1\ E_2 : T_1}(app)
$$
$$
\frac{\Gamma \vdash b : \texttt{bool} \quad \Gamma \vdash E_1, E_2 : T}{\Gamma \vdash \texttt{if } b \texttt{ then } E_1 \texttt{ else } E_2 : T}(if)
$$
$$
\frac{\Gamma \vdash n, m : \texttt{nat}}{\Gamma \vdash n \texttt{ == } m : \texttt{bool}}(eq)
$$

Looking at [typechecker.ml](lib/typechecker.ml), we can see that the `typeof` function encodes each of these rules.
Interestingly, the function constructs the type of the term passed into it.
This is **type synthesis**, which we will look at again when we study bidirectional typing.

## Type erasure

You might have noticed that `typeof` actually deals with two kinds of terms: `sterm`s which carry some typing information with them, and `term`s which carry none.
In practice, we are generally not interested in carrying typing information down to the level of executable code.
Instead, **type erasure** is the common practice of erasing all typing information from a program once it has passed the type checker.
This prevents us from having to carry around type data at runtime.

Right now, the parser enforces that lambda functions always annotate the type.
However, you can see that the types have been erased in the computational value in the following example:
```
>> \x:bool.\y:nat.();;
\x.(\y.(())) : bool -> nat -> unit
```
Solely for pedagogy, the interpreter does hang on to types for now so that it can print them after evaluation.
But inspecting the [evaluation loop](./lib/driver.ml) shows that the computational value is a [term], completely free of typing information.

## Y-Combinator
In the previous chapter, we saw the general-purpose fixpoint operator:

$$
    \lambda f. (\lambda x. f (x\ x)) (\lambda x. f (x\ x))
$$

and observed that applying it to itself results in an infinite loop.
This infinite loop occurs because the term $Y\ Y$ is **ill-typed**.
In the STLC, we enforce well-typedness such that it is impossible to represent the Y-combinator.
On your own, try to write down type annotations for each lambda binding in the term above, just like what is now required by the parser and type checker we've implemented.

## Progress and Preservation

## Strong Normalization
