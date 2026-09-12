# Untyped Lambda Calculus

This project serves as the base for later sections of the course.
We define a parser and interpreter for the [Untyped Lambda Calculus](https://en.wikipedia.org/wiki/Lambda_calculus).

```
$ dune exec -- ulc
>> \x.x;;                           
\x.(x)
>> (\x.x x)(\y.y);;
\y.(y)
>> \x.\y.\z.x;;
\x.(\y.(\z.(x)))
>> \x.
\y.
x;;
\x.(\y.(x))
```

## Syntax

The ULC consists of three syntactic structures defined in [syntax.ml](lib/syntax.ml):
1. **Variables** (`v`)
2. **Abstractions** (`\x.t`) or functions
3. **Applications** (`t1 t2`)

A [lexer](lib/lexer.mll) and [parser](lib/parser.mly) are included.

## Evaluation

[eval.ml](lib/eval.ml) defines an executable small-step semantics and interpreter loop for the ULC.
This semantics defines a notion of **values**, or terms which cannot reduce any further.
For now, the only values are functions, as we can only reduce them when they are applied to other terms.

The reduction rules, in order of priority, are:
1. Variables and functions do not reduce
2. Apply [**beta-reduction**](https://ncatlab.org/nlab/show/beta-reduction) when the LHS of an application is a function and the RHS is a value, or
    $$
    \frac{\texttt{is\_value}\ t}
    {(\lambda v.x)\; t \Rightarrow x[t/v]}
    $$
    where $x[t/v]$ is syntax for [**capture-avoiding substitution**](https://courses.cs.cornell.edu/cs3110/2021sp/textbook/interp/subst_lambda.html)
3. Reduce the RHS of an application if the LHS is a value
4. Reduce the LHS of an application

## Typing

This language has no types, allowing programmers to define poorly-typed terms.
For example, consider the [Y-combinator](https://en.wikipedia.org/wiki/Fixed-point_combinator):
$$
    \lambda f. (\lambda x. f (x\ x)) (\lambda x. f (x\ x))
$$
The Y-combinator acts as a general-purpose fixpoint operator, enabling general recursion.
However, this value is not well-typed, and breaks soundness of the simple type systems we will see in this course.
As a result, we are able to construct non-terminating programs, such as
```
>> (\f.(\x.f (x x))(\x.f (x x)))(\f.(\x.f (x x))(\x.f (x x)));;
```
