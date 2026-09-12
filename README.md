# Practical Type Theory

This repo contains course materials for PTT, a reading course on introductory type theoretical topics such as
- Parametric polymorphism
- Recursive types
- Dependent typing
- Type inference

This course is primarily interested in **type checkers** and will not include treatments of other aspects of language design like evaluation strategies, parsing, optimization, etc.
The material is presented through successive iterations on an OCaml interpreter for the lambda calculus.

# opam Setup

```
opam init
opam switch create ptt 5.3.0
opam install dune menhir ocamllex ocamlformat
```

# Chapters

0. [Untyped Lambda Calculus](./1_ulc) - an interpreter for the untyped lambda calculus, given as a base for students to develop on top of
1. [Simply-Typed Lambda Calculus](./2_stlc) - adding a simple type system to the lambda calculus
2. [Bidirectional Typing](./3_bt) - 
