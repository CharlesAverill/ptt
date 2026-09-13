# Practical Type Theory

This repo contains course materials for PTT, a reading course on introductory type theoretical topics such as type inference, polymorphism, recursve and dependent types.

This course is primarily interested in **type checkers** and will not include treatments of other aspects of language design like evaluation strategies, parsing, optimization, etc.
The material is presented through successive iterations on an OCaml interpreter for the lambda calculus.

# opam Setup

```
opam init
opam switch create ptt 5.3.0
opam install dune menhir ocamlformat
```

# Chapters

0. [Untyped Lambda Calculus](./0_ulc) - an interpreter for the untyped lambda calculus, given as a base for students to develop on top of
1. [Simply-Typed Lambda Calculus](./1_stlc) - a simple type system to the lambda calculus
2. [Recursive Types and Bidirectional Typing](./2_rt_bt) - type definitions in the style of OCaml/Rocq and a precursor to robust type inference
3. [Hindley-Milner Type Inference](./3_hm) - robust type inference for large inter-dependent programs
4. [Parametric Polymorphism](./4_poly) - generic functions
5. [Type operators](./5_ops) - template types/metaprogramming
6. [Dependent types](./6_dt) - types dependent on values
