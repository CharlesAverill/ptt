# Parametric Polymorphism

[Parametric Polymorphism](../reading/ParametricPolymorphism.pdf) - Frank Pfenning

At this point, we've implemented the STLC and a bidirectional type checker that allows users to elide certain type annotations.
In this chapter, we will extend our type checker to **System F**, an extension to the STLC that adds **polymorphic functions**, or, functions that can take arguments of any type.
The simplest example is the polymorphic identity function,

$$
\Lambda \alpha. \lambda x : \alpha. x
$$

where $\alpha$ is a **type variable** that may be instantiated with any type to describe the type of $x$.
In the STLC, we would need to explicitly define, for example, a `nat`-typed identity function, a `bool`-typed identity function, and so on.
For now, the identity function will be about the most interesting polymorphic function we can implement without baking in some more operations and fundamental datatypes to our type system, but the utility of polymorphic functions will soon become clear.
In the reading, Pfenning motivates polymorphic functions with the example of an `add` function that can take on either `int -> int -> int` or `float -> float -> float` depending the types of its arguments.

This chapter marks our first foray onto the edges of the *lambda cube*, a map of type system extensions that guides an implementer towards a highly-expressive calculus called the **Calculus of Constructions**.
This language is at the heart of dependently-typed proof checkers like [Rocq](https://rocq-prover.org/), [Lean](https://lean-lang.org/), and [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).
Although this is the final point on the cube, the set of paths along the way describe the primary features necessary to implement real-world programming language type systems like those of [OCaml](https://ocaml.org/), [Haskell](https://www.haskell.org/), and [Rust](https://rust-lang.org/) (although each substantially extends the features we'll see here).

The following figure shows the lambda cube with annotations relevant to our coursework.
Each direction represents a feature one can add to a type system (so the edges from $\lambda\to$ to $\lambda2$ and $\lambda P$ to $\lambda P2$ both represent parametric polymorphism).
In this course, we will take the green path: polymorphism, then type constructors, then dependent types.
Thus, by adding polymorphism to our STLC, we will reach an implementation of [System F](https://en.wikipedia.org/wiki/System_F), which was proposed independently by Jean-Yves Girard and John C. Reynolds in the 1970s.

![lambda cube](../media/cube.png)
