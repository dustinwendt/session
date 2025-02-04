[![Build Status](https://travis-ci.org/coq-community/dblib.svg?branch=master)](https://travis-ci.org/coq-community/dblib)

# Dblib

- **Author**: François Pottier, INRIA. 2013.
- **License**: GNU GPLv3. See [LICENSE](LICENSE).
- **Requirements**: Coq 8.5~8.10

## What is Dblib?

The dblib library offers facilities for working with de Bruijn indices in
Coq. The basic idea is as follows:

1. The client manually defines the syntax of terms (or types, or whatever
   syntax she is interested in) as usual, as an inductive type;

2. The client manually defines a higher-order "traverse" function, which can
   be thought of as a generic, capture-avoiding substitution function. Its
   job is (i) to apply a user-supplied function f at every variable, and
   (ii) to inform f about the number of binders that have been entered. By
   defining "traverse", the client effectively defines the binding structure.

3. The client proves that the "traverse" function is well-behaved, i.e., it
   satisfies half a dozen reasonable properties. This proof is usually
   trivial, because the library provides tailor-made tactics for this
   purpose.

4. The library defines weakening ("lift") and substitution ("subst") in
   terms of "traverse", and proves a rather large number of properties of
   these functions.

5. The functions "lift" and "subst" are opaque, so an application of these
   functions cannot be reduced by Coq's builtin tactic "simpl". The library
   provides "simpl_lift_goal" and "simpl_subst_goal" for this purpose (plus
   a few variants of these tactics that perform simplification within a
   hypothesis, or within all hypotheses).

6. The library also provides hint databases, to be used with [eauto], that
   can prove many of the typical equalities that arise when proving
   weakening or substitution lemmas.

7. The library defines a "closed" term as one that is invariant under
   lifting (and substitution), and provides lemmas/tactics for reasoning
   about this notion.

Everything is based on type classes: `traverse`, `lift`, `subst`, etc. are
overloaded, so the whole process can be repeated, if desired, for another
inductive type

The library *does* support multiple *independent* namespaces: for instance, it
is possible to have terms that contain term variables and types that contain
type variables.

The library does *not* support multiple namespaces when there is interaction
between them: for instance, it is *not* possible to have terms that contain
both term variables and type variables, as in a standard presentation of
System F. A possible work-around is to define a single namespace of
"variables" and to use a separate well-kindedness judgement in order to
distinguish between "term" variables and "type" variables. I have used this
approach in a large proof where it has turned out to be extremely beneficial.

## Library Files

The library consists of the following files:

- [DblibTactics.v](src/DblibTactics.v)  
  A small number of hints and tactics that are used in the library.
  The end user should not need to worry about them, but can go and
  have a look.

- [DeBruijn.v](src/DeBruijn.v)  
  The core library. The end user is encouraged to read the first
  two parts of this file, which present 1- the operations and
  properties that the client is expected to provide; and 2- the
  operations and properties that the library provides. These two
  parts extend up to the first double dashed line, near line 432.

- [Environments.v](src/Environments.v)  
  This auxiliary library defines a notion of environment, which
  is typically useful when defining a typing judgement. The use
  of this library is optional.

## Demos

The documentation takes the form of a few demo files:

- [DemoLambda.v](src/DemoLambda.v)  
  Small-step operational semantics and typing judgement for the
  simply-typed lambda-calculus. Proof of type preservation and
  of a few other basic lemmas.

- [DemoValueTerm.v](src/DemoValueTerm.v)  
  Short demo of how to use the library in the case where there
  are two distinct syntactic categories of things in which we
  substitute (e.g., terms) and things that we substitute (e.g.,
  values).

- [DemoExplicitSystemF.v](src/DemoExplicitSystemF.v)  
  Proof of type preservation for System F, in a version where
  the presence of type abstractions and type applications is
  explicit in the syntax of terms. (Still, terms do not refer
  to types!)

- [DemoImplicitSystemF.v](src/DemoImplicitSystemF.v)  
  Proof of type preservation for System F, in a version where
  type abstraction and type application are implicit, i.e.,
  the syntax of terms is untyped. This proof is trickier than
  the one above, in that it requires induction over the height
  of type derivations. But as far as binding is concerned, no
  new problems arise.
