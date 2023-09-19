TL;DR HOWTO INSTALL
===================

- Install opam through your favourite means.
- Double-check that no Coq-related environment variables like COQBIN or COQPATH are set.
- Launch the following commands in the folder of this development.
```
opam switch create . --empty
eval $(opam env)
opam install ocaml-base-compiler=4.11.2
opam repo --this-switch add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
make
```

IMPORTANT NOTE
==============

The coqdocjs and coq-partialfun subfolders are **not** part of this development, but independent projects vendored here for simplicity of the build process. The upstream repositories can be respectively found at:
- https://github.com/coq-community/coqdocjs/
- https://github.com/TheoWinterhalter/coq-partialfun.git

Presentation
=======

This repo contains formalisation work on implementing a logical relation over MLTT with one universe.
This formalisation follows the [work done by Abel et al.]((https://github.com/mr-ohman/logrel-mltt/)) (described in [Decidability of conversion for Type Theory in Type Theory, 2018](https://dl.acm.org/doi/10.1145/3158111)), and [Pujet's work](https://github.com/loic-p/logrel-mltt) on removing induction-recursion from the previous formalization, making it feasible to translate it from Agda to Coq.

The definition of the logical relation (**LR**) ressembles Pujet's in many ways, but also had to be modified for a few reasons :
- Because of universe constraints and the fact that functors cannot be indexed by terms in Coq whereas it is possible in Agda, the relevant structures had to be parametrized by a type level and a recursor, and the module system had to be dropped out entirely.
- Since Coq and Agda's positivity checking for inductive types is different, it turns out that **LR**'s definition, even though it does not use any induction-induction or induction-recursion in Agda, is not accepted in Coq. As such, the predicate over Π-types for **LR** has been modified compared to Agda. You can find a MWE of the difference in positivity checking in the two systems in [Positivity.v] and [Positivity.agda].

In order to avoid some work on the syntax, this project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate.

The project builds with Coq version `8.16.1`. It needs the opam package `coq-smpl`. Once these have been installed, you can simply issue `make` in the root folder.

The `make depgraph` recipe can be used to generate the dependency graph.

Browsing the development
==================

The development can be rendered using `coqdoc`.

Syntax (re)generation
============

The syntax boilerplate has been generated using AutoSubst OCaml with the options `-s ucoq -v ge813 -allfv` (see the [AutoSubst OCaml documentation](https://github.com/uds-psl/autosubst-ocaml) for installation instructions for it). Currently, this package works only with older version of Coq (8.13), so we cannot add a recipe to the MakeFile for automatically
re-generating the syntax.

**If you wish to regenerate the syntax** by hand, install autosubst paying attention to [this issue](https://github.com/uds-psl/autosubst-ocaml/issues/1) -- in an opam installation do a `cp -R $OPAM_SWITCH_PREFIX/share/coq-autosubst-ocaml $OPAM_SWITCH_PREFIX/share/autosubst`--, modify the syntax file `AutoSubst/Ast.sig`, run autosubst on it (`autosubst -s ucoq -v ge813 -allfv Ast.sig -o Ast.v`) and patch the resulting files using the checked in patch (`git apply -R autosubst-patch.diff`). This patch does two things, which can also be done by hand if the automatic patching fails:
- change the imports at the beginning of the files;
- add the `#[global]` keyword to all instances.

Getting started with using the development
=================

A few things to get accustomed to if you want to use the development.

Notations and refolding
-----------

In a style somewhat similar to the [Math Classes](https://math-classes.github.io/) project,
generic notations for typing, conversion, renaming, etc. are implemented using type-classes.
While some care has been taken to try and respect the abstractions on which the notations are
based, they might still be broken by carefree reduction performed by tactics. In this case,
the `refold` tactic can be used, as the name suggests, to refold all lost notations.

Induction principles
----------

The development relies on large, mutually-defined inductive relations. To make proofs by induction
more tractable, functions `XXXInductionConcl` are provided. These take the predicates
to be mutually proven, and construct the type of the conclusion of a proof by mutual induction.
Thus, a typical induction proof looks like the following:

``` coq-lang
Section Foo.

Let P := … .
…

Theorem Foo : XXXInductionConcl P … .
Proof.
  apply XXXInduction.

End Section.
```
The names of the arguments printed when querying `About XXXInductionConcl` should make it clear 
to which mutually-defined relation each predicate corresponds.

[Utils]: ./theories/Utils.v
[BasicAst]: ./theories/BasicAst.v
[Context]: ./theories/Context.v
[AutoSubst/]: ./theories/AutoSubst/
[AutoSubst/Extra]: ./theories/AutoSubst/Extra.v
[Notations]: ./theories/Notations.v
[Automation]: ./theories/Automation.v
[NormalForms]: ./theories/NormalForms.v
[UntypedReduction]: ./theories/UntypedReduction.v
[GenericTyping]: ./theories/GenericTyping.v
[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[Properties]: ./theories/Properties.v
[DeclarativeInstance]: ./theories/DeclarativeInstance.v
[LogicalRelation]: ./theories/LogicalRelation.v
[Induction]: ./theories/LogicalRelation/Induction.v
[Escape]: ./theories/Escape.v
[Reflexivity]: ./theories/Reflexivity.v
[Irrelevance]: ./theories/Irrelevance.v
[ShapeView]: ./theories/ShapeView.v
[Positivity.v]: ./theories/Positivity.v
[Weakening]: ./theories/Weakening.v
[Substitution]: ./theories/Substitution.v
[AlgorithmicTyping]: ./theories/AlgorithmicTyping.v
[AlgorithmicConvProperties]: ./theories/AlgorithmicConvProperties.v
[AlgorithmicTypingProperties]: ./theories/AlgorithmicTypingProperties.v
[LogRelConsequences]: ./theories/LogRelConsequences.v
[BundledAlgorithmicTyping]: ./theories/BundledAlgorithmicTyping.v

[autosubst-ocaml]: https://github.com/uds-psl/autosubst-ocaml
[Positivity.agda]: ./theories/Positivity.agda
