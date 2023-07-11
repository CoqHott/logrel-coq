Presentation
=======

This repo contains the formalisation work accompangy the paper *Definitional Functoriality for Dependent (Sub)Types*.

The formalisation follows a similar [Agda formalization]((https://github.com/mr-ohman/logrel-mltt/)) (described in [*Decidability of conversion for Type Theory in Type Theory*, 2018](https://dl.acm.org/doi/10.1145/3158111)). In order to avoid some work on the syntax, this project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate. It also includes code from Winterhalter's [partial-fun](https://github.com/TheoWinterhalter/coq-partialfun) library to handle the definition of partial functions.

Building
===========

The project builds with Coq version `8.16.1`. It needs the opam package `coq-smpl`. Once these have been installed, you can simply issue `make` in the root folder. Apart from a few harmless warnings, and the output of some examples, the build reports on the assumptions of our main theorems. The message `Closed under the global context` indicates that all of them are axiom-free.

For easiness, the html documentation built using `coqdoc` is included in the artefact. It can be built again invoking `make coqdoc`.

Browsing the Development
==================

The development, rendered using the [coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) utility, can be generated using `make coqdoc`, and then browed offline (as html files). To start navigating the sources, the best entry point is probably the [the table of content](./docs/coqdoc/toc.html). A [short description of the file contents](./docs/index.md) is also provided to make the navigation easier.

Files of interest
=================

Definitions
--------

The abstract syntax tree of terms is in [Ast], the declarative typing and conversion predicates are in [DeclarativeTyping], reduction is in [UntypedReduction], and algorithmic typing is in [AlgorithmicTyping].

The logical relation is defined with respect to a generic notion of typing, which is defined in [GenericTyping].

Proofs
----------

The logical relation is defined in [LogicalRelation]. It is first defined component by component, before the components are all brought together by inductive `LR` at the end of the file. The fundamental lemma of the logical relation, saying that every well-typed term is reducible, is in [Fundamental].

Injectivity and no-confusion of type constructor, and subject reduction, are proven in [TypeConstructorsInj]. `typing_SN`, in [Normalisation], shows that reduction on well-typed terms is (strongly) normalizing; this is phrased in a constructively acceptable way, as accessibility of every well-typed term under reduction, i.e. as well-foundation of the reduction relation.

`algo_typing_sound` in [BundledAlgorithmicTyping] says that algorithmic typing (assuming its inputs are well-formed), is sound with respect to declarative typing, and `algo_typing_complete` in [AlgorithmicTypingProperties] says that it is complete.

Finally, `check_full` in file [Decidability], says that typing is decidable.

Example from the paper
---------------

We have formalized a variant of example 1.1 (since we do not have booleans or records in the formalisation, the first have been replaced by natural numbers, and the second by iterated Σ-type) in [Example_1_1].

Rather than building the derivation of conversion by hand, we use our certified checker. So this also serves as a demonstration that our functions are effectively executable.

[Ast]: ./theories/AutoSubst/Ast.v
[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[UntypedReduction]: ./theories/UntypedReduction.v
[AlgorithmicTyping]: ./theories/AlgorithmicTyping.v
[GenericTyping]: ./theories/GenericTyping.v
[LogicalRelation]: ./theories/LogicalRelation.v
[Fundamental]: ./theories/Fundamental.v
[TypeConstructorsInj]: ./theories/TypeConstructorsInj.v
[Normalisation]: ./theories/Normalisation.v
[BundledAlgorithmicTyping]: ./theories/BundledAlgorithmicTyping.v
[AlgorithmicTypingProperties]: ./theories/AlgorithmicTypingProperties.v
[Decidability]: ./theories/Decidability.v
[Example_1_1]: ./theories/Example_1_1.v