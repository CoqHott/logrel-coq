Presentation
=======

This repo contains the formalisation work accompangy the paper *Definitional Functoriality for Dependent (Sub)Types*.

The formalisation follows a similar [Agda formalization]((https://github.com/mr-ohman/logrel-mltt/)) (described in [*Decidability of conversion for Type Theory in Type Theory*, 2018](https://dl.acm.org/doi/10.1145/3158111)). In order to avoid some work on the syntax, this project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate. It also includes code from Winterhalter's [partial-fun](https://github.com/TheoWinterhalter/coq-partialfun) library to handle the definition of partial functions.

Building
===========

The project builds with Coq version `8.16.1`. It needs the opam package `coq-smpl`. Once these have been installed, you can simply issue `make` in the root folder. Apart from a few harmless warnings, the build should report on the assumptions of our main theorems:
- `typing_SN` in [Normalisation](./theories/Normalisation.v), states that reduction on well-typed terms is (strongly) normalizing; this is phrased in a constructively acceptable way, as accessibility of every well-typed term under reduction, i.e. as well-foundation of the reduction relation.
- `algo_typing_sound` in [BundledAlgorithmicTyping](./theories/BundledAlgorithmicTyping.v) says that algorithmic typing (assuming its inputs are well-formed), is sound with respect to declarative typing, and `algo_typing_complete` in [AlgorithmicTypingProperties](./theories/AlgorithmicTypingProperties.v) says that it is complete.
- `check_full` in file [Decidability](./theories/Decidability.v), says that typing is decidable.
The message `Closed under the global context` indicates that all of them are axiom-free.

Browsing the Development
==================

The development, rendered using the [coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) utility, can be generated using `make coqdoc`, and then browed offline (as html files). To start navigating the sources, the best entry point is probably the [the table of content](./docs/coqdoc/toc.html). A [short description of the file contents](./docs/index.md) is also provided to make the navigation easier.

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
