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
- https://github.com/TheoWinterhalter/coq-partialfun

Presentation
=======

This repo contains the formalisation work accompangy the paper *Martin-Löf à la Coq*.

The formalisation follows a similar [Agda formalization](https://github.com/mr-ohman/logrel-mltt/) (described in [*Decidability of conversion for Type Theory in Type Theory*, 2018](https://dl.acm.org/doi/10.1145/3158111)). In order to avoid some work on the syntax, this project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate.

Building
===========

The project builds on Coq version `8.16.1`, see the [opam](./opam) file for complete dependencies. Since they are not available as opam packages, [coq-partialfun](https://github.com/TheoWinterhalter/coq-partialfun) and [coqdocjs](https://github.com/coq-community/coqdocjs/) are simply included.

Once the dependencies have been installed, you can simply issue `make` in the root folder. The development should build within 10 minutes (around 3 minutes on a modern laptop).

Apart from a few harmless warnings, and the output of some examples, the build reports on the assumptions of our main theorems, using `Print Assumptions`. The message `Closed under the global context` indicates that all of them are axiom-free.

For simplicity, the html documentation built using `coqdoc` is included in the artefact. It can be built again by invoking `make coqdoc`.

Browsing the development
==================

The development, rendered using the [coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) utility, can be then browsed (as html files). To start navigating the sources, the best entry point is probably the [the table of content](./docs/coqdoc/toc.html). A [short description of the file contents](./docs/index.md) is also provided to make the navigation easier.

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

Execution examples
---------------

Some sample execution of our certified checker are given in [Execution].

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
[Execution]: ./theories/Decidability/Execution.v