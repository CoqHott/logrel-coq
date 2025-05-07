Presentation
=======

This branch contains the formalisation accompanying the paper *What does it take to certify a conversion checker?*, published at FSCD 2025.

Building
===========

If you already have an opam setup, dependencies can be installed by simply using `opam install . --deps-only`.
Otherwires, the branch builds with Coq version `8.20.0`, and opam packages `coq-smpl` and `coq-equations` see [opam file](./opam) for details.

Once the dependencies have been installed, you can issue `make` in the root folder to
build the whole development.

The `make depgraph` recipe can be used to generate the [dependency graph](https://coqhott.github.io/logrel-coq/dependency_graph.png), and the `make coqdoc` generates coqdoc documentation for offline browsing.

Syntax regeneration
====================

For simplicity, we include the syntax file (`Ast.v`) generated using [AutoSubst](https://github.com/uds-psl/autosubst-ocaml).

Correspondence with the paper
=====================================

Section 2
----------

[DeclarativeTyping] contains the definition of the specification, [NormalForms] that of
normal forms (Fig 2) and [UntypedReduction] that of reduction (Fig 3).

All properties defined in Section 2.2 are defined in [PropertiesDefinition]. The proofs
of Corollaries 2 and 3 are in [TypeInjectivityConsequences]. Neutral comparison is defined in
[DeclarativeTyping], and Proposition 8 is proven in [NeutralConvProperties]. Deep normalisation
is defined in [NormalisationDefinition].

Proofs of the properties that are direct consequences of the logical relation are gathered
in [LogRelConsequences]. A proof of full completeness of neutral comparison is obtained at 
the end of [UntypedTypedConv].

Section 3
----------------------

The definition of the algorithmic judgments (typed and untyped conversion and bidirectional typing) are given in
[AlgorithmicJudgments].
The definitions of the functions are in [Functions].
Figure 3 corresponds to the definition of "bundled" typing judgments, defined in 
[Bundled].

Section 4
-------------------

Proofs of section 4.1 and 4.2
are gathered in the [Checkers](./theories/Checkers/) subfolder.
Those of section 4.3 are in [UntypedConvSoundness] and [UntypedTypedConv].

[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[NormalForms]: ./theories/Syntax/NormalForms.v
[UntypedReduction]: ./theories/Syntax/UntypedReduction.v
[PropertiesDefinition]: ./theories/TypingProperties/PropertiesDefinition.v
[TypeInjectivityConsequences]: ./theories/TypingProperties/TypeInjectivityConsequences.v
[NeutralConvProperties]: ./theories/TypingProperties/NeutralConvProperties.v
[NormalisationDefinition]: ./theories/TypingProperties/NormalisationDefinition.v
[LogRelConsequences]: ./theories/TypingProperties/LogRelConsequences.v
[UntypedConvSoundness]: ./theories/Algorithmic/UntypedConvSoundness.v
[UntypedTypedConv]: ./theories/Algorithmic/UntypedTypedConv.v
[AlgorithmicJudgments]: ./theories/AlgorithmicJudgments.v
[Functions]: ./theories/Checkers/Functions.v
[Bundled]: ./theories/Algorithmic/Bundled.v

[autosubst-ocaml]: https://github.com/uds-psl/autosubst-ocaml
[Positivity.agda]: ./theories/Positivity.agda
