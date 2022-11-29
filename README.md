Presentation
=======

This repo contains formalisation work on implementing a logical relation over MLTT with one universe.
This formalisation follows the [work done by Abel et al.]((https://github.com/mr-ohman/logrel-mltt/)) (described in [Decidability of conversion for Type Theory in Type Theory, 2018](https://dl.acm.org/doi/10.1145/3158111)), and [Loïc Pujet's work](https://github.com/loic-p/logrel-mltt) on removing induction-recursion from the previous formalization, making it feasible to translate it from Agda to Coq.

The definition of the logical relation (**LR**) ressembles Loïc's in many ways, but also had to be modified for a few reasons :
- Because of universe constraints and the fact that functors cannot be indexed by terms in Coq whereas it is possible in Agda, the relevant structures had to be parametrized by a type level and a recursor, and the module system had to be dropped out entirely.
- Since Coq and Agda's positivity checking for inductive types is different, it turns out that **LR**'s definition, even though it does not use any induction-induction or induction-recursion in Agda, is not accepted in Coq. As such, the predicate over Π-types for **LR** has been modified compared to Agda. You can find a MWE of the difference in positivity checking in the two systems in [Positivity.v] and [Positivity.agda].

In order to avoid some work on the syntax, this project uses the AST of [MetaCoq](https://metacoq.github.io), as well as some of its definitions (eg. substitution). While the AST has many nodes which are absent in the current formalization of MLTT, since these are not typable most proofs never have to consider them. Basically, only the proofs without typing assumptions have to be done for the whole AST, but most of these are done in MetaCoq already.

Building
===========

The project depends on the MetaCoq 1.0 packages, available on opam. Once they have been installed, you can simply issue `make` in the root folder.


File description
==========

| File | Description |
|---|----|
[Notations]  | Notations used throughout the file. It can be used as an index for notations!
[Untyped] | Various useful definitions for defining the inference rules |
[Weakening] | Definition of a well-formed weakening, and some properties.
[Substitution] | Definition of a well-formed substitution.
[GenericTyping] | A generic notion of typing, used to define the logical relation, to be instantiated twice: once with the declarative version, and once with the algorithmic one.
[DeclarativeTyping] | Defines the theory's typing rules in a declarative fashion, the current definition has a single universe as well as product types and eta-conversion for functions. |
[Generation] | Contains generation theorems, giving a good inversion on term typing/reduction with a direct structural premise
[Properties] and [Reduction] | Contain basic theorem over the typing rules that are easily derivable by induction over the rules. |
[LogicalRelation] | Contains the logical relation's (**LR**) definition. |
| [LRInduction] | Defines the induction principles over **LR**. Because of universe constraints, **LR** needs two induction principles, one for each type levels. |
| [Escape] | Contains a proof of the escape lemma for **LR** |
| [Shapeview] | Technique to avoid considering non-diagonal cases for two reducibly convertible types. |
[Reflexivity] | Reflexivity of the logical relation.
[Irrelevance] | Irrelevance of the logical relation: two convertible types decode to equivalent predicates. Symmetry is a direct corollary. |
| [Positivity.v] and [Positivity.agda] | Showcase the difference between Coq and Agda's positivity checkers. |

[Notations]: ./theories/Notations.v
[Automation]: ./theories/Automation.v
[Untyped]: ./theories/Untyped.v
[GenericTyping]: ./theories/GenericTyping.v
[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[Properties]: ./theories/Properties.v
[Reduction]: ./theories/Reduction.v
[Generation]: ./theories/Generation.v
[LogicalRelation]: ./theories/LogicalRelation.v
[LRInduction]: ./theories/LRInduction.v
[Escape]: ./theories/Escape.v
[Reflexivity]: ./theories/Reflexivity.v
[Irrelevance]: ./theories/Irrelevance.v
[ShapeView]: ./theories/Shapeview.v
[Positivity.v]: ./theories/Positivity.v
[Positivity.agda]: ./theories/Positivity.agda
[Weakening]: ./theories/Weakening.v
[Substitution]: ./theories/Substitution.v