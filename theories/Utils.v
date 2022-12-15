From Coq Require Import Morphisms List CRelationClasses.
From MetaCoq Require Export MCPrelude MCProd.
From LogRel.AutoSubst Require Import core.

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").
Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
Infix "=1" := (pointwise_relation _ Logic.eq) (at level 70).
Notation "`=2`" := (pointwise_relation _ (pointwise_relation _ Logic.eq)) (at level 80).
Infix "=2" := (pointwise_relation _ (pointwise_relation _ Logic.eq)) (at level 70).
Infix "<~>" := iffT (at level 90).

(* The database used for generic typing *)
Create HintDb gen_typing.
#[global] Hint Constants Opaque : gen_typing.
#[global] Hint Variables Transparent : gen_typing.

Ltac gen_typing := typeclasses eauto 6 with gen_typing typeclass_instances.