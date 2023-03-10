From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context UntypedReduction.

Inductive snf (r : term) : Type :=
  | snf_tSort {s} : [ r ⇒* tSort s ] -> snf r
  | snf_tProd {na A B} : [ r ⇒* tProd na A B ] -> snf A -> snf B -> snf r
  | snf_tLambda {na A t} : [ r ⇒* tLambda na A t ] -> snf A -> snf t -> snf r
  | snf_sne {n} : [ r ⇒* n ] -> sne n -> snf r
with sne (r : term) : Type :=
  | sne_tRel {v} : r = tRel v -> sne r
  | sne_tApp {n t} : r = tApp n t -> sne n -> snf t -> sne r.
