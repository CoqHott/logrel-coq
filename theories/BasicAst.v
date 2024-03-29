(** * LogRel.BasicAst: definitions preceding those of the AST of terms: sorts, binder annotations… *)
From Coq Require Import String Bool.
From LogRel.AutoSubst Require Import core unscoped.

Inductive sort : Set :=
  | set : sort.

Definition sort_of_product (s s' : sort) := set.