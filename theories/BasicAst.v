From Coq Require Import String Bool.
From LogRel.AutoSubst Require Import core unscoped.

Record aname := { nNamed : string }.

Definition eq_binder_annot (a a' : aname) := True.

Inductive sort :=
  | set : sort.