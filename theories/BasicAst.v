From Coq Require Import String Bool.
From LogRel.AutoSubst Require Import core unscoped.

Record aname := { nNamed : string }.

Definition eq_binder_annot (a a' : aname) :=
  String.eqb a.(nNamed) a'.(nNamed).

Lemma eq_binder_annot_eq a a' : reflect (a = a') (eq_binder_annot a a').
Proof.
  destruct a as [a], a' as [a'] ; cbn.
  destruct (String.eqb_spec a a').
  all: constructor ; congruence.
Qed.

Inductive sort :=
  | set : sort.