From Coq Require Import ssreflect.
From LogRel Require Import Utils.
From Coq Require Import CRelationClasses.

Inductive direction :=
| Fun
| Cofun
| Discr
.

Definition dir_op (d: direction) : direction :=
  match d with
  | Fun => Cofun
  | Cofun => Fun
  | Discr => Discr
  end.

Definition dir_leq (d1: direction) (d2: direction) : Type :=
  match d1, d2 with
  | Discr, _ => unit
  | Fun, Fun => unit
  | Fun, Discr => False
  | Cofun, Cofun => unit
  | Cofun, Discr => False
  | Fun, Cofun => False
  | Cofun, Fun => False
  end.


Notation "d1 ⪯ d2" := (dir_leq d1 d2) (at level 70).

Definition max_dir_opt d1 d2 : option direction :=
  match d1, d2 with
  | Discr, d => Some d
  | Fun, Cofun => None
  | Cofun, Fun => None
  | d1, d2 => Some d1
  end.

Definition max_dir d1 d2 d3 := max_dir_opt d1 d2 = Some d3.

Module MaxDirProp.
Section MaxDirProp.

  Lemma max_exists d1 d2 d : d1 ⪯ d -> d2 ⪯ d -> ∑ d', max_dir d1 d2 d'.
  Proof.
    destruct d, d1, d2; cbn; try easy.
    all: intros _ _; eexists; unfold max_dir; cbn; reflexivity.
  Qed.

  Lemma max_left d1 d2 : d1 ⪯ d2 -> max_dir d1 d2 d2.
  Proof.  destruct d1, d2; cbn; easy. Qed.

  Lemma max_right d1 d2 : d2 ⪯ d1 -> max_dir d1 d2 d1.
  Proof. destruct d1, d2; cbn; try easy; reflexivity. Qed.

  Context (d1 d2 d3 : direction) (e : max_dir_opt d1 d2 = Some d3).

  Lemma upper_bound1 : d1 ⪯ d3.
  Proof. 
    destruct d1, d2, d3; cbn in *; try easy.
    all: try injection e; discriminate.
  Qed.

  Lemma upper_bound2 : d2 ⪯ d3.
  Proof. 
    destruct d1, d2, d3; cbn in *; try easy.
    all: try injection e; discriminate.
  Qed.

  Lemma max_least d : d1 ⪯ d -> d2 ⪯ d -> d3 ⪯ d.
  Proof.
    destruct d, d1, d2, d3; try easy + discriminate.
  Qed.
  
End MaxDirProp.
End MaxDirProp.

Lemma dir_leq_trans d1 d2 d3 : dir_leq d1 d2 -> dir_leq d2 d3 -> dir_leq d1 d3.
Proof.  destruct d1,d2, d3; easy. Qed.

#[global]
Instance: Transitive dir_leq := dir_leq_trans.

Lemma dir_leq_refl d : dir_leq d d.
Proof. destruct d; easy. Qed.
#[global]
Instance: Reflexive dir_leq := dir_leq_refl.

Lemma dir_op_mon d1 d2 : d1 ⪯ d2 -> dir_op d1 ⪯ dir_op d2.
Proof. destruct d1, d2; easy. Qed.
