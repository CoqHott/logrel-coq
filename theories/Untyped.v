From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICNormal.
From LogRel Require Import Automation.

Notation whne := (whne RedFlags.default empty_global_env).
Notation whnf := (whnf RedFlags.default empty_global_env).
Definition emptyName : aname := 
  ltac:(repeat econstructor).

#[global] Hint Constructors PCUICNormal.whne PCUICNormal.whnf : mltt.

Definition eta {A B} (f : A -> B) : f = fun x => f x := eq_refl.

Inductive isType Γ : term -> Type :=
  | ProdType {na A B} : isType Γ (tProd na A B)
  | NeType {A}  : whne Γ A -> isType Γ A. 

Inductive isFun Γ : term -> Type :=
  | lamFun {na A t} : isFun Γ (tLambda na A t)
  | NeFun  {A}  : whne Γ A -> isFun Γ A.

Lemma isType_whnf Γ t : isType Γ t -> whnf Γ t.
Proof.
  induction 1.
  all: now constructor.
Qed.

Lemma isFun_whnf Γ t : isFun Γ t -> whnf Γ t.
Proof.
  induction 1.
  all: now constructor.
Qed.

Lemma nePi Γ na A B : whne Γ (tProd na A B) -> False.
Proof.
  intros H.
  inversion H.
  apply mkApps_nisApp in H0 as [? _].
  2: cbn.
  all: congruence.
Qed.

Lemma neLambda Γ na A t : whne Γ (tLambda na A t) -> False.
Proof.
  intros H.
  inversion H.
  1: cbn in * ; congruence.
  apply mkApps_nisApp in H0 as [? _].
  2: cbn.
  all: congruence.
Qed.

#[global] Hint Resolve nePi neLambda : mltt.