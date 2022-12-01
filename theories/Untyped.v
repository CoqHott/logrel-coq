From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICNormal.

(* The database used for generic typing *)
Create HintDb gen_typing.
#[global] Hint Constants Opaque : gen_typing.
#[global] Hint Variables Transparent : gen_typing.

Ltac gen_typing := typeclasses eauto 6 with gen_typing typeclass_instances.

Definition U := (tSort Universe.type0).
Notation "'eta_expand' f" := (tApp (lift0 1 f) (tRel 0)) (at level 40, only parsing).

#[global] Hint Transparent U : gen_typing.

Notation whne := (whne RedFlags.default empty_global_env).
Notation whnf := (whnf RedFlags.default empty_global_env).
Definition emptyName : aname := 
  ltac:(repeat econstructor).

#[global] Hint Constructors PCUICNormal.whne PCUICNormal.whnf : gen_typing.

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

Lemma neU Γ : whne Γ U -> False.
Proof.
  intros H.
  inversion H.
  apply mkApps_nisApp in H0 as [? _].
  1: unfold U in H0.
  2: cbn.
  all: congruence.
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

#[global] Hint Resolve nePi neLambda : gen_typing.