From LogRel.AutoSubst Require Import unscoped Ast.
From LogRel Require Import Utils BasicAst Context.

Export UnscopedNotations.
#[global] Open Scope subst_scope.

Definition U := (tSort set).
Notation "'eta_expand' f" := (tApp f ⟨ ↑ ⟩ (tRel 0)) (at level 40, only parsing).

Inductive whnf (Γ : context) : term -> Type :=
  | whnf_tSort s : whnf Γ (tSort s)
  | whnf_tProd na A B : whnf Γ (tProd na A B)
  | whnf_tLambda na A t : whnf Γ (tLambda na A t)
  | whnf_whne n : whne Γ n -> whnf Γ n
with whne (Γ : context) : term -> Type :=
  | whne_tRel v : whne Γ (tRel v)
  | whne_tApp n t : whne Γ n -> whne Γ (tApp n t).

#[global] Hint Constructors whne whnf : gen_typing.

Inductive isType Γ : term -> Type :=
  | ProdType {na A B} : isType Γ (tProd na A B)
  | NeType {A}  : whne Γ A -> isType Γ A. 

Inductive isFun Γ : term -> Type :=
  | lamFun {na A t} : isFun Γ (tLambda na A t)
  | NeFun  {A}  : whne Γ A -> isFun Γ A.

Lemma isType_whnf Γ t : isType Γ t -> whnf Γ t.
Proof.
  induction 1; now constructor.
Qed.

Lemma isFun_whnf Γ t : isFun Γ t -> whnf Γ t.
Proof.
  induction 1 ; now constructor.
Qed.

Lemma neU Γ : whne Γ U -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi Γ na A B : whne Γ (tProd na A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda Γ na A t : whne Γ (tLambda na A t) -> False.
Proof.
  inversion 1.
Qed.

#[global] Hint Resolve neU nePi neLambda : gen_typing.