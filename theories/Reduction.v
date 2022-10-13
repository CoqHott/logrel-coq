From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping Properties.

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u ::: A] -> 
    [Γ |- t ≅ u ::: A].
Proof.
    induction 1 ; mltt.
Defined.

#[global] Hint Resolve RedConvTe : mltt.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⇒* u ::: A] -> 
    [Γ |- t ≅ u ::: A].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve RedConvTeC : mltt.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve RedConvTy : mltt.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve RedConvTyC : mltt.

Definition ClosureConv {Γ} {t u A B} :
    [Γ |- t ⇒* u ::: A] ->
    [Γ |- A ≅ B] ->
    [Γ |- t ⇒* u ::: B].
Proof.
  induction 1 ; mltt.
  all: econstructor ; mltt.
Defined.

#[global] Hint Resolve ClosureConv | 10 : mltt.

Definition TermRedWFConv {Γ} {t u A B} :
    [Γ |- t :⇒*: u ::: A] ->
    [Γ |- A ≅ B] ->
    [Γ |- t :⇒*: u ::: B].
Proof.
  intros [] ?.
  constructor ; mltt.
Defined. 

#[global] Hint Resolve TermRedWFConv | 10 : mltt.

Definition TypeRedWFConv {Γ} {A B} :
    [Γ |- A :⇒*: B] ->
    [Γ |- A ≅ B].
Proof.
  intros [] ; mltt.
Defined.

#[global] Hint Resolve TypeRedWFConv : mltt.

Definition RedConvTeWFC {Γ} {t u A} :
    [Γ |- t :⇒*: u ::: A] ->
    [Γ |- t ≅ u ::: A].
Proof.
  intros [] ; mltt.
Defined.

#[global] Hint Resolve RedConvTeWFC : mltt.

Ltac skip :=
    match goal with
        | |- _ => try intro
    end.

Ltac gen_conv :=
    match goal with
    | H : [ ?Γ |- ?A ⇒ ?B ] , _ : [ ?Γ |- ?A ≅ ?B]|- _ => skip
    | H : [ _ |- _ ⇒ _] |- _ => pose proof (RedConvTe H)
    | |- _ => skip
    end;match goal with
    | H : [ ?Γ |- ?A ⇒* ?B ] , _ : [ ?Γ |- ?A ≅ ?B]|- _ => skip
    | H : [ _ |- _ ⇒* _] |- _ => pose proof (RedConvTeC H)
    | |- _ => skip
    end;match goal with
    | H : [ ?Γ |- ?t ⇒ ?u ::: ?A ] , _ : [ ?Γ |- ?t ≅ ?u ::: ?A]|- _ => skip
    | H : [ _ |- _ ⇒ _ ::: _] |- _ => pose proof (RedConvTy H)
    | |- _ => skip
    end;match goal with
    | H : [ ?Γ |- ?t ⇒* ?u ::: ?A ] , _ : [ ?Γ |- ?t ≅ ?u ::: ?A]|- _ => skip
    | H : [ _ |- _ ⇒* _ ::: _] |- _ => pose proof (RedConvTy H)
    | |- _ => skip
    end;match goal with
    | H : [ ?Γ |- ?A :⇒*: ?B ] , _ : [ ?Γ |- ?A ≅ ?B]|- _ => skip
    | H : [ _ |- _ :⇒*: _ ] |- _ => pose proof (TypeRedWFConv H)
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ ⇒* _ ::: ?A] , H2 : [_ |- ?A ≅ _] |- _ => pose proof (ClosureConv H1 H2)
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ :⇒*: _ ::: ?A] , H2 : [_ |- ?A ≅ _] |- _ => pose proof (TermRedWFConv H1 H2)
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ ⇒* _ ::: ?A] , H2 : [_ |- _ ≅ ?A] |- _ => pose proof (ClosureConv H1 (TypeSym H2))
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ :⇒*: _ ::: ?A] , H2 : [ _ |- _ ≅ ?A ] |- _ => pose proof (TermRedWFConv H1 (TypeSym H2))  
    | |- _ => skip   
    end.
