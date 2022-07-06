From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping.

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u ::: A] -> 
    [Γ |- t ≅ u ::: A].
    intro.
    induction X. 
    eapply TermConv; eassumption.
    eapply TermAppCong. eassumption.
    constructor. assumption.
    eapply TermBRed; assumption.
Defined.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⇒* u ::: A] -> 
    [Γ |- t ≅ u ::: A].
    intro.
    induction X.
    + constructor. assumption.
    + eapply TermTrans.
      exact (RedConvTe t0). 
      assumption.
Defined.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
    intro.
    destruct X.
    pose proof (RedConvTe t).
    exact (convUniv X).
Defined.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
    intro.
    induction X.
    exact (TypeRefl w).
    eapply TypeTrans.
    exact (RedConvTy t).
    assumption.
Defined.

Definition ClosureConv {Γ} {t u A B} :
    [Γ |- t ⇒* u ::: A] ->
    [Γ |- A ≅ B] ->
    [Γ |- t ⇒* u ::: B].
    intros.
    induction X.
    constructor.
    eapply wfTermConv; eassumption.
    eapply termRedSucc.
    eapply conv; eassumption.
    exact (IHX X0).
Defined.

Definition RedWFConv {Γ} {t u A B} :
    [Γ |- t :⇒*: u ::: A] ->
    [Γ |- A ≅ B] ->
    [Γ |- t :⇒*: u ::: B].
    intros.
    destruct X.
    constructor.
    1,2 : eapply wfTermConv; eassumption.
    exact (ClosureConv C X0).
Defined.

Ltac gen_conv goal :=
    match goal with
        | H : [ _ |- _ ⇒ _] |- _ => pose proof (RedConvTe H)
        | H : [ _ |- _ ⇒* _] |- _ => pose proof (RedConvTeC H)
        | H : [ _ |- _ ⇒ _ ::: _] |- _ => pose proof (RedConvTy H)
        | H : [ _ |- _ ⇒* _ ::: _] |- _ => pose proof (RedConvTy H)
        | H1 : [ _ |- _ ⇒* _ ::: ?A] , H2 : [_ |- ?A ≅ _] |- _ => pose proof (ClosureConv H1 H2)
        | H1 : [ _ |- _ :⇒*: _ ::: ?A] , H2 : [_ |- ?A ≅ _] |- _ => pose proof (RedWFConv H1 H2)
        | H1 : [ _ |- _ ⇒* _ ::: ?A] , H2 : [_ |- _ ≅ ?A] |- _ => pose proof (ClosureConv H1 (TypeSym H2))
        | H1 : [ _ |- _ :⇒*: _ ::: ?A] , H2 : [ _ |- _ ≅ ?A ] |- _ => pose proof (RedWFConv H1 (TypeSym H2))     
    end.

    




