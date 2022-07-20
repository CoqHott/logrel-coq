From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping Untyped.

Definition WFterm {Γ} {t A} :
    [ Γ |- t ::: A ] -> 
    [ |- Γ ].
    intros.
    induction X; try assumption.
    inversion IHX. assumption.
Defined.


Definition WFtype {Γ} {A} :
    [ Γ |- A ] -> 
    [ |- Γ ].
    intros.
    induction X; try assumption.
    exact (WFterm w).
Defined.

Definition WFEqTerm {Γ} {t u A} :
    [ Γ |- t ≅ u ::: A ] -> 
    [ |- Γ ].
    intros.
    induction X; try assumption.
    exact (WFterm w).
    exact (WFterm w1).
    exact (WFterm w0).
Defined.

Definition WFEqType {Γ} {A B} :
    [ Γ |- A ≅ B ] -> 
    [ |- Γ ].
    intros.
    induction X; try assumption.
    destruct w; try eassumption.
    exact (WFtype w1).
    exact (WFterm w).
    exact (WFEqTerm c).
Defined.

Definition redFirstTerm {Γ t u A} : 
  [ Γ |- t ⇒ u ::: A] ->
  [ Γ |- t ::: A ].
  intros.
  induction X.
  exact (wfTermConv IHX c).
  eapply wfTermApp; eassumption.
  eapply wfTermApp; try eassumption.
  eapply wfTermLam; eassumption.
Defined.

Definition redFirst {Γ A B} : 
  [ Γ |- A ⇒ B ] ->
  [ Γ |- A ].
  intro.
  destruct X.
  constructor.
  exact (redFirstTerm t).
Defined.

Definition redFirstCTerm {Γ t u A} : 
  [ Γ |- t ⇒* u ::: A] ->
  [ Γ |- t ::: A ].
  intros.
  destruct X.
  assumption.
  exact (redFirstTerm t0).
Defined.
    
Definition redFirstC {Γ A B} : 
  [ Γ |- A ⇒* B ] ->
  [ Γ |- A ].
  intro.
  destruct X.
  assumption.
  exact (redFirst t).
Defined.

Definition redFirstCWFTerm {Γ t u A} : 
  [ Γ |- t :⇒*: u ::: A] ->
  [ Γ |- t ::: A ].
  intros.
  destruct X.
  exact (redFirstCTerm C).
Defined.
    
Definition redFirstCWF {Γ A B} : 
  [ Γ |- A :⇒*: B ] ->
  [ Γ |- A ].
  intro.
  destruct X.
  exact (redFirstC D).
Defined.


