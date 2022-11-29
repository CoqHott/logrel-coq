From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import Notations Untyped GenericTyping DeclarativeTyping.

#[local] Open Scope untagged_scope.
Import DeclarativeTypingData.

Definition concons_inv {Γ na A} : [|- Γ,, vass na A] -> [|- Γ].
Proof.
  now inversion 1.
Qed.

Definition concons_inv' {Γ na A} : [|- Γ,, vass na A] -> [Γ |- A].
Proof.
  now inversion 1.
Qed.

Definition WFterm {Γ} {t A} :
    [ Γ |- t : A ] -> 
    [ |- Γ ].
Proof.
  induction 1 ; tea.
  now eapply concons_inv.
Qed.

Definition WFtype {Γ} {A} :
    [ Γ |- A ] -> 
    [ |- Γ ].
Proof.
    induction 1; tea.
    now eapply WFterm.
Qed.


Definition WFEqTerm {Γ} {t u A} :
    [ Γ |- t ≅ u : A ] -> 
    [ |- Γ ].
Proof.
    induction 1 ; eauto.
    all: eapply WFterm ; eassumption.
Qed.

Definition WFEqType {Γ} {A B} :
    [ Γ |- A ≅ B ] -> 
    [ |- Γ ].
Proof.
  induction 1 ; eauto.
  1: now eapply WFtype.
  now eapply WFEqTerm.
Qed.

Definition redFirstTerm {Γ t u A} : 
  [ Γ |- t ⇒ u : A] ->
  [ Γ |- t : A ].
Proof.
  induction 1.
  all: econstructor ; eauto.
  now econstructor.
Qed.

Definition redFirst {Γ A B} : 
  [ Γ |- A ⇒ B ] ->
  [ Γ |- A ].
Proof.
  destruct 1.
  econstructor.
  now eapply redFirstTerm.
Qed.

Definition redFirstCTerm {Γ t u A} : 
  [ Γ |- t ⇒* u : A] ->
  [ Γ |- t : A ].
Proof.
  induction 1 ; eauto using redFirstTerm.
Qed.

Definition redFirstC {Γ A B} : 
  [ Γ |- A ⇒* B ] ->
  [ Γ |- A ].
Proof.
  induction 1 ; eauto using redFirst.
Qed.