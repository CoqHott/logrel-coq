From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
From LogRel Require Import MLTTTyping Untyped.

Create HintDb mltt.
#[global] Hint Constants Opaque : mltt.
#[global] Hint Variables Transparent : mltt.

Ltac mltt := eauto with mltt.

#[global] Hint Constructors wfType wfContext wfTerm convType convTerm : mltt.
#[global] Hint Constructors termRed typeRed : mltt.

(*Making the non syntax-directed hints more costly*)
#[global] Remove Hints wfTermConv TermConv termRedConv : mltt.
#[global] Hint Resolve wfTermConv TermConv termRedConv | 10 : mltt.

Definition concons_inv {Γ na A} : [|- Γ,, vass na A] -> [|- Γ].
Proof.
  now inversion 1.
Qed.

Definition concons_inv' {Γ na A} : [|- Γ,, vass na A] -> [Γ |- A].
Proof.
  now inversion 1.
Qed.

#[global] Hint Resolve concons_inv concons_inv': mltt.

Definition WFterm {Γ} {t A} :
    [ Γ |- t ::: A ] -> 
    [ |- Γ ].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve WFterm : mltt.

Definition WFtype {Γ} {A} :
    [ Γ |- A ] -> 
    [ |- Γ ].
Proof.
    induction 1; mltt.
Defined.

#[global] Hint Resolve WFtype : mltt.

Definition WFEqTerm {Γ} {t u A} :
    [ Γ |- t ≅ u ::: A ] -> 
    [ |- Γ ].
Proof.
    induction 1; mltt.
Defined.

#[global] Hint Resolve WFEqTerm : mltt.

Definition WFEqType {Γ} {A B} :
    [ Γ |- A ≅ B ] -> 
    [ |- Γ ].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve WFEqType : mltt.

Definition redFirstTerm {Γ t u A} : 
  [ Γ |- t ⇒ u ::: A] ->
  [ Γ |- t ::: A ].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve redFirstTerm : mltt.

Definition redFirst {Γ A B} : 
  [ Γ |- A ⇒ B ] ->
  [ Γ |- A ].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve redFirst : mltt.

Definition redFirstCTerm {Γ t u A} : 
  [ Γ |- t ⇒* u ::: A] ->
  [ Γ |- t ::: A ].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve redFirstCTerm : mltt.

Definition redFirstC {Γ A B} : 
  [ Γ |- A ⇒* B ] ->
  [ Γ |- A ].
Proof.
  induction 1 ; mltt.
Defined.

#[global] Hint Resolve redFirstC : mltt.

(*Removed the next two lemmas, as they are just projections…*)

(* Definition redFirstCWFTerm {Γ t u A} : 
  [ Γ |- t :⇒*: u ::: A] ->
  [ Γ |- t ::: A ].
Proof.
  now intros [].
Defined. *)

(* Definition redFirstCWF {Γ A B} : 
  [ Γ |- A :⇒*: B ] ->
  [ Γ |- A ].
Proof.
  now intros [].
Defined. *)


