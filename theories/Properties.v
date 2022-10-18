From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import Automation Untyped MLTTTyping.

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
Qed.

#[global] Hint Resolve WFterm : mltt.

Definition WFtype {Γ} {A} :
    [ Γ |- A ] -> 
    [ |- Γ ].
Proof.
    induction 1; mltt.
Qed.

#[global] Hint Resolve WFtype : mltt.

Definition WFEqTerm {Γ} {t u A} :
    [ Γ |- t ≅ u ::: A ] -> 
    [ |- Γ ].
Proof.
    induction 1; mltt.
Qed.

#[global] Hint Resolve WFEqTerm : mltt.

Definition WFEqType {Γ} {A B} :
    [ Γ |- A ≅ B ] -> 
    [ |- Γ ].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve WFEqType : mltt.

Definition redFirstTerm {Γ t u A} : 
  [ Γ |- t ⇒ u ::: A] ->
  [ Γ |- t ::: A ].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve redFirstTerm : mltt.

Definition redFirst {Γ A B} : 
  [ Γ |- A ⇒ B ] ->
  [ Γ |- A ].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve redFirst : mltt.

Definition redFirstCTerm {Γ t u A} : 
  [ Γ |- t ⇒* u ::: A] ->
  [ Γ |- t ::: A ].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve redFirstCTerm : mltt.

Definition redFirstC {Γ A B} : 
  [ Γ |- A ⇒* B ] ->
  [ Γ |- A ].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve redFirstC : mltt.

(*Removed the next two lemmas, as they are just projections…*)

(* Definition redFirstCWFTerm {Γ t u A} : 
  [ Γ |- t :⇒*: u ::: A] ->
  [ Γ |- t ::: A ].
Proof.
  now intros [].
Qed. *)

(* Definition redFirstCWF {Γ A B} : 
  [ Γ |- A :⇒*: B ] ->
  [ Γ |- A ].
Proof.
  now intros [].
Qed. *)


