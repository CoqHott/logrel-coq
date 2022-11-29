From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
From LogRel Require Import Automation Untyped DeclarativeTyping Generation Properties.

(** Inclusion of the various reduction-like *)

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
    induction 1 ; mltt.
Qed.

Corollary termRedFrag Γ t u A : [Γ |- t ⇒ u : A] ->
fragment t && fragment u && fragment A && fragment_ctx Γ.
Proof.
  intros.
  apply wfFrag.
  mltt.
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⇒* u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
  induction 1 ; mltt.
Qed.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1 ; mltt.
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1 ; mltt.
Qed.

Definition TypeRedWFConv {Γ} {A B} :
    [Γ |- A :⇒*: B] ->
    [Γ |- A ≅ B].
Proof.
  intros [] ; mltt.
Qed.

Definition RedConvTeWFC {Γ} {t u A} :
    [Γ |- t :⇒*: u : A] ->
    [Γ |- t ≅ u : A].
Proof.
  intros [] ; mltt.
Qed.

(** Whnf do not reduce *)

Lemma whne_nored Γ n u A :
  whne Γ n -> [Γ |- n ⇒ u : A] -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  - inversion ne ; subst.
    1: easy.
    eapply mkApps_tApp_inj in H as [-> ->] ; cbn in *.
    2: easy.
    apply termRedFrag in red.
    rewrite fragment_mkApps in red ; cbn in red.
    now congruence.
  - inversion ne ; subst ; clear ne.
    1: now eapply neLambda.
    eapply mkApps_tApp_inj in H as [H ->] ; cbn in *.
    2: easy.
    symmetry in H.
    apply mkApps_nisApp in H as [].
    2: cbn.
    all: congruence.
  - easy.
Qed.

Lemma whnf_nored Γ n u A :
  whnf Γ n -> [Γ |- n ⇒ u : A] -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  - inversion nf ; subst.
    2-5:
      match goal with
        | H : mkApps _ _ = tApp _ _ |- _ =>
          apply mkApps_tApp_inj in H as [-> ->]
      end ; [|easy] ;
      apply termRedFrag in red ;
      rewrite fragment_mkApps in red ; cbn in red ;
      now congruence.
    eapply whne_nored.
    1: eassumption.
    mltt.
  - inversion nf.
    2-5:
      match goal with
        | H : mkApps _ _ = tApp _ _ |- _ =>
          apply mkApps_tApp_inj in H as [He _]
      end ; [|easy] ;
      symmetry in He ;
      apply mkApps_nisApp in He as [] ; cbn ; congruence.
    inversion X ; subst.
    1: now eapply neLambda.
    match goal with
        | H : mkApps _ _ = tApp _ _ |- _ =>
          apply mkApps_tApp_inj in H as [He _]
    end ; [|easy] ;
    symmetry in He ;
    apply mkApps_nisApp in He as [] ; cbn ; congruence.
  - easy.
Qed.

Corollary whnf_nored_ty Γ A B : [Γ |- A ⇒ B] -> whnf Γ A -> False.
Proof.
  intros [].
  eauto using whnf_nored.
Qed.


(** Determinism of reduction *)

Lemma red_det {Γ t u v A B} :
  [Γ |- t ⇒ u : A] -> [Γ |- t ⇒ v : B] ->
  u = v.
Proof.
  intros red red'.
  induction red in v, B, red' |- *.
  - eapply termRedGen in red' as [? [d]].
    inversion d ; subst ; clear d.
    + f_equal.
      eauto.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
  - eapply termRedGen in red' as [? [d]].
    inversion d ; subst ; clear d.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
    + reflexivity.
  - easy.
Qed.

Lemma red_det_ty {Γ A B C} :
  [Γ |- A ⇒ B] -> [Γ |- A ⇒ C] ->
  B = C.
Proof.
  intros HB HB'.
  destruct HB, HB'.
  now eapply red_det.
Qed.