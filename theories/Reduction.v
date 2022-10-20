From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
From LogRel Require Import Automation Untyped MLTTTyping Generation Properties.

(** Inclusion of the various reduction-like *)

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
    induction 1 ; mltt.
Qed.

#[global] Hint Resolve RedConvTe : mltt.

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

#[global] Hint Resolve RedConvTeC : mltt.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve RedConvTy : mltt.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1 ; mltt.
Qed.

#[global] Hint Resolve RedConvTyC : mltt.

Definition TypeRedWFConv {Γ} {A B} :
    [Γ |- A :⇒*: B] ->
    [Γ |- A ≅ B].
Proof.
  intros [] ; mltt.
Qed.

#[global] Hint Resolve TypeRedWFConv : mltt.

Definition RedConvTeWFC {Γ} {t u A} :
    [Γ |- t :⇒*: u : A] ->
    [Γ |- t ≅ u : A].
Proof.
  intros [] ; mltt.
Qed.

#[global] Hint Resolve RedConvTeWFC : mltt.

(** Type conversion for multi-step reduction *)

Definition ClosureConv {Γ} {t u A B} :
    [Γ |- t ⇒* u : A] ->
    [Γ |- A ≅ B] ->
    [Γ |- t ⇒* u : B].
Proof.
  induction 1 ; mltt.
  all: econstructor ; mltt.
Qed.

#[global] Hint Resolve ClosureConv | 10 : mltt.

Definition TermRedWFConv {Γ} {t u A B} :
    [Γ |- t :⇒*: u : A] ->
    [Γ |- A ≅ B] ->
    [Γ |- t :⇒*: u : B].
Proof.
  intros [] ?.
  constructor ; mltt.
Qed. 

#[global] Hint Resolve TermRedWFConv | 10 : mltt.

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

Lemma whnf_cred Γ t u A : [Γ |- t ⇒* u : A] -> whnf Γ t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Corollary whnf_cred_ty Γ A B : [Γ |- A ⇒* B] -> whnf Γ A -> A = B.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  now eapply whnf_nored_ty.
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

Lemma nred_cred_det Γ t u u' A A' :
  [Γ |- t ↘ u : A] -> [Γ |- t ⇒* u' : A'] ->
  [Γ |- u' ↘ u : A].
Proof.
  intros [red whnf] red'.
  induction red in whnf, A', u', red' |- *.
  - constructor ; tea.
    eapply whnf_cred in red' as -> ; tea.
    now econstructor.
  - destruct red'.
    + econstructor.
      2: mltt.
      now econstructor.
    + epose proof (red_det t0 t1) as <-.
      eapply IHred ; tea. 
Qed.

Corollary nred_det Γ t u u' A A' :
  [Γ |- t ↘ u : A] -> [Γ |- t ↘ u' : A'] ->
  u = u'.
Proof.
  intros red []. eapply nred_cred_det in red as [] ; tea.
  symmetry.
  now eapply whnf_cred.
Qed.

Lemma nred_cred_det_ty Γ A B B' :
  [Γ |- A ↘ B] -> [Γ |- A ⇒* B'] ->
  [Γ |- B' ↘ B].
Proof.
  intros [red whnf] red'.
  induction red in whnf, B', red' |- *.
  - eapply whnf_cred_ty in red' as -> ; tea.
    mltt.
  - destruct red'.
    1: mltt.
    + now epose proof (red_det_ty t t0) as <-.
Qed.

Corollary nred_det_ty Γ A B B' :
  [Γ |- A ↘ B] -> [Γ |- A ↘ B'] ->
  B = B'.
Proof.
  intros red []. eapply nred_cred_det_ty in red as [] ; tea.
  symmetry.
  now eapply whnf_cred_ty.
Qed.

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
    | H : [ ?Γ |- ?t ⇒ ?u : ?A ] , _ : [ ?Γ |- ?t ≅ ?u : ?A]|- _ => skip
    | H : [ _ |- _ ⇒ _ : _] |- _ => pose proof (RedConvTy H)
    | |- _ => skip
    end;match goal with
    | H : [ ?Γ |- ?t ⇒* ?u : ?A ] , _ : [ ?Γ |- ?t ≅ ?u : ?A]|- _ => skip
    | H : [ _ |- _ ⇒* _ : _] |- _ => pose proof (RedConvTy H)
    | |- _ => skip
    end;match goal with
    | H : [ ?Γ |- ?A :⇒*: ?B ] , _ : [ ?Γ |- ?A ≅ ?B]|- _ => skip
    | H : [ _ |- _ :⇒*: _ ] |- _ => pose proof (TypeRedWFConv H)
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ ⇒* _ : ?A] , H2 : [_ |- ?A ≅ _] |- _ => pose proof (ClosureConv H1 H2)
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ :⇒*: _ : ?A] , H2 : [_ |- ?A ≅ _] |- _ => pose proof (TermRedWFConv H1 H2)
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ ⇒* _ : ?A] , H2 : [_ |- _ ≅ ?A] |- _ => pose proof (ClosureConv H1 (TypeSym H2))
    | |- _ => skip
    end;match goal with
    | H1 : [ _ |- _ :⇒*: _ : ?A] , H2 : [ _ |- _ ≅ ?A ] |- _ => pose proof (TermRedWFConv H1 (TypeSym H2))  
    | |- _ => skip   
    end.
