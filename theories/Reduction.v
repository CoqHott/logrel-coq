From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRenameConv PCUICSigmaCalculus PCUICInstConv.
From LogRel Require Import Notations Untyped Weakening GenericTyping DeclarativeTyping Properties Generation.

#[local] Open Scope untagged_scope.
Import DeclarativeTypingData.

(** Inclusion of the various reduction-like *)

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
    induction 1.
    1,3: now econstructor.
    econstructor ; eauto.
    now econstructor.
Qed.

Corollary termRedFrag Γ t u A : [Γ |- t ⇒ u : A] ->
fragment t && fragment u && fragment A && fragment_ctx Γ.
Proof.
  intros.
  apply wfFrag.
  now eapply RedConvTe.
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⇒* u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
  induction 1.
  1: now constructor.
  eapply TermTrans ; tea.
  now apply RedConvTe.
Qed.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
Proof.
  destruct 1.
  now (econstructor ; eapply RedConvTe ; eassumption).
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1.
  1: now econstructor.
  eapply TypeTrans ; tea.
  now apply RedConvTy.
Qed.

(** Whnf do not reduce *)

Lemma whne_nored Γ n u A :
  whne Γ n -> [Γ |- n ⇒ u : A] -> False.
Proof.
  intros ne red.
  induction red in ne |- * ; fold_decl.
  - inversion ne ; subst ; clear ne.
    1: now eapply neLambda.
    eapply mkApps_tApp_inj in H as [H ->] ; cbn in *.
    2: easy.
    symmetry in H.
    apply mkApps_nisApp in H as [].
    2: cbn.
    all: congruence.
  - inversion ne ; subst.
    1: easy.
    eapply mkApps_tApp_inj in H as [-> ->] ; cbn in *.
    2: easy.
    apply termRedFrag in red.
    rewrite fragment_mkApps in red ; cbn in red.
    now congruence.
  - easy.
Qed.

Lemma whnf_nored Γ n u A :
  whnf Γ n -> [Γ |- n ⇒ u : A] -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
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
    now econstructor.
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
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
    + reflexivity.
  - eapply termRedGen in red' as [? [d]].
    inversion d ; subst ; clear d.
    + f_equal.
      eauto.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
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


Lemma redtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
[|- Δ ] -> [Γ |- t ⇒ u : A] -> [Δ |- t.[ren ρ] ⇒ u.[ren ρ] : A.[ren ρ]].
Proof.
  intros ? red.
  induction red as [? ? ? ? ? ? Ht Ha | |]; fold_decl.
  - cbn in *.
    rewrite ! subst10_inst.
    eapply redtm_meta_conv.
    1: econstructor ; fold_decl.
    1,3: now eapply typing_wk.
    + unshelve eapply typing_wk in Ht.
      3: econstructor ; now eapply well_lift.
      1: shelve.
      2: now econstructor ; [eassumption | eapply typing_wk].
      cbn in *.
      now replace (t.[_]) with (t.[ren (wk_lift ρ)])
        by (cbn ; now rewrite ren_shiftn).
    + cbn.
      now rewrite <- up_Up, ren_shiftn.
    + now rewrite <- up_Up, ren_shiftn.
  - cbn in *.
    rewrite subst10_inst.
    econstructor ; fold_decl.
    2: now eapply typing_wk.
    eapply redtm_meta_conv ; try easy.
    f_equal.
    now rewrite up_Up.
  - econstructor.
    1: eassumption.
    now eapply typing_wk.
Qed.

Lemma redty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
[|- Δ ] -> [Γ |- A ⇒ B] -> [Δ |- A.[ren ρ] ⇒ B.[ren ρ]].
Proof.
  intros ? red.
  destruct red.
  constructor.
  fold_decl.
  change U with (U.[ren ρ]).
  now apply redtm_wk.
Qed.

Module DeclarativeConvProp.

  #[export, refine] Instance ConvTypeDeclProp : ConvTypeProp (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance ConvTermDeclProp : ConvTermProp (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - intros.
    eapply TermConv.
    2: now eapply TypeSym, RedConvTyC.
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - eauto.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProp : ConvNeuProp (ta := de) := {}.
  Proof.
  - split ; red ; intros.
    all: now econstructor.
  - intros.
    now eapply TermConv.
  - intros.
    now eapply typing_wk.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  Qed.
  
  #[export, refine] Instance OneRedTermDeclProp : OneRedTermProp (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtm_wk.
  - intros.
    eapply whnf_nored ; eassumption.
  - intros.
    now eapply red_det.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  Qed. 

  #[export, refine] Instance OneRedTypeDeclProp : OneRedTypeProp (ta := de) := {}.
  Proof.
  - intros.
    now eapply redty_wk.
  - intros.
    now eapply whnf_nored_ty.
  - intros.
    now eapply red_det_ty.
  - intros.
    now econstructor.
  Qed.

End DeclarativeConvProp.

Module DeclarativeTypingProp.
  Import DeclarativeTypingData DeclarativeTypingProp DeclarativeConvProp.

  #[export] Instance DeclarativeTypingProp : GenericTypingProp de _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProp.

Import DeclarativeTypingProp.