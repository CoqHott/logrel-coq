From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping DeclarativeTyping Generation.

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

Lemma InfRedTy {Γ A t} :
  [Γ |- t ▹h A] ->
  [Γ |- t : A].
Proof.
  intros [].
  econstructor ; tea.
  now apply RedConvTyC.
Qed.

(** Whnf do not reduce *)

Lemma whne_nored Γ n u A :
  whne Γ n -> [Γ |- n ⇒ u : A] -> False.
Proof.
  intros ne red.
  induction red in ne |- * ; fold_decl.
  - inversion ne ; subst ; clear ne.
    eapply neLambda.
    eassumption.
  - inversion ne ; subst.
    1: easy.
  - easy.
Qed.

Lemma whnf_nored Γ n u A :
  whnf Γ n -> [Γ |- n ⇒ u : A] -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  - inversion nf ; subst.
    inversion H ; subst.
    eapply neLambda.
    eassumption.
  - inversion nf ; subst.
    inversion H ; subst.
    eapply IHred.
    now constructor.
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
[|- Δ ] -> [Γ |- t ⇒ u : A] -> [Δ |- t⟨ρ⟩ ⇒ u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros ? red.
  induction red as [? ? ? ? ? ? Ht Ha | |]; fold_decl.
  - cbn in *.
    eapply redtm_meta_conv.
    1: econstructor ; fold_decl.
    1,3: now eapply typing_wk.
    + unshelve eapply typing_wk in Ht.
      3: econstructor ; now eapply well_up.
      1: shelve.
      2: now econstructor ; [eassumption | eapply typing_wk].
      cbn in *.
      now replace (ren_term _ t) with (t⟨wk_up ρ⟩)
        by (cbn ; now asimpl).
    + unfold ren1, RenWlWk_term.
      cbn.
      now asimpl.
    + now asimpl. 
  - cbn in *.
    eapply redtm_meta_conv.
    1: econstructor ; fold_decl.
    + now eauto.
    + now eapply typing_wk.
    + now asimpl.
    + reflexivity.
  - econstructor.
    1: eassumption.
    now eapply typing_wk.
Qed.

Lemma redty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
[|- Δ ] -> [Γ |- A ⇒ B] -> [Δ |- A⟨ρ⟩ ⇒ B⟨ρ⟩].
Proof.
  intros ? red.
  destruct red.
  constructor.
  fold_decl.
  change U with (U⟨ρ⟩).
  now apply redtm_wk.
Qed.

Module DeclarativeTypingProperties.
  Import DeclarativeTypingData.

  #[export, refine] Instance WfTypeDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: intros.
    - now eapply WFtype.
    - now eapply WFterm.
    - now eapply WFterm. 
    - now eapply WFEqType.
    - now eapply WFEqTerm.
    - now eapply WFEqType, RedConvTy.
    - now eapply WFEqTerm, RedConvTe. 
  Qed.

  #[export, refine] Instance WfTypeProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    2-4: now econstructor.
    intros.
    now eapply typing_wk.
  Qed.

  #[export, refine] Instance InferringDeclProperties : InferringProperties (ta := de) := {}.
  Proof.
    2-5: intros ;
    repeat match goal with
      | H : [_ |- _ ▹h _ ] |- _ => apply InfRedTy in H
    end ;
    now econstructor.
    - intros.
      now eapply typing_wk.
  Qed.  

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    - intros.
      now eapply typing_wk.
    - intros.
      now econstructor.
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
    - intros.
      now econstructor.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
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

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now eapply TermConv.
  - intros.
    now eapply typing_wk.
  - intros.
    eapply TermConv.
    2: now eapply TypeSym, RedConvTyC.
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros. eassumption.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split ; red ; intros.
    all: now econstructor.
  (* - intros.
    now eapply TermConv. *)
  - intros.
    now eapply typing_wk.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  Qed.
  
  #[export, refine] Instance OneRedTermDeclProperties : OneRedTermProperties (ta := de) := {}.
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

  #[export, refine] Instance OneRedTypeDeclProperties : OneRedTypeProperties (ta := de) := {}.
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

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.