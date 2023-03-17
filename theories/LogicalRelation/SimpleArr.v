From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Transitivity Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.
  
  Lemma ArrRedTy0 {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> [Γ ||-Π<l> arr A B].
  Proof.
    intros RA RB; escape.
    unshelve econstructor; [exact anDummy|exact A| exact B⟨↑⟩|..]; tea.
    - intros; now eapply wk.
    - cbn; intros.
      bsimpl; rewrite <- rinstInst'_term.
      now eapply wk.
    - eapply redtywf_refl.
      now eapply wft_simple_arr.
    - renToWk; eapply wft_wk; gen_typing.
    - eapply convty_simple_arr; tea.
      all: now unshelve eapply escapeEq, LRTyEqRefl_.
    - intros; irrelevance0.
      2: replace (subst_term _ _) with B⟨ρ⟩.      
      2: eapply wkEq, LRTyEqRefl_.
      all: bsimpl; now rewrite rinstInst'_term.
      Unshelve. all: tea.
  Qed.

  Lemma ArrRedTy {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> [Γ ||-<l> arr A B].
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  Lemma idred {Γ l A} (RA : [Γ ||-<l> A]) :
    [Γ ||-<l> idterm A : arr A A | ArrRedTy RA RA].
  Proof.
    normRedΠ ΠAA.
    pose proof (LRTyEqRefl_ RA).
    escape.
    assert (h : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp (idterm A)⟨ρ⟩ a : A⟨ρ⟩| RA] ×
      [Δ ||-<l> tApp (idterm A)⟨ρ⟩ a ≅ a : A⟨ρ⟩| RA]
    ).
    1:{
      intros; cbn; escape.
      assert [Δ |- A⟨ρ⟩] by now eapply wft_wk.
      assert [Δ |- A⟨ρ⟩ ≅ A⟨ρ⟩] by now eapply convty_wk.
      refine (redSubstTermOneStep _ _ _ ha).
      2: now eapply osredtm_id_beta.
      eapply ty_simple_app; tea; now eapply ty_id.
    }
    econstructor; cbn.
    - eapply redtmwf_refl.
      now eapply ty_id.
    - constructor.
    - now eapply convtm_id.
    - intros; cbn; irrelevance0.
      2: now eapply h.
      bsimpl; now rewrite rinstInst'_term.
    - intros ; cbn; irrelevance0; cycle 1.
      1: eapply transEqTerm;[|eapply transEqTerm].
      + now eapply h.
      + eassumption.
      + eapply LRTmEqSym. now eapply h.
      + bsimpl; now rewrite rinstInst'_term.
  Qed.

  Section SimpleAppTerm.
    Context {Γ t u F G l}
      {RF : [Γ ||-<l> F]}
      (RG : [Γ ||-<l> G])
      (hΠ := normRedΠ0 (ArrRedTy0 RF RG))
      (Rt : [Γ ||-<l> t : arr F G | LRPi' hΠ])
      (Ru : [Γ ||-<l> u : F | RF]).

    Lemma simple_app_id : [Γ ||-<l> tApp (PiRedTm.nf Rt) u : G | RG ].
    Proof.
      irrelevance0.
      2: now eapply app_id.
      now bsimpl.
      Unshelve. 1: tea.
      now bsimpl.
    Qed.

    Lemma simple_appTerm0 :
        [Γ ||-<l> tApp t u : G | RG]
        × [Γ ||-<l> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G | RG].
    Proof.
      irrelevance0.
      2: now eapply appTerm0.
      now bsimpl.
      Unshelve. 1: tea.
      now bsimpl.
    Qed.

  End SimpleAppTerm.

  Lemma simple_appTerm {Γ t u F G l}
    {RF : [Γ ||-<l> F]}
    (RG : [Γ ||-<l> G]) 
    (RΠ : [Γ ||-<l> arr F G])
    (Rt : [Γ ||-<l> t : arr F G | RΠ])
    (Ru : [Γ ||-<l> u : F | RF]) :
    [Γ ||-<l> tApp t u : G| RG].
  Proof.  
    unshelve eapply simple_appTerm0.
    3: irrelevance.
    all: tea.
  Qed.


  Lemma simple_appcongTerm {Γ t t' u u' F G l}
    {RF : [Γ ||-<l> F]}
    (RG : [Γ ||-<l> G])
    (RΠ : [Γ ||-<l> arr F G]) 
    (Rtt' : [Γ ||-<l> t ≅ t' : _ | RΠ])
    (Ru : [Γ ||-<l> u : F | RF])
    (Ru' : [Γ ||-<l> u' : F | RF])
    (Ruu' : [Γ ||-<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    irrelevance0.
    2: eapply appcongTerm.
    2-5: tea.
    now bsimpl.
    Unshelve. tea.
    now bsimpl.
  Qed.

End SimpleArrow.