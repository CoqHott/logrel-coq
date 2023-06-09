From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Transitivity Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.
  
  Lemma shiftPolyRed {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> PolyRed Γ l A B⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; now eapply wk.
    - intros; bsimpl; rewrite <- rinstInst'_term; now eapply wk.
    - now escape.
    - renToWk; eapply wft_wk; gen_typing.
    - intros; irrelevance0.
      2: replace (subst_term _ _) with B⟨ρ⟩.
      2: eapply wkEq, LRTyEqRefl_.
      all: bsimpl; now rewrite rinstInst'_term.
      Unshelve. all: tea.
  Qed.


  Lemma ArrRedTy0 {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> [Γ ||-Π<l> arr A B].
  Proof.
    intros RA RB; escape.
    unshelve econstructor; [exact A| exact B⟨↑⟩|..]; tea.
    - eapply redtywf_refl.
      now eapply wft_simple_arr.
    - eapply convty_simple_arr; tea.
      all: now unshelve eapply escapeEq, LRTyEqRefl_.
    - now eapply shiftPolyRed.
  Qed.

  Lemma ArrRedTy {Γ l A B} : [Γ ||-<l> A] -> [Γ ||-<l> B] -> [Γ ||-<l> arr A B].
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  (* Lemma idrefl {Γ l A} (RA : [Γ ||-<l> A]) :
    [Γ ||-<l> idterm A ≅ idterm A : arr A A | ArrRedTy RA RA].
  Proof.
    set (ΠAA := normRedΠ0 (invLRΠ (ArrRedTy RA RA))).
    enough [LRPi' ΠAA | Γ ||- idterm A ≅ idterm A : arr A A] by irrelevance.
    unshelve econstructor ; cbn. *)


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
      eapply redSubstTerm; tea.
      now eapply redtm_id_beta.
    }
    assert [Γ,, A |- A⟨↑⟩].
    {
      erewrite <- wk1_ren_on.
      eapply wft_wk ; tea.
      eapply wfc_cons ; gen_typing.
    }
    econstructor; cbn.
    - eapply redtmwf_refl.
      now eapply ty_id.
    - constructor.
    - eapply convtm_eta ; tea.
      + eapply ty_lam ; tea.
        now eapply ty_var0.
      + econstructor.
      + eapply ty_lam ; tea.
        now eapply ty_var0.
      + econstructor.
      + eapply convtm_exp ; cycle 1.
        * cbn.
          eapply redtm_beta ; tea.
          2: now eapply ty_var0.
          now eapply ty_var0.
        * cbn.
          eapply redtm_beta ; tea.
          2: now eapply ty_var0.
          now eapply ty_var0.
        * cbn.
          replace (A⟨↑⟩⟨↑⟩[_]) with (A⟨↑⟩) by (bsimpl ; now substify).
          unshelve eapply escapeEqTerm, LREqTermRefl_ ; tea.
          2: now eapply var0.
          erewrite <- wk1_ren_on.
          eapply wk ; tea.
          gen_typing.
        * replace (A⟨↑⟩⟨↑⟩[_]) with (A⟨↑⟩) by (bsimpl ; now substify).
          now eapply redty_refl.
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

  Lemma arr_wk {Γ Δ A B} {ρ : Δ ≤ Γ} : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
  Proof. cbn; now bsimpl. Qed.

  Lemma wkRedArr {Γ l A B f} 
    (RA : [Γ ||-<l> A]) 
    (RB : [Γ ||-<l> B]) 
    {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    [Γ ||-<l> f : arr A B | ArrRedTy RA RB] ->
    [Δ ||-<l> f⟨ρ⟩ : arr A⟨ρ⟩ B⟨ρ⟩ | ArrRedTy (wk ρ wfΔ RA) (wk ρ wfΔ RB)].
  Proof.
    intro; irrelevance0.
    2: unshelve eapply wkTerm; cycle 3; tea.
    symmetry; apply arr_wk.
  Qed.

  Lemma compred {Γ l A B C f g} 
    (RA : [Γ ||-<l> A]) 
    (RB : [Γ ||-<l> B]) 
    (RC : [Γ ||-<l> C]) :
    [Γ ||-<l> f : arr A B | ArrRedTy RA RB] ->
    [Γ ||-<l> g : arr B C | ArrRedTy RB RC] ->
    [Γ ||-<l> comp A g f : arr A C | ArrRedTy RA RC].
  Proof.
    intros Rf Rg.
    normRedΠin Rf; normRedΠin Rg; normRedΠ ΠAC. 
    assert (h : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp g⟨ρ⟩ (tApp f⟨ρ⟩ a) : _ | wk ρ wfΔ RC]).
    1:{
      intros; eapply simple_appTerm; [|eapply simple_appTerm; tea].
      1,2: eapply wkRedArr; irrelevance.
      Unshelve. 1: eapply wk. all: tea.
    }
    assert (heq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA
      (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]) (hb : [Δ ||-<l> b : A⟨ρ⟩ | RA])
      (ha : [Δ ||-<l> a ≅ b: A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp g⟨ρ⟩ (tApp f⟨ρ⟩ a) ≅ tApp g⟨ρ⟩ (tApp f⟨ρ⟩ b) : _ | wk ρ wfΔ RC]).
    1:{
      intros.
      eapply simple_appcongTerm; [| | |eapply simple_appcongTerm; tea].
      1,4: eapply LREqTermRefl_; eapply wkRedArr; irrelevance.
      1,2: eapply simple_appTerm; tea; eapply wkRedArr; irrelevance.
      Unshelve. 1: eapply wk. all: tea.
    }
    escape.
    assert (beta : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) RA (ha : [Δ ||-<l> a : A⟨ρ⟩ | RA]),
      [Δ ||-<l> tApp (comp A g f)⟨ρ⟩ a : _ | wk ρ wfΔ RC] ×
      [Δ ||-<l> tApp (comp A g f)⟨ρ⟩ a ≅ tApp g⟨ρ⟩ (tApp f⟨ρ⟩ a) : _ | wk ρ wfΔ RC]).
    1:{
      intros; cbn. 
      assert (eq : forall t : term, t⟨↑⟩⟨upRen_term_term ρ⟩ = t⟨ρ⟩⟨↑⟩) by (intros; now asimpl).
      do 2 rewrite eq.
      eapply redSubstTerm.
      + now eapply h.
      + eapply redtm_comp_beta.
        6: cbn in *; now escape.
        5: erewrite arr_wk; eapply ty_wk; tea.
        4: eapply typing_meta_conv.
        4: eapply ty_wk; tea.
        4: now rewrite <- arr_wk.
        1-3: now eapply wft_wk.
    }
    econstructor.
    - eapply redtmwf_refl.
      eapply ty_comp; cycle 2; tea.
    - constructor.
    - cbn. eapply convtm_comp; cycle 3; tea.
      erewrite <- wk1_ren_on.
      eapply escapeEqTerm.
      eapply LREqTermRefl_.
      do 2 erewrite <- wk1_ren_on.
      eapply h.
      eapply var0; now bsimpl.
      { now eapply wfc_ty. }
      Unshelve. 1: gen_typing.
      eapply wk; tea; gen_typing.
    - intros; cbn.
      irrelevance0.
      2: unshelve eapply beta; tea.
      bsimpl; now rewrite rinstInst'_term.
    - intros; irrelevance0; cycle 1.
      1: eapply transEqTerm;[|eapply transEqTerm].
      + unshelve eapply beta; tea.
      + unshelve eapply heq; tea.
      + eapply LRTmEqSym.
        unshelve eapply beta; tea.
      + cbn; bsimpl; now rewrite rinstInst'_term.
  Qed. 

End SimpleArrow.
