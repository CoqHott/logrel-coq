
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction NormalRed.

Set Universe Polymorphism.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Section AppTerm.
  Context {wl Γ t u F G l l' l''}
    (hΠ : [Γ ||-Π<l> tProd F G]< wl >)
    {RF : W[Γ ||-<l'> F]< wl >}
    (Rt : [Γ ||-<l> t : tProd F G | LRPi' (normRedΠ0 hΠ)]< wl >)
    (Ru : W[Γ ||-<l'> u : F | RF]< wl >)
    (RGu : W[Γ ||-<l''> G[u..]]< wl >).

  Definition AppTy : W[Γ ||-<l> G[u..]]< wl >.
  Proof.
    clear Rt RGu.
    destruct Ru ; destruct RF ; cbn in *.
    destruct hΠ ; cbn in *.
    exists (max WN WNTm).
    intros.
    assert ([Γ ||-< l > cod[u..] ]< wl' >).
    - pose (q := codRed Γ u wl' wk_id τ).
      cbn in q.
      replace (cod[u..]) with (cod[u .: _wk_id Γ >> tRel]) by now bsimpl.
      unshelve eapply q.
      
      eapply codRed.
    
    
  Lemma app_id : W[Γ ||-<l''> tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    exists (PiRedTyPack.domN  hΠ ).
    intros.
    replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance0.  2: unshelve eapply (PiRedTm.app Rt).
    cbn; now bsimpl.
    - exact wl'.
    - assumption.
    - assumption.
    - eapply wfc_Ltrans.
      2: exact (wfc_wft (escape RF)).
      assumption.
    - irrelevance0.
      2:{ unshelve eapply LRTm_Ltrans.
          exact l'.
          exact wl.
          all: try eassumption.}
      cbn.
      now bsimpl.
    - now eapply wfLCon_le_id.
    - cbn.
      unfold NormalRed.normRedΠ0_obligation_7.
      cbn.
         eassumption.
         eassumption.}
      Unshelve.
      cbn.
      now bsimpl.
    
    assert (wfΓ := wfc_wft (escape RF)).
    replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance0.  2: unshelve eapply (PiRedTm.app Rt).
    cbn; now bsimpl.
    Unshelve. 1: eassumption.
    cbn; irrelevance0; tea; now bsimpl.
  Qed.

  Lemma appTerm0 :
      [Γ ||-<l''> tApp t u : G[u..] | RGu]< wl >
      × [Γ ||-<l''> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    eapply redwfSubstTerm.
    1: unshelve eapply app_id; tea.
    escape.
    eapply redtmwf_app.
    1: apply Rt.
    easy.
  Qed.

End AppTerm.

Lemma appTerm {wl Γ t u F G l}
  (RΠ : [Γ ||-<l> tProd F G]< wl >)
  {RF : [Γ ||-<l> F]< wl >}
  (Rt : [Γ ||-<l> t : tProd F G | RΠ]< wl >)
  (Ru : [Γ ||-<l> u : F | RF]< wl >)
  (RGu : [Γ ||-<l> G[u..]]< wl >) : 
  [Γ ||-<l> tApp t u : G[u..]| RGu]< wl >.
Proof.  
  unshelve eapply appTerm0.
  7:irrelevance.
  3: exact (invLRΠ RΠ).
  all: tea.
  irrelevance.
Qed.


Lemma appcongTerm {wl Γ t t' u u' F G l l'}
  (RΠ : [Γ ||-<l> tProd F G]< wl >) 
  {RF : [Γ ||-<l'> F]< wl >}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ]< wl >)
  (Ru : [Γ ||-<l'> u : F | RF]< wl >)
  (Ru' : [Γ ||-<l'> u' : F | RF]< wl >)
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]< wl >)
  (RGu : [Γ ||-<l'> G[u..]]< wl >)
   :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu]< wl >.
Proof.
  set (hΠ := invLRΠ RΠ); pose (RΠ' := LRPi' (normRedΠ0 hΠ)).
  assert [Γ ||-<l> t ≅ t' : tProd F G | RΠ']< wl > as [Rt Rt' ? eqApp] by irrelevance.
  set (h := invLRΠ _) in hΠ.
  epose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tProd); 
  symmetry in e; injection e; clear e; 
  destruct h as [?????? domRed codRed codExt] ; clear RΠ Rtt'; 
  intros; cbn in *; subst. 
  assert (wfΓ : [|-Γ]< wl >) by gen_typing.
  assert [Γ ||-<l> u' : F⟨@wk_id Γ⟩ | domRed _ (@wk_id Γ) wfΓ]< wl > by irrelevance.
  assert [Γ ||-<l> u : F⟨@wk_id Γ⟩ | domRed _ (@wk_id Γ) wfΓ]< wl > by irrelevance.
  assert (RGu' : [Γ ||-<l> G[u'..]]< wl >).
  1:{
    replace G[u'..] with G[u' .: @wk_id Γ >> tRel] by now bsimpl.
    now eapply (codRed _ u' (@wk_id Γ)).
  }
  assert (RGuu' : [Γ ||-<l>  G [u'..] ≅ G[u..]  | RGu']< wl >).
  1:{
    replace G[u..] with G[u .: @wk_id Γ >> tRel] by now bsimpl.
    irrelevance0.
    2: unshelve eapply codExt.
    6: eapply LRTmEqSym; irrelevance.
    2-4: tea.
    now bsimpl.
  }
  eapply transEqTerm; eapply transEqTerm.
  - eapply (snd (appTerm0 hΠ Rt Ru RGu)).
  - unshelve epose  proof (eqApp _ u (@wk_id Γ) wfΓ _).  1: irrelevance. 
    replace (PiRedTm.nf Rt) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance.
  - unshelve epose proof (PiRedTm.eq Rt' (a:= u) (b:=u') (@wk_id Γ) wfΓ _ _ _).
    all: irrelevance.
  - replace (_)⟨_⟩ with (PiRedTm.nf Rt') by now bsimpl.
    eapply LRTmEqRedConv; tea.
    eapply LRTmEqSym.
    eapply (snd (appTerm0 hΠ Rt' Ru' RGu')).
Qed.

End Application.


