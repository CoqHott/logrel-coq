
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Split Induction Irrelevance Escape Reflexivity Weakening Monotonicity Neutral Transitivity Reduction NormalRed.

Set Universe Polymorphism.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Section AppTerm.
  Context {wl Γ t u F G l l' l''}
    (hΠ : [Γ ||-Π<l> tProd F G]< wl >)
    {RF : [Γ ||-<l'> F]< wl >}
    (Rt : [Γ ||-<l> t : tProd F G | LRPi' (normRedΠ0 hΠ)]< wl >)
    (Ru : [Γ ||-<l'> u : F | RF]< wl >)
    (RGu : W[Γ ||-<l''> G[u..]]< wl >).

  Lemma app_id : W[Γ ||-<l''> tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    assert (wfΓ := wfc_wft (escape RF)).
    replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    unshelve econstructor.
    - eapply DTree_fusion.
      + unshelve eapply (PiRedTm.appTree Rt wk_id (wfLCon_le_id _)).
        2: eassumption.
        * exact u.
        * cbn in *.
          irrelevance0.
          2: eassumption.
          now bsimpl.
      + eapply (PolyRedPack.posTree (normRedΠ0 hΠ) wk_id (wfLCon_le_id _) wfΓ).
        irrelevance0.
        2: eassumption.
        cbn ; now bsimpl.
    - intros.
      irrelevance0.
      2: unshelve eapply (PiRedTm.app Rt wk_id (wfLCon_le_id _) wfΓ).
      cbn; now bsimpl.
      2: now eapply over_tree_fusion_r.
      now eapply over_tree_fusion_l.
  Qed.
  
  Lemma appTerm0 :
      W[Γ ||-<l''> tApp t u : G[u..] | RGu]< wl >
      × W[Γ ||-<l''> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    eapply WredSubstTerm.
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
  (RGu : W[Γ ||-<l> G[u..]]< wl >) : 
  W[Γ ||-<l> tApp t u : G[u..]| RGu]< wl >.
Proof.  
  unshelve eapply appTerm0.
  7:irrelevance.
  3: exact (invLRΠ RΠ).
  all: tea.
  irrelevance.
Qed.

Lemma WappTerm {wl Γ t u F G l}
  (hΠ : W[Γ ||-<l> tProd F G]< wl >)
  {RF : W[Γ ||-<l> F]< wl >}
  (Rt : W[Γ ||-<l> t : tProd F G | hΠ]< wl >)
  (Ru : W[Γ ||-<l> u : F | RF]< wl >)
  (RGu : W[Γ ||-<l> G[u..]]< wl >):
  W[Γ ||-<l> tApp t u : G[u..] | RGu]< wl >.
Proof.
  revert RGu.
  pattern wl.
  unshelve eapply split_to_over_tree.
  2:{ intros wl' n ne Ht RGu.
      unshelve eapply (TmSplit' (ne := ne)) ; intros m.
      1: eapply WLtrans ; [ | eassumption].
      1: eapply LCon_le_step ; now eapply wfLCon_le_id.
      + unshelve eapply Ht.
  } 
  - eapply DTree_fusion ; eapply DTree_fusion.
    + exact (WT _ hΠ).
    + exact (WT _ RF).
    + exact (WTTm _ Rt).
    + exact (WTTm _ Ru).
  - intros wl' Hover.
    unshelve eapply appTerm.
    2: eapply (WRed _ hΠ).
    + now eapply over_tree_fusion_l, over_tree_fusion_l.
    + eapply (WRed _ RF).
      now eapply over_tree_fusion_r, over_tree_fusion_l.
    + eapply (WRedTm _ Rt).
      now eapply over_tree_fusion_l, over_tree_fusion_r.
    + eapply (WRedTm _ Ru).
      now eapply over_tree_fusion_r, over_tree_fusion_r.
Qed.

Lemma appTerm' {wl Γ t u F G l X}
  (hΠ : [Γ ||-<l> tProd F G]< wl >)
  {RF : [Γ ||-<l> F]< wl >}
  (Rt : [Γ ||-<l> t : tProd F G | hΠ]< wl >)
  (Ru : [Γ ||-<l> u : F | RF]< wl >)
  (eq : X = G[u..])
  (RX : W[Γ ||-<l> X]< wl >) :
  W[Γ ||-<l> tApp t u : X | RX]< wl >.
Proof.
  eapply WLRTmRedIrrelevant' ; [symmetry; tea|].
  unshelve eapply appTerm; cycle 1; tea.
  Unshelve. now rewrite <- eq.
Qed.


Lemma WappTerm' {wl Γ t u F G l X}
  (hΠ : W[Γ ||-<l> tProd F G]< wl >)
  {RF : W[Γ ||-<l> F]< wl >}
  (Rt : W[Γ ||-<l> t : tProd F G | hΠ]< wl >)
  (Ru : W[Γ ||-<l> u : F | RF]< wl >)
  (eq : X = G[u..])
  (RX : W[Γ ||-<l> X]< wl >) :
  W[Γ ||-<l> tApp t u : X | RX]< wl >.
Proof.
  eapply WLRTmRedIrrelevant' ; [symmetry; tea|].
  unshelve eapply WappTerm; cycle 1; tea.
  Unshelve. now rewrite <- eq.
Qed.

  
Lemma appcongTerm {wl Γ t t' u u' F G l l'}
  (RΠ : [Γ ||-<l> tProd F G]< wl >) 
  {RF : [Γ ||-<l'> F]< wl >}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ]< wl >)
  (Ru : [Γ ||-<l'> u : F | RF]< wl >)
  (Ru' : [Γ ||-<l'> u' : F | RF]< wl >)
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]< wl >)
  (RGu : W[Γ ||-<l'> G[u..]]< wl >)
   :
   W[Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu]< wl >.
Proof.
  set (hΠ := invLRΠ RΠ); pose (RΠ' := LRPi' (normRedΠ0 hΠ)).
  assert [Γ ||-<l> t ≅ t' : tProd F G | RΠ']< wl > as [Rt Rt' ?? eqApp] by irrelevance.
  set (h := invLRΠ _) in hΠ.
  epose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tProd); 
  symmetry in e; injection e; clear e; 
  destruct h as [?????? [?? domRed ? codRed codExtTree codExt]] ; clear RΠ Rtt'; 
  intros; cbn in *; subst. 
  assert (wfΓ : [|-Γ]< wl >) by gen_typing.
  assert [Γ ||-<l> u' : F⟨@wk_id Γ⟩ | domRed _ _ (@wk_id Γ) (idε _) wfΓ]< wl > by irrelevance.
  assert [Γ ||-<l> u : F⟨@wk_id Γ⟩ | domRed _ _ (@wk_id Γ) (idε _) wfΓ]< wl > by irrelevance.
  assert (RGu' : W[Γ ||-<l> G[u'..]]< wl >).
  1:{
    replace G[u'..] with G[u' .: @wk_id Γ >> tRel] by now bsimpl.
    exists (posTree _ _ u' (@wk_id Γ) (idε _) wfΓ X).
    intros wl' f.
    eapply (codRed _ u' _ (@wk_id Γ) (idε _)).
    eassumption.
  }
  assert (RGuu' : W[Γ ||-<l>  G [u'..] ≅ G[u..]  | RGu']< wl >).
  1:{
    replace G[u..] with G[u .: @wk_id Γ >> tRel] by now bsimpl.
    unshelve eapply WLRTyEqIrrelevant'.
    5:{ unshelve eexists ; [eapply DTree_fusion ; [eapply DTree_fusion | ] | ].
        + exact (posTree _ _ u' (@wk_id Γ) (idε _) wfΓ X).
        + exact (posTree _ _ u (@wk_id Γ) (idε _) wfΓ X0).
        + eapply (codExtTree Γ wl u' u wk_id ((idε) wl) wfΓ) ; eauto.
          now eapply LRTmEqSym; irrelevance.
        + intros.
          irrelevance0 ; [reflexivity | unshelve eapply codExt].
          9: eapply over_tree_fusion_r, over_tree_fusion_l ; eassumption.
          2: do 2 (eapply over_tree_fusion_l) ; eassumption.
          1: now eapply LRTmEqSym; irrelevance.
          eapply over_tree_fusion_r ; exact Hover'.
    }
    3: now bsimpl.
    2: now replace G[u' .: @wk_id Γ >> tRel] with G[u'..] by now bsimpl.
  }
  unshelve epose  proof (eqApp _ u _ (@wk_id Γ) (idε _) wfΓ _).  1: irrelevance.
  eapply WtransEqTerm; eapply WtransEqTerm.
  - unshelve eapply (snd (appTerm0 hΠ Rt Ru RGu)).
  - unshelve epose  proof (eqApp _ u _ (@wk_id Γ) (idε _) wfΓ _).  1: irrelevance.
    replace (PiRedTm.nf Rt) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    unshelve econstructor.
    2:intros wl' Hover Hover' ; irrelevance0 ; [ | unshelve eapply X2].
    2: now bsimpl.
    3: eapply over_tree_fusion_l ; exact Hover'. 
    eapply over_tree_fusion_r ; exact Hover'.
  - unshelve epose proof (Hyp := PiRedTm.eq Rt' (a:= u) (b:=u') (@wk_id Γ) (idε wl) wfΓ _ _).
    3: unshelve econstructor ; [ | intros wl' Hover Hover' ; irrelevance0].
    5: unshelve eapply Hyp.
    4: now bsimpl.
    1,2,5: irrelevance.
    2: do 2 (eapply over_tree_fusion_l) ; exact Hover'. 
    + eapply over_tree_fusion_r, over_tree_fusion_l ; exact Hover'.
    + eapply over_tree_fusion_l, over_tree_fusion_r ; exact Hover'.
    + do 2 (eapply over_tree_fusion_r) ; exact Hover'.
  - replace (_)⟨_⟩ with (PiRedTm.nf Rt') by now bsimpl.
    eapply WLRTmEqRedConv; tea.
    eapply WLRTmEqSym.
    eapply (snd (appTerm0 hΠ Rt' Ru' RGu')).
Qed.


Lemma WappcongTerm {wl Γ t t' u u' F G l l'}
  (RΠ : W[Γ ||-<l> tProd F G]< wl >) 
  {RF : W[Γ ||-<l'> F]< wl >}
  (Rtt' : W[Γ ||-<l> t ≅ t' : tProd F G | RΠ]< wl >)
  (Ru : W[Γ ||-<l'> u : F | RF]< wl >)
  (Ru' : W[Γ ||-<l'> u' : F | RF]< wl >)
  (Ruu' : W[Γ ||-<l'> u ≅ u' : F | RF ]< wl >)
  (RGu : W[Γ ||-<l'> G[u..]]< wl >)
   :
   W[Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu]< wl >.
Proof.
  revert RGu.
  pattern wl.
  unshelve eapply split_to_over_tree.
  - do 2 (eapply DTree_fusion) ; [eapply DTree_fusion | eapply DTree_fusion | ..].
    + exact (WT _ RΠ).
    + exact (WT _ RF).
    + exact (WTTmEq _ Rtt').
    + exact (WTTm _ Ru).
    + exact (WTTm _ Ru').
    + exact (WTTmEq _ Ruu').
  - intros wl' n ne Ht RGu.
    unshelve eapply TmEqSplit'.
    2: exact ne.
    1: intros m ;  eapply WLtrans ; [ | eassumption].
    1: eapply LCon_le_step ; now eapply wfLCon_le_id.
    + intros m ; now apply Ht.
  - intros wl' Hover RGu.
    unshelve eapply appcongTerm.
    3: unshelve eapply (WRed _ RΠ).
    + now do 3 (eapply over_tree_fusion_l).
    + eapply (WRed _ RF).
      now eapply over_tree_fusion_r ; do 2 (eapply over_tree_fusion_l).
    + eapply (WRedTmEq _ Rtt').
      now eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l.
    + eapply (WRedTm _ Ru).
      now eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l.
    + eapply (WRedTm _ Ru').
      now eapply over_tree_fusion_l, over_tree_fusion_r.
    + eapply (WRedTmEq _ Ruu').
      now eapply over_tree_fusion_r, over_tree_fusion_r.
Qed.
  

Lemma appcongTerm' {wl Γ t t' u u' F F' G l l' X}
  (RΠ : [Γ ||-<l> tProd F G]< wl >) 
  {RF : [Γ ||-<l'> F]< wl >}
  {RF' : [Γ ||-<l'> F']< wl >}
  (RFF' : [Γ ||-<l'> F ≅ F' | RF]< wl >)
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ]< wl >)
  (Ru : [Γ ||-<l'> u : F | RF]< wl >)
  (Ru' : [Γ ||-<l'> u' : F' | RF']< wl >)
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]< wl >)
  (RGu : W[Γ ||-<l'> X]< wl >)
   : X = G[u..] ->
    W[Γ ||-<l'> tApp t u ≅ tApp t' u' : X | RGu]< wl >.
Proof.
  intros eq.
  eapply WLRTmEqIrrelevant' ; [symmetry; apply eq|].
  eapply appcongTerm; tea.
  eapply LRTmRedConv; tea.
  now eapply LRTyEqSym.
  Unshelve. now rewrite <- eq.
Qed.

Lemma WappcongTerm' {wl Γ t t' u u' F F' G l l' X}
  (RΠ : W[Γ ||-<l> tProd F G]< wl >) 
  {RF : W[Γ ||-<l'> F]< wl >}
  {RF' : W[Γ ||-<l'> F']< wl >}
  (RFF' : W[Γ ||-<l'> F ≅ F' | RF]< wl >)
  (Rtt' : W[Γ ||-<l> t ≅ t' : tProd F G | RΠ]< wl >)
  (Ru : W[Γ ||-<l'> u : F | RF]< wl >)
  (Ru' : W[Γ ||-<l'> u' : F' | RF']< wl >)
  (Ruu' : W[Γ ||-<l'> u ≅ u' : F | RF ]< wl >)
  (RGu : W[Γ ||-<l'> X]< wl >)
   : X = G[u..] ->
    W[Γ ||-<l'> tApp t u ≅ tApp t' u' : X | RGu]< wl >.
Proof.
  intros eq.
  eapply WLRTmEqIrrelevant' ; [symmetry; apply eq|].
  eapply WappcongTerm; tea.
  eapply WLRTmRedConv ; tea.
  now eapply WLRTyEqSym.
  Unshelve. now rewrite <- eq.
Qed.

End Application.
