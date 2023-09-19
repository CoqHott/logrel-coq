From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.


Section LambdaValid.
Context `{GenericTypingProperties}.





Context {Γ F G l} {VΓ : [||-v Γ]} (VF : [Γ ||-v<l> F | VΓ]) 
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma consWkEq {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma lamBetaRed {t} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]) 
  {Δ σ} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) 
  {Δ0 a} (ρ : Δ0 ≤ Δ) (wfΔ0 : [|-Δ0])
  (RFσ : [Δ0 ||-<l> F[σ]⟨ρ⟩]) 
  (ha : [RFσ | _ ||- a : _])
  (RGσ : [Δ0 ||-<l> G[up_term_term σ][a .: ρ >> tRel]]) :
    [_ ||-<l> tApp (tLambda F t)[σ]⟨ρ⟩ a : _ | RGσ] × 
    [_ ||-<l> tApp (tLambda F t)[σ]⟨ρ⟩ a ≅ t[a .: σ⟨ρ⟩] : _ | RGσ].
Proof.
  pose proof (Vσa := consWkSubstS VF ρ wfΔ0 Vσ ha); instValid Vσa.
  pose proof (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ. instValid VσUp.  escape.
  irrelevance0. 1: now rewrite consWkEq'.
  eapply redwfSubstTerm; tea.
  constructor; tea.
  do 2 rewrite <- consWkEq.
  eapply redtm_beta; tea.
  fold subst_term; renToWk;  eapply ty_wk; tea.
  eapply wfc_cons; tea; eapply wft_wk; tea.
Qed.

Lemma betaValid {t a} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]) 
  (Va : [Γ ||-v<l> a : F | VΓ | VF]) :
  [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G[a..] | VΓ | substS VG Va].
Proof.
  constructor; intros. instValid Vσ.
  pose (Vσa := consSubstS _ _ Vσ _ RVa). instValid Vσa.
  pose proof (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ. instValid VσUp.  escape.
  assert (eq : forall t, t[a..][σ] = t[up_term_term σ][a[σ]..]) by (intros; now bsimpl).
  assert (eq' : forall t, t[a..][σ] = t[a[σ].: σ]) by (intros; now bsimpl).
  irrelevance0. 1: symmetry; apply eq.
  rewrite eq;  eapply redwfSubstTerm; tea.
  1: rewrite <- eq; rewrite eq'; irrelevance.
  constructor; tea.
  * do 2 (rewrite <- eq; rewrite eq'); tea.
  * eapply redtm_beta; tea.
    Unshelve. 2:rewrite <- eq; now rewrite eq'.
Qed.

Lemma lamValid0 {t} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG]) 
  {Δ σ} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) :
  [validTy VΠFG wfΔ Vσ | Δ ||- (tLambda F t)[σ] : (tProd F G)[σ]].
Proof.
  pose proof (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ. instValid VσUp. escape.
  pose (RΠ := normRedΠ RVΠFG); refold.
  enough [RΠ | Δ ||- (tLambda F t)[σ] : (tProd F G)[σ]] by irrelevance.
  assert [Δ |- (tLambda F t)[σ] : (tProd F G)[σ]] by (escape; cbn; gen_typing).
  exists (tLambda F t)[σ]; intros; cbn in *.
  + now eapply redtmwf_refl.
  + constructor;  unshelve eapply escapeEq, reflLRTyEq; [|tea].
  + eapply convtm_eta; tea.
    1,2: constructor; unshelve eapply escapeEq, reflLRTyEq; [|tea].
    assert (eqσ : forall Z, Z[up_term_term σ] = Z[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0) ..])
    by (intro; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
    assert [Δ,, F[σ] |-[ ta ] tApp (tLambda F[σ] t[up_term_term σ])⟨S⟩ (tRel 0) ⤳*  t[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0)..] : G[up_term_term σ]].
    {
      rewrite (eqσ G). eapply redtm_beta.
      * renToWk; eapply wft_wk; tea; gen_typing.
      * renToWk; eapply ty_wk; tea.
        eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
      * fold ren_term; refine (ty_var _ (in_here _ _)); gen_typing.
    }
    eapply convtm_exp; tea.
    - rewrite <- eqσ; tea.
    - rewrite <- eqσ; tea.
    - unshelve eapply escapeEq, reflLRTyEq; [|tea].
    - rewrite <- (eqσ t); eapply escapeEqTerm; now eapply reflLRTmEq.
  + eapply lamBetaRed; tea. 
  + pose proof (Vσa := consWkSubstS VF ρ h Vσ ha).
    pose proof (Vσb := consWkSubstS VF ρ h Vσ hb).
    assert (Vσab : [_ ||-v _ ≅ (b .: σ⟨ρ⟩) : _ | _ | _ | Vσa]).
    1:{
      unshelve eapply consSubstSEq'.
      2: irrelevance.
      eapply irrelevanceSubstEq.
      eapply wkSubstSEq ; eapply reflSubst.
      Unshelve. all: tea.
    }
    eapply LREqTermHelper.
    1,2: eapply lamBetaRed; tea.
    - irrelevance0; rewrite consWkEq';[reflexivity|].
      unshelve eapply validTyExt; cycle 3; tea.
      Unshelve. rewrite consWkEq'; eapply validTy; tea.
    - epose proof (validTmExt Vt _ _ Vσb Vσab).
      irrelevance. now rewrite consWkEq'.
Qed.

Lemma lamValid {t} (Vt : [Γ ,, F ||-v<l> t : G | VΓF | VG])
   :
    [Γ ||-v<l> tLambda F t : tProd F G | VΓ | VΠFG ].
Proof.
  opector. 1: now apply lamValid0.
  intros.
  pose (VσUp :=  liftSubstS' VF Vσ).
  pose proof (VσUp' :=  liftSubstS' VF Vσ').
  pose proof (VσUprea :=  liftSubstSrealign' VF Vσσ' Vσ').
  pose proof (VσσUp := liftSubstSEq' VF Vσσ').
  instAllValid Vσ Vσ' Vσσ';  instValid VσUp'; instAllValid VσUp VσUprea VσσUp.
  pose (RΠ := normRedΠ RVΠFG); refold.
  enough [RΠ | Δ ||- (tLambda F t)[σ] ≅ (tLambda F t)[σ'] : (tProd F G)[σ]] by irrelevance.
  unshelve econstructor.
  - change [RΠ | Δ ||- (tLambda F t)[σ] : (tProd F G)[σ]].
    eapply normLambda.
    epose (lamValid0 Vt wfΔ Vσ).
    irrelevance.
  - change [RΠ | Δ ||- (tLambda F t)[σ'] : (tProd F G)[σ]].
    eapply normLambda.
    eapply LRTmRedConv.
    2: epose (lamValid0 Vt wfΔ Vσ'); irrelevance.
    eapply LRTyEqSym. eapply (validTyExt VΠFG); tea.
    Unshelve. 2: now eapply validTy.
  - refold; cbn; escape.
    eapply convtm_eta; tea.
    2,4: constructor; first [assumption|now eapply lrefl].
    + gen_typing.
    + eapply ty_conv; [gen_typing| now symmetry].
    + assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0) ..])
      by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
      eapply convtm_exp. 
      * rewrite (eqσ σ G). eapply redtm_beta.
        -- renToWk; eapply wft_wk; tea; gen_typing.
        -- renToWk; eapply ty_wk; tea.
           eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
        -- fold ren_term; refine (ty_var _ (in_here _ _)); gen_typing.
      * eapply redtm_conv.  2: now symmetry.
        rewrite (eqσ σ' G). eapply redtm_beta.
        -- renToWk; eapply wft_wk; tea; gen_typing.
        -- renToWk; eapply ty_wk; tea.
           eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
        -- fold ren_term. eapply ty_conv.
           refine (ty_var _ (in_here _ _)). 1: gen_typing.
           cbn; renToWk; eapply convty_wk; tea; gen_typing.
      * tea.
      * fold ren_term; rewrite <- eqσ; tea.
      * fold ren_term; rewrite <- eqσ.
        eapply ty_conv; [tea|symmetry; tea].
      * now eapply lrefl.
      * fold ren_term. 
        set (x := ren_term _ _); change x with (t[up_term_term σ]⟨upRen_term_term S⟩); clear x.
        set (x := ren_term _ _); change x with (t[up_term_term σ']⟨upRen_term_term S⟩); clear x.
        do 2 rewrite <- eqσ ; eapply escapeEqTerm; now eapply validTmExt.
  - refold; cbn; intros.
    pose proof (Vσa := consWkSubstS VF ρ h Vσ ha).
    assert (ha' : [ _||-<l> a : _| wk ρ h RVF0]).
    1: {
      eapply LRTmRedConv; tea.
      irrelevance0; [reflexivity|].
      eapply wkEq; eapply (validTyExt VF); tea.
    }
    pose proof (Vσa' := consWkSubstS VF ρ h Vσ' ha').
    assert (Vσσa : [_ ||-v _ ≅ (a .: σ'⟨ρ⟩) : _ | _ | _ | Vσa]).
    {
      unshelve eapply consSubstSEq'.
      2: eapply reflLRTmEq; irrelevance0; [|exact ha]; now bsimpl.
      eapply irrelevanceSubstEq; now eapply wkSubstSEq.
      Unshelve. all: tea.
    }
    eapply LREqTermHelper.
    1,2: eapply lamBetaRed; tea.
    + irrelevance0; rewrite consWkEq';[reflexivity|].
      unshelve eapply validTyExt; cycle 3; tea. 
      Unshelve. rewrite consWkEq'; eapply validTy; tea.
    + epose proof (validTmExt Vt _ _ Vσa' Vσσa).
      irrelevance. now rewrite consWkEq'.
Qed.



Lemma ηeqEqTermConvNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ))
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ]) :
  [Δ ,, F[σ] |- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp (PiRedTm.nf Rf)⟨↑⟩ (tRel 0) : G[up_term_term σ]].
Proof.
  refold.
  pose (VσUp :=  liftSubstS' VF Vσ).
  instValid Vσ; instValid VσUp; escape.
  destruct (PiRedTm.red Rf); cbn in *.
  assert (wfΔF : [|- Δ,, F[σ]]) by gen_typing.
  unshelve epose proof (r := PiRedTm.app Rf (@wk1 Δ F[σ]) wfΔF (var0 _ _ _)).
  1: now rewrite wk1_ren_on.
  assumption.
  assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ][(tRel 0) .: @wk1 Δ F[σ] >> tRel])
  by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
  eapply convtm_exp. 
  7: rewrite eqσ; eapply escapeEqTerm; eapply reflLRTmEq; irrelevance.
  * eapply redtm_meta_conv. 3: reflexivity.
    1: eapply redtm_app.
    2: eapply (ty_var wfΔF (in_here _ _)).
    1:{
      replace (f⟨_⟩[_]) with f[σ]⟨@wk1 Δ F[σ]⟩ by (unfold ρ; now bsimpl).
      eapply redtm_meta_conv. 3: reflexivity.
      1: eapply redtm_wk; tea.
      now rewrite wk1_ren_on.
    }
    fold ren_term. rewrite eqσ; now bsimpl. 
  * rewrite <- (wk1_ren_on Δ F[σ]); unshelve eapply redtmwf_refl.
    rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2,4: rewrite <- eqσ; tea.
  * tea.
  * rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2: rewrite <- eqσ; tea.
  * rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2: rewrite <- eqσ; tea.
  * unshelve eapply escapeEq, reflLRTyEq; [|tea].
Qed.


Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ F)
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTy VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ].
Proof.
  set (RΠ := normRedΠ RΠFG); refold.
  enough [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠ ] by irrelevance.
  opector.
  - change [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠ ]; irrelevance.
  - change [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠ ]; irrelevance.
  - cbn; pose (VσUp :=  liftSubstS' VF Vσ).
    instValid Vσ; instValid VσUp; escape.
    destruct (PiRedTm.red p); destruct (PiRedTm.red p0); cbn in *.
    eapply convtm_eta; tea.
    + apply (PiRedTm.isfun p0).
    + apply (PiRedTm.isfun p).
    + etransitivity ; [symmetry| etransitivity]; tea; eapply ηeqEqTermConvNf.
  - match goal with H : [_ ||-Π f[σ] : _ | _] |- _ => rename H into Rfσ end.
    match goal with H : [_ ||-Π g[σ] : _ | _] |- _ => rename H into Rgσ end.
    cbn; intros ?? ρ' h ha.
    set (ν := (a .: σ⟨ρ'⟩)).
    pose (Vν := consWkSubstS VF ρ' h Vσ ha).
    instValid Vσ; instValid Vν; escape.
    assert (wfΔF : [|- Δ,, F[σ]]) by gen_typing.
    cbn in *.
    assert (eq : forall t, t⟨ρ⟩[a .: σ⟨ρ'⟩] = t[σ]⟨ρ'⟩) by (intros; unfold ρ; now bsimpl).
    do 2 rewrite eq in RVfg.
    eapply transEqTerm; [|eapply transEqTerm].
    2: irrelevance; symmetry; apply consWkEq'.
    + eapply LRTmEqSym; eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app Rfσ ρ' h ha); irrelevance.
      eapply redtmwf_appwk; tea.
      1: exact (PiRedTm.red Rfσ).
      now bsimpl.
    + eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app Rgσ ρ' h ha); irrelevance.
      eapply redtmwf_appwk; tea.
      1: exact (PiRedTm.red Rgσ).
      now bsimpl.
Qed.

Lemma etaeqValid {f g} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ]) 
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG].
Proof.
  constructor; intros ??? Vσ; instValid Vσ; now eapply ηeqEqTerm.
Qed.

End LambdaValid.