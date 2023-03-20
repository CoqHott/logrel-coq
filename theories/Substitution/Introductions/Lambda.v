From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.


Section LambdaValid.
Context `{GenericTypingProperties}.





Context {Γ nF F G l} {VΓ : [||-v Γ]} (VF : [Γ ||-v<l> F | VΓ]) 
  (VΓF := validSnoc nF VΓ VF)
  (VG : [Γ ,, vass nF F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma consWkEq {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up nF F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma lamBetaRed {t} (Vt : [Γ ,, vass nF F ||-v<l> t : G | VΓF | VG]) 
  {Δ σ} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) 
  {Δ0 a} (ρ : Δ0 ≤ Δ) (wfΔ0 : [|-Δ0])
  (RFσ : [Δ0 ||-<l> F[σ]⟨ρ⟩]) 
  (ha : [RFσ | _ ||- a : _])
  (RGσ : [Δ0 ||-<l> G[up_term_term σ][a .: ρ >> tRel]]) :
    [_ ||-<l> tApp (tLambda nF F t)[σ]⟨ρ⟩ a : _ | RGσ] × 
    [_ ||-<l> tApp (tLambda nF F t)[σ]⟨ρ⟩ a ≅ t[a .: σ⟨ρ⟩] : _ | RGσ].
Proof.
  pose proof (Vσa := consWkSubstS nF VF ρ wfΔ0 Vσ ha); instValid Vσa.
  pose proof (VσUp :=  liftSubstS' nF VF Vσ).
  instValid Vσ. instValid VσUp.  escape.
  irrelevance0. 1: now rewrite consWkEq'.
  eapply redwfSubstTerm; tea.
  constructor; tea.
  * rewrite <- consWkEq.  eapply (ty_app (na:= nF)); tea.
    change (tProd _ _ _) with ((tProd nF F G)[σ]⟨ρ⟩).
    eapply ty_wk; tea; cbn; gen_typing.
  * do 2 rewrite <- consWkEq.
    eapply redtm_beta; tea.
    fold subst_term; renToWk;  eapply ty_wk; tea.
    eapply wfc_cons; tea; eapply wft_wk; tea.
Qed.

Lemma betaValid {t a} (Vt : [Γ ,, vass nF F ||-v<l> t : G | VΓF | VG]) 
  (Va : [Γ ||-v<l> a : F | VΓ | VF]) :
  [Γ ||-v<l> tApp (tLambda nF F t) a ≅ t[a..] : G[a..] | VΓ | substS nF VG Va].
Proof.
  constructor; intros. instValid Vσ.
  pose (Vσa := consSubstS (nA := nF) _ _ Vσ _ RVa). instValid Vσa.
  pose proof (VσUp :=  liftSubstS' nF VF Vσ).
  instValid Vσ. instValid VσUp.  escape.
  assert (eq : forall t, t[a..][σ] = t[up_term_term σ][a[σ]..]) by (intros; now bsimpl).
  assert (eq' : forall t, t[a..][σ] = t[a[σ].: σ]) by (intros; now bsimpl).
  irrelevance0. 1: symmetry; apply eq.
  rewrite eq;  eapply redwfSubstTerm; tea.
  1: rewrite <- eq; rewrite eq'; irrelevance.
  constructor; tea.
  * eapply (ty_app (na:= nF)); tea. refold. gen_typing.
  * do 2 (rewrite <- eq; rewrite eq'); tea.
  * eapply redtm_beta; tea.
    Unshelve. 2:rewrite <- eq; now rewrite eq'.
Qed.

Lemma lamValid0 {t} (Vt : [Γ ,, vass nF F ||-v<l> t : G | VΓF | VG]) 
  {Δ σ} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) :
  [validTy VΠFG wfΔ Vσ | Δ ||- (tLambda nF F t)[σ] : (tProd nF F G)[σ]].
Proof.
  pose proof (VσUp :=  liftSubstS' nF VF Vσ).
  instValid Vσ. instValid VσUp. escape.
  pose (RΠ := normRedΠ RVΠFG); refold.
  enough [RΠ | Δ ||- (tLambda nF F t)[σ] : (tProd nF F G)[σ]] by irrelevance.
  assert [Δ |- (tLambda nF F t)[σ] : (tProd nF F G)[σ]] by (escape; cbn; gen_typing).
  exists (tLambda nF F t)[σ]; intros; cbn in *.
  + now eapply redtmwf_refl.
  + constructor.
  + apply tm_nf_lam.
    - now apply reifyType in RVF.
    - now apply reifyTerm in RVt.
  + eapply convtm_eta; tea. 
    1,2: now constructor.
    assert (eqσ : forall Z, Z[up_term_term σ] = Z[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0) ..])
    by (intro; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
    assert [Δ,, vass nF F[σ] |-[ ta ] tApp (tLambda nF F[σ] t[up_term_term σ])⟨S⟩ (tRel 0) ⇒*  t[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0)..] : G[up_term_term σ]].
    {
      rewrite (eqσ G). eapply redtm_beta.
      * renToWk; eapply wft_wk; tea; gen_typing.
      * renToWk; eapply ty_wk; tea.
        eapply wfc_cons; [gen_typing | eapply wft_wk; gen_typing].
      * fold ren_term; refine (ty_var _ (in_here _ _)); gen_typing.
    }
    eapply convtm_exp; tea.
    1: now eapply redty_refl.
    rewrite <- (eqσ t); eapply escapeEqTerm; now eapply LREqTermRefl_.
  + eapply lamBetaRed; tea. 
  + pose proof (Vσa := consWkSubstS nF VF ρ h Vσ ha).
    pose proof (Vσb := consWkSubstS nF VF ρ h Vσ hb).
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

Lemma lamValid {t} (Vt : [Γ ,, vass nF F ||-v<l> t : G | VΓF | VG])
   :
    [Γ ||-v<l> tLambda nF F t : tProd nF F G | VΓ | VΠFG ].
Proof.
  opector. 1: now apply lamValid0.
  intros.
  pose (VσUp :=  liftSubstS' nF VF Vσ).
  pose proof (VσUp' :=  liftSubstS' nF VF Vσ').
  pose proof (VσUprea :=  liftSubstSrealign' nF VF Vσσ' Vσ').
  pose proof (VσσUp := liftSubstSEq' nF VF Vσσ').
  instAllValid Vσ Vσ' Vσσ';  instValid VσUp'; instAllValid VσUp VσUprea VσσUp.
  pose (RΠ := normRedΠ RVΠFG); refold.
  enough [RΠ | Δ ||- (tLambda nF F t)[σ] ≅ (tLambda nF F t)[σ'] : (tProd nF F G)[σ]] by irrelevance.
  unshelve econstructor.
  - change [RΠ | Δ ||- (tLambda nF F t)[σ] : (tProd nF F G)[σ]].
    eapply normLambda.
    epose (lamValid0 Vt wfΔ Vσ).
    irrelevance.
  - change [RΠ | Δ ||- (tLambda nF F t)[σ'] : (tProd nF F G)[σ]].
    eapply normLambda.
    eapply LRTmRedConv.
    2: epose (lamValid0 Vt wfΔ Vσ'); irrelevance.
    eapply LRTyEqSym. eapply (validTyExt VΠFG); tea.
    Unshelve. 2: now eapply validTy.
  - refold; cbn; escape.
    eapply convtm_eta; tea. 
    2,4: now constructor.
    + gen_typing.
    + eapply ty_conv; [gen_typing| now symmetry].
    + assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ]⟨upRen_term_term S⟩[(tRel 0) ..])
      by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
      eapply convtm_exp. 
      * now eapply redty_refl.
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
      * fold ren_term. 
        set (x := ren_term _ _); change x with (t[up_term_term σ]⟨upRen_term_term S⟩); clear x.
        set (x := ren_term _ _); change x with (t[up_term_term σ']⟨upRen_term_term S⟩); clear x.
        do 2 rewrite <- eqσ ; eapply escapeEqTerm; now eapply validTmExt.
  - refold; cbn; intros.
    pose proof (Vσa := consWkSubstS nF VF ρ h Vσ ha).
    assert (ha' : [ _||-<l> a : _| wk ρ h RVF0]).
    1: {
      eapply LRTmRedConv; tea.
      irrelevance0; [reflexivity|].
      eapply wkEq; eapply (validTyExt VF); tea.
    }
    pose proof (Vσa' := consWkSubstS nF VF ρ h Vσ' ha').
    assert (Vσσa : [_ ||-v _ ≅ (a .: σ'⟨ρ⟩) : _ | _ | _ | Vσa]).
    {
      unshelve eapply consSubstSEq'.
      2: eapply LREqTermRefl_; irrelevance0; [|exact ha]; now bsimpl.
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



Lemma ηeqEqTermConvNf {σ Δ f} (ρ := @wk1 Γ nF F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ))
  (Rf : [Δ ||-<l> f[σ] : (tProd nF F G)[σ] | RΠFG ]) :
  [Δ ,, vass nF F[σ] |- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp (PiRedTm.nf Rf)⟨↑⟩ (tRel 0) : G[up_term_term σ]].
Proof.
  refold.
  pose (VσUp :=  liftSubstS' nF VF Vσ).
  instValid Vσ; instValid VσUp; escape.
  destruct (PiRedTm.red Rf); cbn in *.
  assert (wfΔF : [|- Δ,, vass nF F[σ]]) by gen_typing.
  unshelve epose proof (r := PiRedTm.app Rf (@wk1 Δ nF F[σ]) wfΔF (var0 _ _ _)).
  1: now rewrite wk1_ren_on.
  assert (eqσ : forall σ Z, Z[up_term_term σ] = Z[up_term_term σ][(tRel 0) .: @wk1 Δ nF F[σ] >> tRel])
  by (intros; bsimpl; cbn; now rewrite rinstInst'_term_pointwise).
  eapply convtm_exp. 
  1: now eapply redty_refl.
  3: rewrite eqσ; eapply escapeEqTerm; eapply LREqTermRefl_; irrelevance.
  * eapply redtm_meta_conv. 3: reflexivity.
    1: eapply redtm_app.
    2: eapply (ty_var wfΔF (in_here _ _)).
    1:{
      replace (f⟨_⟩[_]) with f[σ]⟨@wk1 Δ nF F[σ]⟩ by (unfold ρ; now bsimpl).
      eapply redtm_meta_conv. 3: reflexivity.
      1: eapply redtm_wk; tea.
      now rewrite wk1_ren_on.
    }
    fold ren_term. rewrite eqσ; now bsimpl. 
  * rewrite <- (wk1_ren_on Δ nF F[σ]); unshelve eapply redtmwf_refl.
    rewrite eqσ; eapply escapeTerm ; irrelevance.
    Unshelve. 2,4: rewrite <- eqσ; tea.
Qed.


Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ nF F)
  (Vfg : [Γ ,, vass nF F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTy VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd nF F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd nF F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd nF F G)[σ] | RΠFG ].
Proof.
  set (RΠ := normRedΠ RΠFG); refold.
  enough [Δ ||-<l> f[σ] ≅ g[σ] : (tProd nF F G)[σ] | RΠ ] by irrelevance.
  opector.
  - change [Δ ||-<l> f[σ] : (tProd nF F G)[σ] | RΠ ]; irrelevance.
  - change [Δ ||-<l> g[σ] : (tProd nF F G)[σ] | RΠ ]; irrelevance.
  - cbn; pose (VσUp :=  liftSubstS' nF VF Vσ).
    instValid Vσ; instValid VσUp; escape.
    destruct (PiRedTm.red p); destruct (PiRedTm.red p0); cbn in *.
    eapply convtm_eta; tea.
    1,2: eapply PiRedTm.isfun.
    etransitivity ; [symmetry| etransitivity]; tea; eapply ηeqEqTermConvNf.
  - cbn; intros.
    set (ν := (a .: σ⟨ρ0⟩)).
    pose (Vν := consWkSubstS nF VF ρ0 h Vσ ha).
    instValid Vσ; instValid Vν; escape.
    assert (wfΔF : [|- Δ,, vass nF F[σ]]) by gen_typing.
    cbn in *.
    assert (eq : forall t, t⟨ρ⟩[a .: σ⟨ρ0⟩] = t[σ]⟨ρ0⟩) by (intros; unfold ρ; now bsimpl).
    do 2 rewrite eq in RVfg.
    eapply transEqTerm; [|eapply transEqTerm].
    2: irrelevance; symmetry; apply consWkEq'.
    + eapply LRTmEqSym; eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app p ρ0 h ha); irrelevance.
      eapply redtmwf_appwk; tea.
      1: exact (PiRedTm.red p).
      now bsimpl.
    + eapply redwfSubstTerm.
      1: unshelve epose proof (r := PiRedTm.app p0 ρ0 h ha); irrelevance.
      eapply redtmwf_appwk; tea.
      1: exact (PiRedTm.red p0).
      now bsimpl.
Qed.

Lemma etaeqValid {f g} (ρ := @wk1 Γ nF F)
  (Vf : [Γ ||-v<l> f : tProd nF F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd nF F G | VΓ | VΠFG ]) 
  (Vfg : [Γ ,, vass nF F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd nF F G | VΓ | VΠFG].
Proof.
  constructor; intros ??? Vσ; instValid Vσ; now eapply ηeqEqTerm.
Qed.

End LambdaValid.