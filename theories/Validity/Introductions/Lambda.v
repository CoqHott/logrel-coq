From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance Properties Pi Application Var ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Lemma isLRFun_isWfFun `{GenericTypingProperties}
  {l Γ F F' G G' t} (RΠFG : [Γ ||-< l > tProd F G ≅ tProd F' G'])
  (Rt : isLRFun (normRedΠ RΠFG) t)
  : isWfFun Γ F G t.
Proof.
  assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
  destruct Rt as [?? wtA convtyA eqt|]; cbn in *.
  2: now constructor.
  epose proof (instKripkeFamTm wfΓ eqt).
  escape; now constructor.
Qed.


Section LambdaValid.
Context `{GenericTypingProperties}.

  Lemma irrPiRedTm {l l1 l2 Γ domA1 domA2 domB1 domB2 codA1 codA2 codB1 codB2}
  {t} (PA1: PolyRed Γ l1 domA1 domB1 codA1 codB1) (PA2: PolyRed Γ l2 domA2 domB2 codA2 codB2) :
    PolyRed Γ l domA1 domA2 codA1 codA2 -> PiRedTm PA1 t -> PiRedTm PA2 t.
  Proof.
    intros PA Rt; exists Rt.(PiRedTmEq.nf);
      destruct Rt as [?? isfun]; cbn;
      assert (wfΓ : [|-Γ]) by gtyping;
      pose proof (instKripke wfΓ (PA.(PolyRed.shpRed)));
      pose proof (instKripkeFam wfΓ (PA.(PolyRed.posRed))).
    + eapply redtmwf_conv; tea; escape; gtyping.
    + destruct isfun; econstructor; tea; cycle -1.
      1: eapply convneu_conv; tea; escape; gtyping.
      1: etransitivity; tea; escape; now symmetry.
      intros. eapply irrLRCum.
      2: unshelve eapply e; tea; eapply irrLRCum; tea.
      1: eapply PA.(PolyRed.posRed), irrLRCum; try now eapply lrefl.
      all: symmetry; now eapply PA.(PolyRed.shpRed).
      Unshelve. tea.
  Defined.

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.


Lemma lamPiRedTm
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-<l> (tProd F G)[σ] ≅ (tProd F' G')[σ']])
  (R := normRedΠ R0)
  : PiRedTm R (tLambda F t)[σ].
Proof.
  exists (tLambda F[σ] t[up_term_term σ]);
  instValid (liftSubst' VF  Vσσ'); instValid Vσσ'; escape.
  1: now eapply redtmwf_refl, ty_lam.
  constructor; tea; [now eapply lrefl|].
  intros; rewrite 2!consWkEq'.
  pose (Vaσ := consWkSubstEq VF (lrefl Vσσ') ρ h ha).
  eapply irrLREq.
  2: now unshelve eapply (validTmExt (lrefl Vtt')).
  cbn; now rewrite consWkEq'.
Defined.

Lemma lamPiRedTm'
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  (VΠFG := PiValid VΓ VF VG)
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-<l> (tProd F G)[σ] ≅ (tProd F' G')[σ']])
  (R := normRedΠ R0)
  : PiRedTm R (tLambda F' t')[σ'].
Proof.
  eapply irrPiRedTm; [|eapply lamPiRedTm]; refold.
  + cbn; unshelve eapply symPoly; [exact R| (intros; apply symLR)..].
  + now eapply symValidTm.
  + now eapply symSubst.
  Unshelve. 1-3: irrValid.
  1: now symmetry.
  tea.
Defined.

Lemma consWkEq {Δ Ξ F} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma eq_subst_3 t a ρ σ : t[up_term_term σ][a .: ρ >> tRel] = t[up_term_term σ⟨ρ⟩][a..].
Proof.
  bsimpl ; now substify.
Qed.

Lemma eq_subst_4 t a σ : t[up_term_term σ][a..] = t[a .: σ].
Proof.
  bsimpl ; now substify.
Qed.

Lemma eq_upren t σ ρ : t[up_term_term σ]⟨upRen_term_term ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. rasimpl; unfold Ren1_subst; rasimpl; substify; now rasimpl. Qed.

Lemma eq_substren {Γ Δ} t σ (ρ : Γ ≤ Δ) : t[σ]⟨ρ⟩ = t[σ⟨ρ⟩].
Proof. now rasimpl. Qed.

Context {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VF : [Γ ||-v<l> F ≅ F' | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF])
  (VΠFG := PiValid VΓ VF VG).

Lemma lamCongValid {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG]) :
  [Γ ||-v<l> tLambda F t ≅ tLambda F' t' : tProd F G | VΓ | VΠFG ].
Proof.
  constructor; intros.
  match goal with | [|- [LRAd.pack ?R | _ ||- ?t ≅ ?t' : _]] =>
    enough [_ ||-<_> t ≅ t' : _| LRPi' (normRedΠ R)] by now eapply irrLREq
  end; refold.
  exists (lamPiRedTm Vtt' Vσσ' _)  (lamPiRedTm' Vtt' Vσσ' _); cbn; refold.
  + pose proof (Vuσ := liftSubst' VF Vσσ').
    pose proof (Vuσ' := liftSubstSym' VF Vσσ').
    pose proof (symValidTm' Vtt'); pose proof (symValidTy' VG).
    instValid Vσσ'; instValid Vuσ'; instValid Vuσ; escape.
    eapply lambda_cong; tea; now symmetry.
  + cbn; intros.
    set (RF := PolyRed.shpRed _ _ _) in hab.
    pose proof (Vσρ := wkSubst VΓ wfΔ h ρ Vσσ').
    pose proof (symValidTm' Vtt').
    instValid Vσρ; instValid (liftSubst' VF Vσρ); instValid (liftSubstSym' VF Vσρ).
    instValid (consWkSubstEq VF Vσσ' ρ h hab).
    escape. eapply irrLREq.
    1: now rewrite eq_subst_3.
    eapply redSubstTmEq; cycle 1.
    * eapply redtm_beta; tea.
      now rewrite eq_upren, eq_substren.
    * eapply redtm_beta.
      1,3: rewrite eq_substren; tea.
      1: eapply ty_conv; tea; cbn; now rewrite eq_substren.
      now rewrite eq_upren, eq_substren.
      Unshelve. now rewrite 2!eq_subst_4.
    * now rewrite !eq_upren, !eq_subst_4.
  Qed.


Lemma lamValid {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG]) :
  [Γ ||-v<l> tLambda F t : tProd F G | VΓ | VΠFG ].
Proof.
  now eapply lrefl, lamCongValid.
Qed.


Lemma singleSubst_subst_eq t a σ : t[a..][σ] = t[up_term_term σ][a[σ]..].
Proof. now bsimpl. Qed.

Lemma singleSubst_subst_eq' t a σ : t[a..][σ] = t[a[σ] .: σ].
Proof. now bsimpl. Qed.

Lemma betaValid {t t' a a'} (Vt : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  (Va : [Γ ||-v<l> a ≅ a' : F | VΓ | VF]) :
  [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G[a..] | VΓ | substS VG Va].
Proof.
  eapply redSubstValid.
  2: now eapply lrefl, substSTm.
  constructor; intros; cbn.
  rewrite 2!singleSubst_subst_eq.
  instValid (lrefl Vσσ').
  instValid (liftSubst' VF (lrefl Vσσ')).
  escape; now eapply redtm_beta.
Qed.


Lemma redtm_app_helper {Δ Δ' f nf a σ} (ρ : Δ' ≤ Δ) :
  [|- Δ'] ->
  [Δ |- f[σ] ⤳* nf : (tProd F G)[σ]] ->
  [Δ' |- a : F[σ]⟨ρ⟩] ->
  [Δ' |- tApp f[σ]⟨ρ⟩ a ⤳* tApp nf⟨ρ⟩ a : G[up_term_term σ][a .: ρ >> tRel]].
Proof.
  intros red tya.
  rewrite eq_subst_3; eapply redtm_app; tea.
  eapply redtm_meta_conv; [now eapply redtm_wk| | reflexivity].
  cbn; now rewrite eq_upren.
Qed.


Lemma ηeqEqTermNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := normRedΠ (validTyExt VΠFG wfΔ Vσ))
  (RGσ : [Δ ,, F[σ] ||-<l> G[up_term_term σ]])
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | LRPi' RΠFG ]) :
  [RGσ | Δ ,, F[σ] ||- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp Rf.(PiRedTmEq.redR).(PiRedTmEq.nf)⟨↑⟩ (tRel 0) : G[up_term_term σ]].
Proof.
  refold.
  pose (VσUp :=  liftSubst' VF Vσ).
  instValid Vσ; instValid VσUp; escape.
  assert (wfΔF : [|- Δ,, F[σ]]) by gen_typing.
  unshelve epose proof (r := PiRedTmEq.eqApp Rf (@wk1 Δ F[σ]) wfΔF (var0 _ _ _)); tea.
  1: now rewrite wk1_ren_on.
  eapply irrLREq; [ erewrite <-(var0_wk1_id (t:=G[_])); reflexivity|].
  eapply redSubstLeftTmEq.
  + erewrite <- wk1_ren_on; now eapply irrLREq.
  + clear r; destruct Rf.(PiRedTmEq.redL) as [? [? red] ?]; cbn -[wk1] in *.
    replace f⟨ρ⟩[up_term_term σ] with f[σ]⟨@wk1 Δ F[σ]⟩.
    eapply redtm_app_helper; tea.
    1: rewrite wk1_ren_on; now eapply ty_var0.
    unfold ρ; now bsimpl.
    Unshelve. 2: now rewrite var0_wk1_id.
Qed.


Lemma ηeqEqTermConvNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := normRedΠ (validTyExt VΠFG wfΔ Vσ))
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | LRPi' RΠFG ]) :
  [Δ ,, F[σ] |- tApp f⟨ρ⟩[up_term_term σ] (tRel 0) ≅ tApp Rf.(PiRedTmEq.redR).(PiRedTmEq.nf)⟨↑⟩ (tRel 0) : G[up_term_term σ]].
Proof.
  refold.
  pose (VσUp :=  liftSubst' VF Vσ); instValid VσUp.
  unshelve eapply escapeEqTerm, ηeqEqTermNf; now eapply lrefl.
Qed.

Ltac normRedΠin Rt :=
  match type of Rt with
  | [LRAd.pack ?R | _ ||- ?t ≅ ?t' : _] =>
    apply (irrLREq _ (LRPi' (normRedΠ R)) eq_refl) in Rt
  end; refold.


Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ F)
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTyExt VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ].
Proof.
  normRedΠin Rf; normRedΠin Rg; set (RΠ := normRedΠ _) in Rf, Rg.
  enough [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | LRPi' RΠ ] by now eapply irrLREq.
  pose (Rf0 := Rf.(PiRedTmEq.redR)); pose (Rg0 := Rg.(PiRedTmEq.redR)).
  exists Rf0 Rg0.
  - cbn; pose (VσUp := liftSubst' VF Vσ).
    instValid Vσ; instValid VσUp; escape.
    eapply convtm_eta; tea.
    2,4: eapply isLRFun_isWfFun, PiRedTmEq.isfun.
    + destruct Rf0; cbn in *; gen_typing.
    + destruct Rg0; cbn in *; gen_typing.
    + etransitivity ; [symmetry| etransitivity]; tea; eapply ηeqEqTermConvNf.
  - cbn; intros ??? ρ' h ha.
    epose (Vν := consWkSubstEq VF Vσ ρ' h (lrefl ha)); instValid Vν.
    assert (eq : forall t a, t⟨ρ⟩[a .: σ⟨ρ'⟩] = t[σ]⟨ρ'⟩) by (intros; unfold ρ; now bsimpl).
    cbn in RVfg; rewrite 2!eq in RVfg.
    etransitivity; [| etransitivity].
    + symmetry; eapply redSubstLeftTmEq.
      1: pose proof (urefl (PiRedTmEq.eqApp Rf ρ' h (lrefl ha))); now eapply irrLREq.
      eapply redtm_app_helper; tea; [| now escape].
      now destruct (PiRedTmEq.redR Rf) as [? []].
    + eapply irrLREq; tea; now rewrite Poly.eq_subst_2.
    + eapply redSubstLeftTmEq.
      1: pose proof (rg := PiRedTmEq.eqApp Rg ρ' h ha); now eapply irrLREq.
      eapply redtm_app_helper; tea; [| now escape].
      now destruct (PiRedTmEq.redL Rg) as [? []].
Qed.

Lemma etaeqValid {f g} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ])
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG].
Proof.
  constructor; intros ???? Vσ; instValid Vσ; instValid (lrefl Vσ).
  etransitivity.
  + eapply irrLREq; [reflexivity|];eapply ηeqEqTerm; tea.
  + now eapply irrLREq.
Qed.

Lemma upren_subst_rel0 t : t[(tRel 0)]⇑ = t.
Proof. bsimpl; rewrite scons_eta'; now bsimpl. Qed.

Lemma etaExpandValid {f} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]) :
  [Γ ,, F ||-v<l> eta_expand f : G | VΓF | VG].
Proof.
  unshelve epose (VF' := wkValidTy ρ _ _ VF); [|tea|].
  unshelve epose (wkValidTy ρ _ _ VΠFG); [|tea|].
  unshelve epose (wkValidTm ρ _ _ _ Vf); [|tea|].
  eapply irrValidTmRfl; cycle 1.
  + eapply appcongValid; erewrite <-wk1_ren_on.
    eapply irrValidTmRfl; tea; reflexivity.
  + refold; unfold ρ; now erewrite <-wk_up_ren_on, <-subst1_ren_wk_up, var0_wk1_id.
  Unshelve.
  1: tea.
  3: tea.
  all: refold.
  1: pose (var0Valid _ VF); now eapply irrValidTmRfl.
  tea.
Qed.

End LambdaValid.

Section EtaValid.
Context `{GenericTypingProperties}.

Context {Γ F G l}
  {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma subst_rel0 t : t⟨↑⟩[(tRel 0)..] = t.
Proof. now bsimpl. Qed.

Lemma etaValid {f} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]) :
  [Γ ||-v<l> (tLambda F (eta_expand f)) ≅ f : tProd F G | VΓ | VΠFG].
Proof.
  assert [||-v Γ,, F] by now eapply validSnoc.
  unshelve epose (wkValidTm ρ _ _ _ Vf); [|tea|].
  unshelve epose (VF' := wkValidTy ρ _ _ VF); [|tea|].
  unshelve epose (VG' := wkValidTy (wk_up F ρ) _ _ VG).
  2:now eapply validSnoc.
  unshelve epose (wkValidTy ρ _ _ VΠFG); [|tea|].
  eapply etaeqValid; tea.
  1: now eapply lamValid, etaExpandValid.
  unshelve epose (x := betaValid VF'  VG' (t:=(eta_expand f⟨ρ⟩)) (t':=(eta_expand f⟨ρ⟩)) (a:=(tRel 0)) (a':=(tRel 0)) _ _).
  3: eapply irrValidTmRfl; cycle 1.
  + eapply etaExpandValid; now eapply irrValidTmRfl.
  + pose (var0Valid _ VF); now eapply irrValidTmRfl.
  + cbn -[wk1] in x |- *.
    rewrite subst_rel0 in x.
    replace f⟨↑⟩⟨upRen_term_term (wk1 F)⟩ with f⟨ρ⟩⟨↑⟩.
    2: unfold ρ; unshelve erewrite <-wk_up_ren_on; tea; now bsimpl.
    apply x.
  + rewrite wk_up_wk1_ren_on; bsimpl; apply upren_subst_rel0.
Qed.

End EtaValid.
