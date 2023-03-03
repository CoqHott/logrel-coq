From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section LambdaValid.
Context `{GenericTypingProperties}.

Lemma consWkSubstS {Γ F Δ Ξ σ a l VΓ wfΔ } nF VF
  (ρ : Ξ ≤ Δ) wfΞ {RF}:
  [Δ ||-v σ : Γ | VΓ | wfΔ] ->
  [Ξ ||-<l> a : F[σ]⟨ρ⟩ | RF] ->
  [Ξ ||-v (a .: σ⟨ρ⟩) : Γ,, vass nF F | validSnoc (l:=l) nF VΓ VF | wfΞ].
Proof.
  intros. unshelve eapply consSubstS.  2: irrelevance.
  now eapply wkSubstS.
Qed.
  
Context {Γ nF F G l} {VΓ : [||-v Γ]} (VF : [Γ ||-v<l> F | VΓ]) 
  (VΓF := validSnoc nF VΓ VF)
  (VG : [Γ ,, vass nF F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma consWkEq {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up nF F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.


Lemma lamValid0 {t} (Vt : [Γ ,, vass nF F ||-v<l> t : G | VΓF | VG]) 
  {Δ σ} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) :
  [validTy VΠFG wfΔ Vσ | Δ ||- (tLambda nF F t)[σ] : (tProd nF F G)[σ]].
Proof.
  pose proof (VσUp :=  liftSubstS' nF VF Vσ).
  instValid Vσ. instValid VσUp.
  pose (RΠ := normRedΠ RVΠFG); refold.
  enough [RΠ | Δ ||- (tLambda nF F t)[σ] : (tProd nF F G)[σ]] by irrelevance.
  pose proof (escape_ RVF). pose proof (escapeTerm_ _ RVt). 
  pose proof (escape_ RVG).
  assert [Δ |- (tLambda nF F t)[σ] : (tProd nF F G)[σ]] by (cbn; gen_typing).
  assert (happred :
    forall Δ0 a (ρ : Δ0 ≤ Δ) (wfΔ0 : [|-Δ0])
      (RFσ : [Δ0 ||-<l> F[σ]⟨ρ⟩]) 
      (ha : [RFσ | _ ||- a : _])
      (RGσ : [Δ0 ||-<l> G[up_term_term σ][a .: ρ >> tRel]]),
      [_ ||-<l> tApp (tLambda nF F t)[σ]⟨ρ⟩ a : _ | RGσ] × 
      [_ ||-<l> tApp (tLambda nF F t)[σ]⟨ρ⟩ a ≅ t[a .: σ⟨ρ⟩] : _ | RGσ]).
  1:{
    intros.
    pose proof (escapeTerm_ _ ha).
    pose proof (Vσa := consWkSubstS nF VF ρ wfΔ0 Vσ ha).
    assert [_ ||-<l> t[a .: σ⟨ρ⟩] : _ | validTy VG wfΔ0 Vσa].
    1:{ irrelevance0. 2:unshelve eapply validTm. 4-8: tea. reflexivity. }
    (* assert (hredbeta : [Δ0 |-[ ta ] tApp (tLambda nF F t)[σ]⟨ρ⟩ a :⇒*:  t[up_term_term σ]⟨wk_up nF F[σ] ρ⟩[a..] : G[up_term_term σ]⟨wk_up nF F[σ] ρ⟩[a..]]). *)
    assert (hredbeta : [Δ0 |-[ ta ] tApp (tLambda nF F t)[σ]⟨ρ⟩ a :⇒*:  t[a .: σ⟨ρ⟩] : G[a .: σ⟨ρ⟩]]).
    {
      constructor.
      * rewrite <- consWkEq.
      eapply (ty_app (na:= nF)); tea.
        change (tProd _ _ _) with ((tProd nF F G)[σ]⟨ρ⟩).
        now eapply ty_wk.
      * now eapply escapeTerm_.
      * do 2 rewrite <- consWkEq.
        eapply redtm_beta.
        -- fold subst_term; renToWk; eapply wft_wk; tea; gen_typing.
        -- fold subst_term; renToWk;  eapply ty_wk; tea.
            eapply wfc_cons; tea; eapply wft_wk; tea.
        -- now eapply escapeTerm_.
    }
    irrelevance0.
    2: unshelve eapply (redSubstTerm _ _ hredbeta); tea.
    rewrite <- consWkEq; now bsimpl.
  }
  exists (tLambda nF F t)[σ]; intros; cbn in *.
  + now eapply redtmwf_refl.
  + now constructor.
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
    rewrite <- (eqσ t); eapply escapeEqTerm_; now eapply LREqTermRefl_.
  + eapply happred; tea. 
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
    eapply transEqTerm; [| eapply transEqTerm].
    1: eapply happred; tea.
    2:{
      eapply LRTmEqSym; eapply LRTmEqRedConv.
      2:eapply happred; tea.
      rewrite consWkEq'; unshelve eapply LRTyEqSym.
      2: eapply validTy; tea.
      rewrite consWkEq'. 
      unshelve eapply validTyExt; tea.
      Unshelve. rewrite consWkEq'; eapply validTy; tea.
    }
    epose proof (validTmExt Vt _ _ Vσb Vσab).
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
  pose proof (VσσUp := liftSubstSEq' nF VF Vσσ').
  instAllValid Vσ Vσ' Vσσ'.
  instAllValid VσUp VσUp' VσσUp.
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
  - refold; cbn. admit.
  - refold; cbn; intros.
  admit.
Admitted.

Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ nF F)
  (Vfg : [Γ ,, vass nF F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTy VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd nF F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd nF F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd nF F G)[σ] | RΠFG ].
Proof.
  admit.
Admitted.


Lemma etaeqValid {f g} (ρ := @wk1 Γ nF F)
  (Vf : [Γ ||-v<l> f : tProd nF F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd nF F G | VΓ | VΠFG ]) 
  (Vfg : [Γ ,, vass nF F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd nF F G | VΓ | VΠFG].
Proof.
  admit.
Admitted.

End LambdaValid.