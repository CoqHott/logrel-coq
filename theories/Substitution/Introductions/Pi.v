From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedValues Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Universe.

(* Set Universe Polymorphism. *)

Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.

Section PiTyValidity.

  Context `{GenericTypingProperties}.
  Context {l Γ F G} (vΓ : [||-v Γ])
    (vF : [Γ ||-v< l > F | vΓ ])
    (vG : [Γ ,, F ||-v< l > G | validSnoc vΓ vF]).

  Lemma domainRed {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > F[σ] ].
  Proof.
    exact (validTy vF tΔ vσ).
  Defined.

  Lemma domainTy {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ |-[ ta ] F[σ] ].
  Proof.
    eapply escape.
    now eapply domainRed.
  Defined.

  Lemma domainTyRefl {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ |-[ ta ] F[σ] ≅ F[σ] ].
  Proof.
    refine (escapeEq (domainRed tΔ vσ) _).
    now eapply LRTyEqRefl_.
  Qed.

  Lemma domainTyEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
    : [Δ,, F[σ] |-[ ta ] F[σ⟨@wk1 Δ F[σ]⟩] ≅ F[σ'⟨@wk1 Δ F[σ]⟩]].
  Proof.
    eapply escapeEq.
    eapply (validTyExt vF).
    refine (wk1SubstS _ _ (domainTy tΔ vσ) vσ').
    refine (wk1SubstSEq _ _ (domainTy tΔ vσ) vσ vσσ').
  Qed.


  Lemma codomainRed {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, F[σ] ||-< l > G[ up_term_term σ ] ].
  Proof.
    rewrite (eq_subst_1 F G Δ σ).
    refine (validTy vG _ (liftSubstS vΓ tΔ vF vσ)).
  Qed.

  Lemma codomainTy {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, F[σ] |-[ ta ] G[ up_term_term σ ] ].
  Proof.
    eapply escape.
    now eapply codomainRed.
  Qed.

  Lemma codomainTyRefl {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, F[σ] |-[ ta ] G[ up_term_term σ ] ≅ G[ up_term_term σ ]].
  Proof.
    refine (escapeEq (codomainRed tΔ vσ) _).
    now eapply LRTyEqRefl_.
  Qed.

  Lemma codomainSubstRed {Δ Δ' σ a} (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ'])
    (ρ : Δ' ≤ Δ) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (domainRed tΔ vσ)])
    : [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]].
  Proof.
    rewrite eq_subst_2.
    unshelve eapply (validTy vG) ; tea.
    unshelve eapply consSubstS.
    eapply wkSubstS ; tea. irrelevance.
  Qed.

  Lemma codomainSubstRedEq1 {Δ Δ' σ a b} (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ'])
    (ρ : Δ' ≤ Δ) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (domainRed tΔ vσ)])
    (rb : [ Δ' ||-< l > b : F[σ]⟨ρ⟩ | wk ρ tΔ' (domainRed tΔ vσ)])
    (rab : [ Δ' ||-< l > a ≅ b : F[σ]⟨ρ⟩ | wk ρ tΔ' (domainRed tΔ vσ)])
    : [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]
                     ≅ G[up_term_term σ][b .: ρ >> tRel] | codomainSubstRed tΔ tΔ' ρ vσ ra].
  Proof.
    eapply LRTyEqIrrelevant' with (A := G[a .: σ⟨ρ⟩]).
    - symmetry. eapply eq_subst_2.
    - rewrite eq_subst_2.
      unshelve eapply (validTyExt vG tΔ' _ _ _).
      + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
      + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
      + unshelve econstructor.
        * eapply reflSubst.
        * irrelevance.
  Qed.

  Lemma codomainSubstRedEq2 {Δ Δ' σ σ' a} (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ']) (ρ : Δ' ≤ Δ)
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
    (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (domainRed tΔ vσ)])
    : [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]
                     ≅ G[up_term_term σ'][a .: ρ >> tRel] | codomainSubstRed tΔ tΔ' ρ vσ ra].
    Proof.
      eapply LRTyEqIrrelevant' with (A := G[a .: σ⟨ρ⟩]).
      - symmetry. apply eq_subst_2.
      - rewrite eq_subst_2. unshelve eapply (validTyExt vG tΔ' _ _ _).
        + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
        + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ') vF _).
          refine (LRTmRedConv _ _ _ _ _ _ _ _ _ ra).
          replace (F[σ'⟨ρ⟩]) with (F[σ']⟨ρ⟩) by (now asimpl).
          refine (wkEq ρ tΔ' _ (validTyExt vF tΔ vσ vσ' vσσ')).
        + unshelve econstructor.
          * cbn. now eapply wkSubstSEq.
          * cbn. eapply LRTmEqIrrelevant'.
            2:refine (LREqTermRefl_ _ ra). now asimpl.
  Qed.

  Lemma prodTyEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
    : [Δ |-[ ta ] tProd F[σ] G[up_term_term σ] ≅ tProd F[σ'] G[up_term_term σ']].
  Proof.
    refine (convty_prod (domainTy tΔ vσ) _ _).
    - eapply escapeEq. eapply (validTyExt vF tΔ vσ vσ' vσσ').
    - rewrite (eq_subst_1 F G Δ σ). rewrite (eq_subst_1 F G Δ σ').
      assert ([Δ,, F[σ] |-[ ta ] tRel 0 : F[↑ >> (tRel 0 .: σ⟨@wk1 Δ F[σ]⟩)]]).
      { replace (F[_ >> _]) with (F[σ]⟨S⟩) by (now bsimpl).
        refine (ty_var (wfc_cons tΔ (domainTy _ vσ)) (in_here _ _)). }
      eapply escapeEq. unshelve refine (validTyExt vG _ _ _ _).
      + eapply wfc_cons. easy. refine (domainTy tΔ vσ).
      + refine (liftSubstS vΓ tΔ vF vσ).
      + unshelve econstructor.
        * refine (wk1SubstS vΓ tΔ (domainTy tΔ vσ) vσ').
        * set (ρ' := @wk1 Δ F[σ']).
          assert ([Δ,, F[σ] |-[ ta ] tRel 0 : F[↑ >> (tRel 0 .: σ'⟨ρ'⟩)]]).
          { eapply ty_conv; [eassumption|].
            eapply (domainTyEq tΔ vσ vσ' vσσ'). }
          cbn; eapply neuTerm; [|assumption|now apply convneu_var].
          replace (F[_ >> _]) with (F[σ']⟨↑⟩) by (unfold ρ'; now bsimpl).
          eapply tm_ne_conv; [apply tm_ne_rel; now eapply escape, vF| |].
          -- replace F[σ']⟨↑⟩ with F[σ']⟨@wk1 Δ F[σ]⟩ by (now bsimpl).
             apply wft_wk; [|now eapply escape, vF].
             now eapply wfc_ty.
          -- do 2 erewrite <- wk1_ren_on.
            apply convty_wk; [now eapply wfc_ty|].
            eapply escapeEq, vF; tea.
      + unshelve econstructor.
        * refine (wk1SubstSEq vΓ tΔ (domainTy tΔ vσ) vσ vσσ').
        * assert (ne : Ne[ Δ,, F[σ] |-[ ta ] tRel 0 : F[↑ >> (tRel 0 .: σ⟨@wk1 Δ F[σ]⟩)]]).
          { replace (F[_ >> _]) with (F[σ]⟨↑⟩) by (now bsimpl).
            apply tm_ne_rel; now eapply escape, vF. }
          cbn; eapply neuTermEq; try apply convneu_var; tea.
  Qed.

  Lemma PiRed {Δ σ} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > (tProd F G)[σ] ].
  Proof.
    cbn. eapply LRPi'. econstructor.
    - apply redtywf_refl.
      exact (wft_prod (domainTy tΔ vσ) (codomainTy tΔ vσ)).
    - exact (domainTy tΔ vσ).
    - exact (codomainTy tΔ vσ).
    - exact (convty_prod (domainTy tΔ vσ) (domainTyRefl tΔ vσ) (codomainTyRefl tΔ vσ)).
    - intros Δ' a b ρ tΔ'.
      refine (codomainSubstRedEq1 tΔ tΔ' ρ vσ).
  Defined.

  Lemma PiEqRed1 {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ])
    : [ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F G)[σ'] | PiRed tΔ vσ ].
  Proof.
    cbn. econstructor.
    - apply redtywf_refl.
      exact (wft_prod (domainTy tΔ vσ') (codomainTy tΔ vσ')).
    - cbn. eapply (prodTyEq tΔ vσ vσ' vσσ').
    - cbn. intros Δ' ρ tΔ'.
      eapply wkEq.
      refine (validTyExt vF tΔ vσ vσ' vσσ').
    - cbn. intros Δ' a ρ tΔ' ra.
      refine (codomainSubstRedEq2 _ _ _ vσ vσ' vσσ' ra).
  Defined.

  Lemma PiValid : [Γ ||-v< l > tProd F G | vΓ].
  Proof.
    unshelve econstructor.
    - intros Δ σ. eapply PiRed.
    - intros Δ σ σ'. eapply PiEqRed1.
  Defined.

End PiTyValidity.


Section PiTyCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G' l}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< l > F | vΓ ])
    (vG : [ Γ ,, F ||-v< l > G | validSnoc vΓ vF ])
    (vF' : [ Γ ||-v< l > F' | vΓ ])
    (vG' : [ Γ ,, F' ||-v< l > G' | validSnoc vΓ vF' ])
    (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ])
    (vGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc vΓ vF | vG ]).

  Lemma PiEqRed2 {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F' G')[σ] | validTy (PiValid vΓ vF vG) tΔ vσ ].
  Proof.
    econstructor.
    - apply redtywf_refl.
      exact (wft_prod (domainTy vΓ vF' tΔ vσ) (codomainTy vΓ vF' vG' tΔ vσ)).
    - cbn. fold subst_term.
      refine (convty_prod (domainTy vΓ vF tΔ vσ) _ _).
      + eapply escapeEq. eapply (validTyEq vFF' tΔ vσ).
      + eapply escapeEq. unshelve eapply (validTyEq vGG').
        2: unshelve eapply liftSubstS' ; tea.
    - intros Δ' ρ tΔ'. cbn. fold subst_term.
      eapply wkEq. eapply (validTyEq vFF').
    - intros Δ' a ρ tΔ' ra. cbn. fold subst_term.
      eapply LRTyEqIrrelevant' with (A := G[a .: σ⟨ρ⟩]) ; tea.
      + symmetry. eapply eq_subst_2.
      + rewrite eq_subst_2. unshelve eapply (validTyEq vGG') ; tea.
        refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _).
        irrelevance.
  Qed.

  Lemma PiCong : [ Γ ||-v< l > tProd F G ≅ tProd F' G' | vΓ | PiValid vΓ vF vG ].
  Proof.
    econstructor. intros Δ σ. eapply PiEqRed2.
  Qed.

End PiTyCongruence.


Section PiTmValidity.

  Context `{GenericTypingProperties}.
  Context {Γ F G} (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< one > F | vΓ ])
    (vU : [ Γ ,, F ||-v< one > U | validSnoc vΓ vF ])
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ])
    (vGU : [ Γ ,, F ||-v< one > G : U | validSnoc vΓ vF | vU ]).

  Lemma domainRedU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< one > F[σ] : U | validTy (UValid vΓ) tΔ vσ ].
  Proof.
    exact (validTm vFU tΔ vσ).
  Defined.

  Lemma domainTmU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ |-[ ta ] F[σ] : U ].
  Proof.
    eapply escapeTerm.
    now eapply domainRedU.
    Unshelve. all: tea.
  Defined.

  Lemma domainTmReflU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ |-[ ta ] F[σ] ≅ F[σ] : U ].
  Proof.
    refine (escapeEqTerm (validTy (UValid vΓ) tΔ vσ) _).
    eapply LREqTermRefl_. now eapply domainRedU.
  Qed.

  Lemma codomainRedU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, F[σ] ||-< one > G[ up_term_term σ ] : U | validTy vU _ (liftSubstS' vF vσ) ].
  Proof.
    refine (validTm vGU _ (liftSubstS' vF vσ)).
  Qed.

  Lemma codomainTmU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, F[σ] |-[ ta ] G[ up_term_term σ ] : U ].
  Proof.
    eapply escapeTerm.
    now eapply codomainRedU.
    Unshelve. all: tea.
  Qed.

  Lemma codomainTmReflU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, F[σ] |-[ ta ] G[ up_term_term σ ] ≅ G[ up_term_term σ ] : U].
  Proof.
    refine (escapeEqTerm (validTy vU _ (liftSubstS' vF vσ)) _).
    eapply LREqTermRefl_. now eapply codomainRedU.
  Qed.

  Lemma prodTyEqU {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
    : [Δ |-[ ta ] tProd F[σ] G[up_term_term σ] ≅ tProd F[σ'] G[up_term_term σ'] : U].
  Proof.
    assert ([Δ,, F[σ] |-[ ta ] tRel 0 : F[↑ >> (tRel 0 .: σ⟨@wk1 Δ F[σ]⟩)]]).
    { replace (F[_ >> _]) with (F[σ]⟨S⟩) by (now bsimpl).
      refine (ty_var (wfc_cons tΔ (domainTy vΓ vF _ vσ)) (in_here _ _)). }
    assert ([Δ,, F[σ] |-[ ta ] F[↑ >> (tRel 0 .: σ⟨@wk1 Δ F[σ]⟩)]]).
    { replace (F[_ >> _]) with (F[σ]⟨@wk1 Δ F[σ]⟩) by (now bsimpl).
      apply wft_wk; [now eapply wfc_ty|].
      now eapply escape, vF. }
    assert ([ Δ,, F[σ] |-[ ta ] tRel 0 : F[↑ >> (tRel 0 .: σ'⟨@wk1 Δ F[σ']⟩)]]).
    { eapply ty_conv; [tea|].
      eapply (domainTyEq vΓ vF tΔ vσ vσ' vσσ'). }
    assert (Ne[ Δ,, F[σ] |-[ ta ] tRel 0 : F[↑ >> (tRel 0 .: σ'⟨@wk1 Δ F[σ']⟩)]]).
    { eapply tm_ne_conv; [eapply tm_ne_rel| |].
      - pose proof vF as [vF0 _].
        unshelve (eapply escape; eapply vF0, vσ).
      - replace (F[_ >> _]) with (F[σ']⟨@wk1 Δ F[σ]⟩) by (now bsimpl).
        apply wft_wk; [now eapply wfc_ty|].
        now eapply escape, vF.
      - replace (F[_ >> _]) with (F[σ']⟨↑⟩) by (now bsimpl).
      do 2 erewrite <- wk1_ren_on.
      apply convty_wk; [eapply wfc_ty; tea|].
      eapply escapeEq, vF; tea. }
    refine (convtm_prod (domainTmU tΔ vσ) _ _).
    - eapply escapeEqTerm. eapply (validTmExt vFU tΔ vσ vσ' vσσ').
    - rewrite (eq_subst_1 F G Δ σ). rewrite (eq_subst_1 F G Δ σ').
      eapply escapeEqTerm. unshelve refine (validTmExt vGU _ _ _ _).
      + eapply wfc_cons. easy. refine (domainTy vΓ vF tΔ vσ).
      + refine (liftSubstS vΓ tΔ vF vσ).
      + unshelve econstructor.
        * refine (wk1SubstS vΓ tΔ (domainTy vΓ vF tΔ vσ) vσ').
        * cbn. eapply neuTerm; try apply convneu_var; tea.
      + unshelve econstructor.
        * refine (wk1SubstSEq vΓ tΔ (domainTy vΓ vF tΔ vσ) vσ vσσ').
        * cbn. eapply neuTermEq; try eapply convneu_var; tea.
          all: eapply tm_ne_conv; [|eassumption|symmetry; eapply (domainTyEq vΓ vF tΔ vσ vσ' vσσ')].
          all: assumption.
  Qed.

  Lemma PiRedU {Δ σ}
    (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< one > (tProd F G)[σ] : U | validTy (UValid vΓ) tΔ vσ ].
  Proof.
    econstructor.
    - apply redtmwf_refl ; cbn.
      refine (ty_prod (domainTmU tΔ vσ) (codomainTmU tΔ vσ)).
    - cbn; constructor.
    - cbn; apply tm_nf_prod.
      + assert (HF := validTm vFU tΔ vσ); now apply reifyTerm in HF.
      + assert (vρ := liftSubstS vΓ tΔ vF vσ).
        assert (HG := validTm vGU _ vρ).
        apply reifyTerm in HG.
        erewrite eq_subst_1; apply HG.
    - cbn. eapply (convtm_prod (domainTmU tΔ vσ) (domainTmReflU tΔ vσ) (codomainTmReflU tΔ vσ)).
    - cbn. unshelve refine (LRCumulative (PiRed _ _ _ tΔ vσ)).
      refine (univValid _ _ vFU).
      eapply (irrelevanceValidity (validSnoc vΓ vF) _).
      refine (univValid _ _ vGU).
  Defined.

  Lemma PiValidU : [ Γ ||-v< one > tProd F G : U | vΓ | UValid vΓ ].
  Proof.
    econstructor.
    - intros Δ σ tΔ vσ.
      exact (PiRedU tΔ vσ).
    - intros Δ σ σ' tΔ vσ vσ' vσσ'.
      pose proof (univValid (l' := zero) _ _ vFU) as VF0.
      pose proof (irrelevanceValidity (validSnoc vΓ vF)
                    (validSnoc (l := zero) vΓ VF0)
                    (univValid (l' := zero) _ _ vGU)) as VG0.
      unshelve econstructor ; cbn.
      + exact (PiRedU tΔ vσ).
      + exact (PiRedU tΔ vσ').
      + exact (LRCumulative (PiRed vΓ VF0 VG0 tΔ vσ)).
      + exact (prodTyEqU tΔ vσ vσ' vσσ').
      + exact (LRCumulative (PiRed vΓ VF0 VG0 tΔ vσ')).
      + pose proof (PiEqRed1 vΓ VF0 VG0 tΔ vσ vσ' vσσ').
        irrelevanceCum.
  Qed.

End PiTmValidity.


Section PiTmCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G'}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< one > F | vΓ ])
    (vU : [ Γ ,, F ||-v< one > U | validSnoc vΓ vF ])
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ])
    (vGU : [ Γ ,, F ||-v< one > G : U | validSnoc vΓ vF | vU ])
    (vF' : [ Γ ||-v< one > F' | vΓ ])
    (vU' : [ Γ ,, F' ||-v< one > U | validSnoc vΓ vF' ])
    (vF'U : [ Γ ||-v< one > F' : U | vΓ | UValid vΓ ])
    (vG'U : [ Γ ,, F' ||-v< one > G' : U | validSnoc vΓ vF' | vU' ])
    (vFF' : [ Γ ||-v< one > F ≅ F' : U | vΓ | UValid vΓ ])
    (vGG' : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc vΓ vF | vU ]).

  Lemma PiCongTm : [ Γ ||-v< one > tProd F G ≅ tProd F' G' : U | vΓ | UValid vΓ ].
  Proof.
    econstructor.
    intros Δ σ tΔ vσ.
    pose proof (univValid (l' := zero) _ _ vFU) as vF0.
    pose proof (irrelevanceValidity (validSnoc vΓ vF)
                  (validSnoc (l := zero) vΓ vF0)
                  (univValid (l' := zero) _ _ vGU)) as vG0.
    pose proof (univValid (l' := zero) _ _ vF'U) as vF'0.
    pose proof (irrelevanceValidity (validSnoc vΓ vF')
                  (validSnoc (l := zero) vΓ vF'0)
                  (univValid (l' := zero) _ _ vG'U)) as vG'0.
    unshelve econstructor ; cbn.
    - exact (PiRedU vΓ vF vU vFU vGU tΔ vσ).
    - exact (PiRedU vΓ vF' vU' vF'U vG'U tΔ vσ).
    - exact (LRCumulative (PiRed vΓ vF0 vG0 tΔ vσ)).
    - cbn. refine (convtm_prod (domainTmU vΓ vFU tΔ vσ) _ _).
      + eapply escapeEqTerm. eapply (validTmEq vFF' tΔ vσ).
      + eapply escapeEqTerm. unshelve eapply (validTmEq vGG').
        2: unshelve eapply liftSubstS' ; tea.
    - exact (LRCumulative (PiRed vΓ vF'0 vG'0 tΔ vσ)).
    - enough ([ Δ ||-< zero > (tProd F G)[σ] ≅ (tProd F' G')[σ] | PiRed vΓ vF0 vG0 tΔ vσ]) by irrelevanceCum.
      refine (PiEqRed2 vΓ vF0 vG0 vF'0 vG'0 _ _ tΔ vσ).
      + exact (univEqValid vΓ (UValid vΓ) vF0 vFF').
      + pose proof (univEqValid (validSnoc vΓ vF) vU (univValid (l' := zero) _ _ vGU) vGG') as vGG'0.
        refine (irrelevanceEq _ _ _ _ vGG'0).
  Qed.

End PiTmCongruence.


Section FuncTyValidity.

  Context `{GenericTypingProperties}.

  Lemma FunValid {Γ F G l}
      (vΓ : [||-v Γ])
      (vF : [ Γ ||-v< l > F | vΓ ])
      (vG : [ Γ ||-v< l > G | vΓ ])
    : [ Γ ||-v< l > tProd F (G⟨@wk1 Γ F⟩) | vΓ ].
  Proof.
    unshelve eapply PiValid ; tea.
    eapply wk1ValidTy. eassumption.
  Defined.

End FuncTyValidity.


Section FuncTyCongruence.

  Context `{GenericTypingProperties}.

  Lemma FunCong {Γ F G F' G' l}
      (vΓ : [||-v Γ])
      (vF : [ Γ ||-v< l > F | vΓ ])
      (vG : [ Γ ||-v< l > G | vΓ ])
      (vF' : [ Γ ||-v< l > F' | vΓ ])
      (vG' : [ Γ ||-v< l > G' | vΓ ])
      (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ])
      (vGG' : [ Γ ||-v< l > G ≅ G' | vΓ | vG ])
    : [ Γ ||-v< l > tProd F (G⟨@wk1 Γ F⟩) ≅ tProd F' (G'⟨@wk1 Γ F'⟩) | vΓ | FunValid vΓ vF vG ].
  Proof.
    unshelve eapply PiCong ; tea.
    - eapply wk1ValidTy. eassumption.
    - replace (G'⟨@wk1 Γ F'⟩) with (G'⟨@wk1 Γ F⟩) by (now bsimpl).
      eapply wk1ValidTyEq. eassumption.
  Qed.

End FuncTyCongruence.
