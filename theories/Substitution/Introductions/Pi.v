From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.

Section PiValidity.
  Context `{GenericTypingProperties}.

  Lemma convTerm {Γ A B t l l'} (rA : [ Γ ||-< l > A ]) (rB : [ Γ ||-< l' > B ])
    : [ Γ ||-< l >  A ≅ B | rA ] -> [ Γ ||-< l >  t : A | rA ] -> [ Γ ||-< l' > t : B | rB ].
  Admitted.

  Context {l Γ na F G} (vΓ : [||-v Γ])
    (vF : [Γ ||-v< l > F | vΓ])
    (vG : [Γ ,, vass na F ||-v< l > G | validSnoc na vΓ vF]).

  Lemma domainRed {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > F[σ] ].
  Proof.
    exact (validTy vF tΔ vσ).
  Defined.

  Lemma domainTy {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ |-[ ta ] F[σ] ].
  Proof.
    eapply escape_.
    now eapply domainRed.
  Defined.

  Lemma domainTyRefl {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ |-[ ta ] F[σ] ≅ F[σ] ].
  Proof.
    refine (escapeEq_ (domainRed tΔ vσ) _).
    now eapply LRTyEqRefl_.
  Qed.

  Lemma domainTyEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
    : [Δ,, vass na F[σ] |-[ ta ] F[σ⟨@wk1 Δ na F[σ]⟩] ≅ F[σ'⟨@wk1 Δ na F[σ]⟩]].
  Proof.
    eapply escapeEq_.
    refine (validTyExt vF _ _ _ _).
    refine (wk1SubstS _ _ (domainTy tΔ vσ) vσ').
    refine (wk1SubstSEq _ _ (domainTy tΔ vσ) vσ vσσ').
  Qed.


  Lemma codomainRed {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, vass na F[σ] ||-< l > G[ up_term_term σ ] ].
  Proof.
    replace (G[up_term_term σ]) with (G[tRel 0 .: σ⟨ @wk1 Δ na F[σ] ⟩]) by (now bsimpl).
    refine (validTy vG _ (liftSubstS vΓ tΔ vF vσ)).
  Qed.

  Lemma codomainTy {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, vass na F[σ] |-[ ta ] G[ up_term_term σ ] ].
  Proof.
    eapply escape_.
    now eapply codomainRed.
  Qed.

  Lemma codomainTyRefl {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, vass na F[σ] |-[ ta ] G[ up_term_term σ ] ≅ G[ up_term_term σ ]].
  Proof.
    refine (escapeEq_ (codomainRed tΔ vσ) _).
    now eapply LRTyEqRefl_.
  Qed.

  Lemma codomainSubstRed {Δ Δ' σ a} (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ'])
    (ρ : Δ' ≤ Δ) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (domainRed tΔ vσ)])
    : [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]].
  Proof.
    replace (G[_][_]) with (G[a .: σ⟨ρ⟩]) by (bsimpl ; now substify).
    eapply (validTy vG).
    refine (consSubstS _ _ (wkSubstS vΓ tΔ tΔ' ρ vσ) _ _).
    irrelevance.
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
    - bsimpl ; now substify.
    - replace (G[_][_]) with (G[b .: σ⟨ρ⟩]) by (bsimpl ; now substify).
      unshelve eapply (validTyExt vG tΔ' _ _ _).
      + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
      + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
      + unshelve econstructor.
        * eapply reflSubst.
        * cbn. irrelevance.
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
      - bsimpl ; now substify.
      - replace (G[_][_]) with (G[a .: σ'⟨ρ⟩]) by (bsimpl ; now substify).
        unshelve eapply (validTyExt vG tΔ' _ _ _).
        + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
        + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ') vF _).
          refine (convTerm _ _ _ ra).
          replace (F[σ'⟨ρ⟩]) with (F[σ']⟨ρ⟩).
          refine (wkEq ρ tΔ' _ (validTyExt vF tΔ vσ vσ' vσσ')).
          now asimpl.
        + unshelve econstructor.
          * cbn. now eapply wkSubstSEq.
          * cbn. eapply LRTmEqIrrelevant'.
            2:refine (LREqTermRefl_ _ ra). now asimpl.
  Qed.

  Lemma prodTyEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
    : [Δ |-[ ta ] tProd na F[σ] G[up_term_term σ] ≅ tProd na F[σ'] G[up_term_term σ']].
  Proof.
    refine (convty_prod I (domainTy tΔ vσ) _ _).
    - eapply escapeEq_. eapply (validTyExt vF tΔ vσ vσ' vσσ').
    - replace (G[up_term_term σ]) with (G[tRel 0 .: σ⟨ @wk1 Δ na F[σ] ⟩]) by (now bsimpl).
      replace (G[up_term_term σ']) with (G[tRel 0 .: σ'⟨ @wk1 Δ na F[σ] ⟩]) by (now bsimpl).
      eapply escapeEq_. unshelve refine (validTyExt vG _ _ _ _).
      + eapply wfc_cons. easy. refine (domainTy tΔ vσ).
      + refine (liftSubstS vΓ tΔ vF vσ).
      + unshelve econstructor.
        * refine (wk1SubstS vΓ tΔ (domainTy tΔ vσ) vσ').
        * cbn. eapply neuTerm. constructor.
          2: refine (convneu_var _).
          all: eapply (ty_conv (A' := F[σ]⟨S⟩) (ty_var (wfc_cons na tΔ (domainTy _ vσ)) (in_here _ _))).
          all: replace (F[σ]⟨S⟩) with (F[σ⟨@wk1 Δ na F[σ]⟩]) by (now bsimpl).
          all: eapply (domainTyEq tΔ vσ vσ' vσσ').
      + unshelve econstructor.
        * refine (wk1SubstSEq vΓ tΔ (domainTy tΔ vσ) vσ vσσ').
        * cbn. eapply neuTermEq.
          1, 2: constructor.
          3: refine (convneu_var _).
          all: replace (F[_ >> _]) with (F[σ]⟨S⟩) by (now bsimpl).
          all: refine (ty_var (wfc_cons na tΔ (domainTy _ vσ)) (in_here _ _)).
  Qed.

  Lemma PiValid : [Γ ||-v< l > tProd na F G | vΓ].
  Proof.
    unshelve econstructor.
    - intros Δ σ tΔ vσ. cbn.
      unshelve eapply LRPi_.
      + econstructor.
        * apply redtywf_refl.
          exact (wft_prod (domainTy tΔ vσ) (codomainTy tΔ vσ)).
        * exact (domainTy tΔ vσ).
        * exact (codomainTy tΔ vσ).
        * exact (convty_prod I (domainTy tΔ vσ) (domainTyRefl tΔ vσ) (codomainTyRefl tΔ vσ)).
        Unshelve.
        ** intros Δ' ρ tΔ'.
           exact (wk ρ tΔ' (domainRed tΔ vσ)).
        ** intros Δ' a ρ tΔ' ra.
           eapply codomainSubstRed. exact ra.
        * intros Δ' a b ρ tΔ' ra rb rab.
          eapply codomainSubstRedEq1. exact rb. exact rab.
      + econstructor.
        * cbn. intros Δ' ρ tΔ'.
          eapply (wk ρ tΔ' (domainRed tΔ vσ)).
        * cbn. intros Δ' a ρ tΔ' ra.
          eapply codomainSubstRed.
    - intros Δ σ σ' tΔ vσ vσ' vσσ'. cbn.
      econstructor.
      + apply redtywf_refl.
        exact (wft_prod (domainTy tΔ vσ') (codomainTy tΔ vσ')).
      + cbn. eapply (prodTyEq tΔ vσ vσ' vσσ').
      + cbn. intros Δ' ρ tΔ'.
        eapply wkEq.
        refine (validTyExt vF tΔ vσ vσ' vσσ').
      + cbn. intros Δ' a ρ tΔ' ra.
        refine (codomainSubstRedEq2 _ _ _ vσ vσ' vσσ' ra).
  Qed.

End PiValidity.
