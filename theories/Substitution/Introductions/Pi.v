From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Universe Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.

Section PiValidity.
  Context `{GenericTypingProperties}.

  Lemma TypeRedWf_refl {Γ} {A} : [ Γ |-[ ta ] A ] -> [ Γ |-[ ta ] A :⇒*: A ].
  Proof.
    intro h. econstructor.
    - assumption.
    - assumption.
    - now apply redty_refl.
  Defined.

  Lemma reflSubst {Γ} (VΓ : [||-v Γ]) : forall {σ Δ} (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
  [Δ ||-v σ ≅ σ : Γ | VΓ | wfΔ | Vσ].
  Admitted.

  Lemma convTerm {Γ A B t l l'} (rA : [ Γ ||-< l > A ]) (rB : [ Γ ||-< l' > B ])
    : [ Γ ||-< l >  A ≅ B | rA ] -> [ Γ ||-< l >  t : A | rA ] -> [ Γ ||-< l' > t : B | rB ].
  Admitted.

  Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  whne n ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
  Admitted.

  Lemma PiValid {l Γ na F G} (vΓ : [||-v Γ])
    (vF : [Γ ||-v< l > F | vΓ])
    (vG : [Γ ,, vass na F ||-v< l > G | validSnoc na vΓ vF])
    : [Γ ||-v< l > tProd na F G | vΓ].
  Proof.
    assert (forall Δ σ, G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ na F[σ] ⟩]) as substlemma1. {
      intros. now bsimpl.
    }
    assert (forall σ ρ a, G[a .: σ⟨ρ⟩] = G[up_term_term σ][a .: ρ >> tRel]) as substlemma2. {
      intros. bsimpl. now substify.
    }
    pose (rF := fun Δ σ => validTy (Δ := Δ) (σ := σ) vF).
    pose proof (tF := fun Δ σ tΔ vσ => escape_ (rF Δ σ tΔ vσ)).
    pose proof (tFrefl := fun Δ σ tΔ vσ => escapeEq_ _ (LRTyEqRefl_ (rF Δ σ tΔ vσ))).
    assert (forall Δ σ (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ]),
               [ Δ ,, vass na F[σ] ||-< l > G[ up_term_term σ ] ]) as rG. {
      intros. rewrite (substlemma1 Δ).
      refine (validTy vG _ (liftSubstS vΓ tΔ vF vσ)).
    }
    pose proof (tG := fun Δ σ tΔ vσ => escape_ (rG Δ σ tΔ vσ)).
    pose proof (tGrefl := fun Δ σ tΔ vσ => escapeEq_ _ (LRTyEqRefl_ (rG Δ σ tΔ vσ))).
    assert (forall Δ Δ' σ a  (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ'])
                   (ρ : Δ' ≤ Δ) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
                   (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (rF Δ σ tΔ vσ)]),
               [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]]) as rGa'. {
      intros. rewrite <- substlemma2.
      eapply (validTy vG).
      refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _).
      irrelevance.
    }
    assert (forall Δ Δ' σ a b (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ'])
                   (ρ : Δ' ≤ Δ) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
                   (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (rF Δ σ tΔ vσ)])
                   (rb : [ Δ' ||-< l > b : F[σ]⟨ρ⟩ | wk ρ tΔ' (rF Δ σ tΔ vσ)])
                   (rab : [ Δ' ||-< l > a ≅ b : F[σ]⟨ρ⟩ | wk ρ tΔ' (rF Δ σ tΔ vσ)]),
               [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]
                              ≅ G[up_term_term σ][b .: ρ >> tRel] | rGa' Δ Δ' σ a tΔ tΔ' ρ vσ ra]) as rGext. {
      intros. eapply LRTyEqIrrelevant'.
      - apply substlemma2.
      - rewrite <- substlemma2.
        unshelve eapply (validTyExt vG tΔ' _ _ _).
        + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
        + refine (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF _). irrelevance.
        + unshelve econstructor.
          * eapply reflSubst.
          * cbn. irrelevance.
    }
    assert (forall Δ Δ' σ σ' a (tΔ : [ |-[ ta ] Δ]) (tΔ' : [ |-[ ta ] Δ']) (ρ : Δ' ≤ Δ)
                   (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
                   (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
                   (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ ])
                   (ra : [ Δ' ||-< l > a : F[σ]⟨ρ⟩ | wk ρ tΔ' (rF Δ σ tΔ vσ)]),
               [Δ' ||-< l > G[up_term_term σ][a .: ρ >> tRel]
                              ≅ G[up_term_term σ'][a .: ρ >> tRel] | rGa' Δ Δ' σ a tΔ tΔ' ρ vσ ra]) as rGext2. {
      intros. eapply LRTyEqIrrelevant'.
      apply substlemma2. rewrite <- substlemma2.
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
    }
    unshelve econstructor.
    - intros Δ σ tΔ vσ. cbn.
      unshelve eapply LRPi_.
      + econstructor.
        * apply TypeRedWf_refl.
          exact (wft_prod (tF _ _ tΔ vσ) (tG _ _ tΔ vσ)).
        * exact (tF _ _ tΔ vσ).
        * exact (tG _ _ tΔ vσ).
        * exact (convty_prod I (tF _ _ tΔ vσ) (tFrefl _ _ tΔ vσ) (tGrefl _ _ tΔ vσ)).
        Unshelve.
        ** intros Δ' ρ tΔ'.
           exact (wk ρ tΔ' (rF Δ σ tΔ vσ)).
        ** intros Δ' a ρ tΔ' ra.
           eapply rGa'. exact ra.
        * cbn. intros Δ' a b ρ tΔ' ra rb rab.
          eapply rGext. exact rb. exact rab.
      + econstructor.
        * cbn. intros Δ' ρ tΔ'.
          eapply (wk ρ tΔ' (rF Δ σ tΔ vσ)).
        * cbn. intros Δ' a ρ tΔ' ra.
          eapply rGa'.
    - intros Δ σ σ' tΔ vσ vσ' vσσ'. cbn.
      econstructor.
      + apply TypeRedWf_refl.
        exact (wft_prod (tF _ _ tΔ vσ') (tG _ _ tΔ vσ')).
      + cbn. refine (convty_prod I (tF _ _ tΔ vσ) _ _).
        * eapply escapeEq_. eapply (validTyExt vF tΔ vσ vσ' vσσ').
        * rewrite (substlemma1 Δ).
          replace (G[up_term_term σ']) with (G[tRel 0 .: σ'⟨@wk1 Δ na F[σ]⟩]).
          2:now bsimpl.
          eapply escapeEq_. unshelve refine (validTyExt vG _ _ _ _).
          ** now eapply wfc_cons.
          ** unshelve econstructor.
             *** refine (wk1SubstS vΓ tΔ (tF Δ σ tΔ vσ) vσ).
             *** cbn. admit.
          ** unshelve econstructor.
             *** refine (wk1SubstS vΓ tΔ (tF Δ σ tΔ vσ) vσ').
             *** cbn. (* some neutral manipulation *) admit.
          ** unshelve econstructor.
             *** refine (wk1SubstSEq vΓ tΔ (tF Δ σ tΔ vσ) vσ vσσ').
             *** cbn.  (* some neutral manipulation *) admit.
      + cbn. intros Δ' ρ tΔ'.
        eapply wkEq.
        refine (validTyExt vF tΔ vσ vσ' vσσ').
      + cbn. intros Δ' a ρ tΔ' ra.
        refine (rGext2 _ _ _ _ _ _ _ _ vσ vσ' vσσ' ra).
  Admitted.

End PiValidity.
