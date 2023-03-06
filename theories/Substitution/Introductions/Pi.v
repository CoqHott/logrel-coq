From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Universe.

(* Set Universe Polymorphism. *)

Lemma eq_subst_1 F na G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ na F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.

Section PiTyValidity.

  Context `{GenericTypingProperties}.
  Universe i j k l m n o p.
  (* i j k l are the universe levels of the hypotheses *)
  (* m n o p are the universe levels of the conclusions *)
  Context {l Γ na F G} (vΓ : [VR@{i j k l} | ||-v Γ])
    (* (vF : typeValidity@{k m n o p} Γ vΓ l F) *)
    (* (vF' : typeValidity@{k i j k l} Γ vΓ l F) *)
    (vF : [Γ ||-v< l > F | vΓ ])
    (* (vG : typeValidity@{k m n o p} *)
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
    eapply (validTyExt vF).
    refine (wk1SubstS _ _ (domainTy tΔ vσ) vσ').
    refine (wk1SubstSEq _ _ (domainTy tΔ vσ) vσ vσσ').
  Qed.


  Lemma codomainRed {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ,, vass na F[σ] ||-< l > G[ up_term_term σ ] ].
  Proof.
    rewrite (eq_subst_1 F na G Δ σ).
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
    : [Δ |-[ ta ] tProd na F[σ] G[up_term_term σ] ≅ tProd na F[σ'] G[up_term_term σ']].
  Proof.
    refine (convty_prod I (domainTy tΔ vσ) _ _).
    - eapply escapeEq_. eapply (validTyExt vF tΔ vσ vσ' vσσ').
    - rewrite (eq_subst_1 F na G Δ σ). rewrite (eq_subst_1 F na G Δ σ').
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

  Lemma PiRed {Δ σ} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > (tProd na F G)[σ] ].
  Proof.
    cbn. eapply LRPi'. econstructor.
    - apply redtywf_refl.
      exact (wft_prod (domainTy tΔ vσ) (codomainTy tΔ vσ)).
    - exact (domainTy tΔ vσ).
    - exact (codomainTy tΔ vσ).
    - exact (convty_prod I (domainTy tΔ vσ) (domainTyRefl tΔ vσ) (codomainTyRefl tΔ vσ)).
    - intros Δ' a b ρ tΔ'.
      refine (codomainSubstRedEq1 tΔ tΔ' ρ vσ).
  Defined.

  Lemma PiValid : [Γ ||-v< l > tProd na F G | vΓ].
  Proof.
    unshelve econstructor.
    - intros Δ σ tΔ vσ. eapply PiRed ; tea.
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
  Defined.

End PiTyValidity.


Section PiTyCongruence.

  Context `{GenericTypingProperties}.

  Lemma PiCong {Γ F nF G F' nF' G' l}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< l > F | vΓ ])
    (vG : [ Γ ,, vass nF F ||-v< l > G | validSnoc nF vΓ vF ])
    (vF' : [ Γ ||-v< l > F' | vΓ ])
    (vG' : [ Γ ,, vass nF' F' ||-v< l > G' | validSnoc nF' vΓ vF' ])
    (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ])
    (vGG' : [ Γ ,, vass nF F ||-v< l > G ≅ G' | validSnoc nF vΓ vF | vG ])
    : [ Γ ||-v< l > tProd nF F G ≅ tProd nF' F' G' | vΓ | PiValid vΓ vF vG ].
  Proof.
    econstructor. intros Δ σ tΔ vσ. econstructor.
    - apply redtywf_refl.
      exact (wft_prod (domainTy vΓ vF' tΔ vσ) (codomainTy vΓ vF' vG' tΔ vσ)).
    - cbn. fold subst_term.
      refine (convty_prod I (domainTy vΓ vF tΔ vσ) _ _).
      + eapply escapeEq_. eapply (validTyEq vFF' tΔ vσ).
      + eapply escapeEq_. unshelve eapply (validTyEq vGG').
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

End PiTyCongruence.


Section PiTmValidity.

  Context `{GenericTypingProperties}.

  Lemma PiValidTm {Γ F nF G}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< one > F | vΓ ])
    (vU : [ Γ ,, vass nF F ||-v< one > U | validSnoc nF vΓ vF ])
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ])
    (vGU : [ Γ ,, vass nF F ||-v< one > G : U | validSnoc nF vΓ vF | vU ])
    : [ Γ ||-v< one > tProd nF F G : U | vΓ | UValid vΓ ].
  Proof.
    (* unshelve econstructor. *)
    (* - intros Δ σ tΔ vσ. econstructor. *)
    (*   + apply redtmwf_refl. admit. *)
    (*   + constructor. *)
    (*   + admit. *)
    (*   + cbn. Set Printing Universes. Check PiRed. refine (PiRed _ _ _ tΔ vσ). *)
  Admitted.

End PiTmValidity.


Section PiTmCongruence.

  Context `{GenericTypingProperties}.

  Lemma PiCongTm {Γ F nF G F' nF' G'}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< one > F | vΓ ])
    (vU : [ Γ ,, vass nF F ||-v< one > U | validSnoc nF vΓ vF ])
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ])
    (vGU : [ Γ ,, vass nF F ||-v< one > G : U | validSnoc nF vΓ vF | vU ])
    (vF' : [ Γ ||-v< one > F' | vΓ ])
    (vU' : [ Γ ,, vass nF' F' ||-v< one > U | validSnoc nF' vΓ vF' ])
    (vF'U : [ Γ ||-v< one > F' : U | vΓ | UValid vΓ ])
    (vG'U : [ Γ ,, vass nF' F' ||-v< one > G' : U | validSnoc nF' vΓ vF' | vU' ])
    (vFF' : [ Γ ||-v< one > F ≅ F' : U | vΓ | UValid vΓ ])
    (vGG' : [ Γ ,, vass nF F ||-v< one > G ≅ G' : U | validSnoc nF vΓ vF | vU ])
    : [ Γ ||-v< one > tProd nF F G ≅ tProd nF' F' G' : U | vΓ | UValid vΓ ].
  Proof.
  Admitted.

End PiTmCongruence.


Section FuncTyValidity.

  Context `{GenericTypingProperties}.

  Lemma FunValid {Γ F nF G l}
      (vΓ : [||-v Γ])
      (vF : [ Γ ||-v< l > F | vΓ ])
      (vG : [ Γ ||-v< l > G | vΓ ])
    : [ Γ ||-v< l > tProd nF F (G⟨@wk1 Γ nF F⟩) | vΓ ].
  Proof.
    unshelve eapply PiValid ; tea.
    eapply wk1ValidTy. eassumption.
  Defined.

End FuncTyValidity.


Section FuncTyCongruence.

  Context `{GenericTypingProperties}.

  Lemma FunCong {Γ F nF G F' nF' G' l}
      (vΓ : [||-v Γ])
      (vF : [ Γ ||-v< l > F | vΓ ])
      (vG : [ Γ ||-v< l > G | vΓ ])
      (vF' : [ Γ ||-v< l > F' | vΓ ])
      (vG' : [ Γ ||-v< l > G' | vΓ ])
      (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ])
      (vGG' : [ Γ ||-v< l > G ≅ G' | vΓ | vG ])
    : [ Γ ||-v< l > tProd nF F (G⟨@wk1 Γ nF F⟩) ≅ tProd nF' F' (G'⟨@wk1 Γ nF' F'⟩) | vΓ | FunValid vΓ vF vG ].
  Proof.
    unshelve eapply PiCong ; tea.
    - eapply wk1ValidTy. eassumption.
    - replace (G'⟨@wk1 Γ nF' F'⟩) with (G'⟨@wk1 Γ nF F⟩) by (now bsimpl).
      eapply wk1ValidTyEq. eassumption.
  Qed.

End FuncTyCongruence.
