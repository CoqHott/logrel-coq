From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedValues Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Universe.

Set Universe Polymorphism.

Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.

  Set Printing Primitive Projection Parameters.

Section PolyValidity.

  Context `{GenericTypingProperties}.

  Lemma polyRedId {Γ l F G} : PolyRed Γ l F G -> [Γ ||-<l> F] × [Γ ,, F ||-<l> G].
  Proof.
    intros [?? RF RG]; split.
    -  rewrite <- (wk_id_ren_on Γ F). eapply RF; gen_typing.
    - replace G with G[tRel 0 .: @wk1 Γ F >> tRel].
      2: bsimpl; rewrite scons_eta'; now asimpl.
      eapply RG. eapply var0; tea; now bsimpl.
      Unshelve. gen_typing.
  Qed.

  Lemma polyRedEqId {Γ l F F' G G'} (PFG : PolyRed Γ l F G) (RFG := polyRedId PFG) :
    PolyRedEq PFG F' G' -> [Γ ||-<l> F ≅ F' | fst RFG] × [Γ ,, F ||-<l> G ≅ G' | snd RFG].
  Proof.
    intros [RFF' RGG']; destruct RFG; escape; split.
    - rewrite <- (wk_id_ren_on Γ F'); irrelevance0.
      2: unshelve eapply RFF'; gen_typing.
      apply wk_id_ren_on.
    - replace G' with G'[tRel 0 .: @wk1 Γ F >> tRel].
      2: bsimpl; rewrite scons_eta'; now asimpl.
      irrelevance0.
      2: eapply RGG'.
      bsimpl; rewrite scons_eta'; now asimpl.
      Unshelve. 1: gen_typing.
      eapply var0; tea; now bsimpl.
  Qed.

  Context {l Γ F G} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ,, F ||-v< l > G | validSnoc VΓ VF]).

  Context {Δ σ} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : _ | tΔ]).
  
  Lemma substPolyRed : PolyRed Δ l F[σ] G[up_term_term σ].
  Proof.
    pose proof (Vuσ := liftSubstS' VF Vσ).
    instValid Vσ; instValid Vuσ; escape.
    unshelve econstructor; tea.
    - intros; now eapply wk.
    - cbn; intros ?? ρ wfΔ' ha.
      rewrite eq_subst_2.
      pose proof (Vawkσ := consWkSubstS VF ρ wfΔ' Vσ ha).
      now instValid Vawkσ.
    - cbn; intros ??? ρ wfΔ' ha hb hab.
      irrelevance0; rewrite eq_subst_2.
      1: reflexivity.
      pose proof (Vawkσ := consWkSubstS VF ρ wfΔ' Vσ ha).
      pose proof (Vbwkσ := consWkSubstS VF ρ wfΔ' Vσ hb).
      epose proof (Vabwkσ := consWkSubstSEq' VF Vσ (reflSubst _ _ Vσ) ρ wfΔ' ha hab).
      now instAllValid Vawkσ Vbwkσ Vabwkσ.
  Qed.

  Lemma substEqPolyRedEq {F' G'} (VF' : [Γ ||-v< l > F' | VΓ ])
    (VG' : [Γ ,, F' ||-v< l > G' | validSnoc VΓ VF'])
    (VFF' : [Γ ||-v< l > F ≅ F' | VΓ | VF])
    (VGG' : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF | VG])
    : PolyRedEq substPolyRed F'[σ] G'[up_term_term σ].
  Proof.
    instValid Vσ.
    unshelve econstructor.
    - intros; irrelevanceRefl; now unshelve eapply wkEq.
    - intros ?? ρ wfΔ' ha; irrelevance0; rewrite eq_subst_2.
      1: reflexivity.
      unshelve epose proof (Vabwkσ := consWkSubstSEq' VF Vσ (reflSubst _ _ Vσ) ρ wfΔ' ha _).
      2: now eapply LREqTermRefl_.
      unshelve eapply validTyEq; cycle 2; tea. 
      now eapply consWkSubstS.
  Qed.

  Context {σ'} (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ]) (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ]).

  Lemma substPolyRedEq : PolyRedEq substPolyRed F[σ'] G[up_term_term σ'].
  Proof.
    instAllValid Vσ Vσ' Vσσ'.
    unshelve econstructor.
    - intros; irrelevanceRefl; now eapply wkEq.
    - intros ?? ρ wfΔ' ha; irrelevance0; rewrite eq_subst_2.
      1: reflexivity.
      unshelve epose proof (Vabwkσ := consWkSubstSEq' VF Vσ Vσσ' ρ wfΔ' ha _).
      2: now eapply LREqTermRefl_.
      eapply validTyExt; tea.
      eapply consWkSubstS; tea.
      eapply LRTmRedConv; tea.
      irrelevanceRefl; now eapply wkEq.
      Unshelve. 1,3,5: tea. now eapply wk.
  Qed.

End PolyValidity.


