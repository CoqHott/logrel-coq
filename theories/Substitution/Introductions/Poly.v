From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedValues Weakening
  GenericTyping LogicalRelation Validity.
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

Lemma subst_wk_id_tail Γ P t : P[t .: @wk_id Γ >> tRel] = P[t..].
Proof. setoid_rewrite id_ren; now bsimpl. Qed.


Set Printing Primitive Projection Parameters.

Section PolyValidity.

  Context `{GenericTypingProperties}.

  Lemma mkPolyRed {Γ l A B} (wfΓ : [|-Γ])
    (RA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩]) 
    (RB : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> a : _ | RA Δ ρ wfΔ] -> [Δ ||-<l> B[a .: ρ >> tRel]])
    (RBext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (Ra : [Δ ||-<l> a : _ | RA Δ ρ wfΔ]),
      [Δ ||-<l> b : _ | RA Δ ρ wfΔ] ->
      [Δ ||-<l> a ≅ b : _ | RA Δ ρ wfΔ] -> [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a ρ wfΔ Ra]) :
    PolyRed Γ l A B.
  Proof.
    assert [Γ |- A] by (eapply escape; now eapply instKripke).
    unshelve econstructor; tea.
    unshelve epose proof (RB _ (tRel 0) (@wk1 Γ A) _ _).
    + gen_typing.
    + eapply var0; tea; now rewrite wk1_ren_on.
    + enough (B = B[tRel 0 .: @wk1 Γ A >> tRel]) as -> by now escape.
      setoid_rewrite wk1_ren; rewrite scons_eta'; now asimpl.
  Qed.

  Lemma mkPolyRed' {Γ l A B} (RA : [Γ ||-<l> A]) 
    (RB : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> a : _ | wk ρ wfΔ RA] -> [Δ ||-<l> B[a .: ρ >> tRel]])
    (RBext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (Ra : [Δ ||-<l> a : _ | wk ρ wfΔ RA]),
      [Δ ||-<l> b : _ | wk ρ wfΔ RA] ->
      [Δ ||-<l> a ≅ b : _ | wk ρ wfΔ RA] -> [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a ρ wfΔ Ra]) :
    PolyRed Γ l A B.
  Proof.
    unshelve eapply mkPolyRed; tea.
    escape; gen_typing.
  Qed.


  Lemma polyCodSubstRed {Γ l F G} (RF : [Γ ||-<l> F]) : 
    PolyRed Γ l F G -> forall t, [Γ ||-<l> t : _ | RF] -> [Γ ||-<l> G[t..]].
  Proof.
    intros PFG ??. 
    escape. assert (wfΓ : [|- Γ]) by gen_typing.
    erewrite <- subst_wk_id_tail.
    eapply (PolyRed.posRed PFG wk_id wfΓ).
    irrelevance.
  Qed.

  Lemma polyCodSubstExtRed {Γ l F G} (RF : [Γ ||-<l> F]) (PFG : PolyRed Γ l F G) (RG := polyCodSubstRed RF PFG) :
    forall t u (Rt : [Γ ||-<l> t : _ | RF]), [Γ ||-<l> u : _ | RF] -> [Γ ||-<l> t ≅ u : _ | RF] -> 
    [Γ ||-<l> G[t..] ≅ G[u..]| RG t Rt].
  Proof.
    intros. escape. assert (wfΓ : [|- Γ]) by gen_typing.
    irrelevance0; erewrite <- subst_wk_id_tail; [reflexivity|].
    unshelve eapply (PolyRed.posExt PFG wk_id wfΓ); irrelevance.
  Qed.  


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

  Lemma polyRedSubst {Γ l A B t} (PAB : PolyRed Γ l A B) 
    (Rt : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    (Rtext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] ≅ t[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    : PolyRed Γ l A B[t]⇑.
  Proof.
    destruct PAB; opector; tea.
    + intros; rewrite liftSubst_scons_eq.
      unshelve eapply posRed; tea; eapply Rt; now irrelevanceRefl.
    + unshelve epose proof (posRed _ t (@wk1 Γ A) _ _).
      - escape; gen_typing.
      - replace t with t[tRel 0 .: @wk1 Γ A >> tRel].
        2:{ bsimpl; rewrite scons_eta'; now asimpl. }
        eapply Rt.
        eapply var0; tea; now rewrite wk1_ren_on.
      - escape. 
        replace (B[_]) with B[t .: @wk1 Γ A >> tRel]; tea.
        now setoid_rewrite wk1_ren.
    + intros; irrelevance0; rewrite liftSubst_scons_eq;[reflexivity|].
      unshelve eapply posExt; tea; eapply Rt + eapply Rtext; now irrelevanceRefl.
  Qed.

  Lemma polyRedEqSubst {Γ l A B t u} (PAB : PolyRed Γ l A B) 
    (Rt : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    (Ru : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> u[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    (Rtu : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
      [Δ ||-<l> t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
    (PABt : PolyRed Γ l A B[t]⇑)
    : PolyRedEq PABt A B[u]⇑.
  Proof.
    constructor.
    - intros; eapply reflLRTyEq.
    - intros; irrelevance0; rewrite liftSubst_scons_eq; [reflexivity|].
      unshelve eapply PolyRed.posExt; cycle 1; tea.
      + eapply Rt; now irrelevanceRefl.
      + eapply Ru; now irrelevanceRefl.
      + eapply Rtu; try eapply reflLRTmEq; now irrelevanceRefl.
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
      2: now eapply reflLRTmEq.
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
      2: now eapply reflLRTmEq.
      eapply validTyExt; tea.
      eapply consWkSubstS; tea.
      eapply LRTmRedConv; tea.
      irrelevanceRefl; now eapply wkEq.
      Unshelve. 1,3,5: tea. now eapply wk.
  Qed.

End PolyValidity.


