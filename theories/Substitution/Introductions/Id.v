From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application Universe Id.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity Reduction.
From LogRel.Substitution.Introductions Require Import Universe Var.

Set Universe Polymorphism.

Section Id.
Context `{GenericTypingProperties}.

  Lemma IdValid {Γ l A x y} 
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) :
    [_ ||-v<l> tId A x y | VΓ].
  Proof.
    unshelve econstructor; intros.
    - instValid vσ; cbn; now eapply IdRed.
    - instAllValid vσ vσ' vσσ'; eapply IdCongRed; refold; tea.
      eapply wft_Id; now escape.
  Qed.

  Lemma IdCongValid {Γ l A A' x x' y y'}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) 
    (Vy' : [_ ||-v<l> y' : _ | _ | VA]) 
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA]) 
    (VId : [_ ||-v<l> tId A x y | VΓ]) :
    [_ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ | VId].
  Proof.
    constructor; intros.
    instValid Vσ; eapply IdCongRed; refold; tea.
    eapply wft_Id. 
    2,3: eapply ty_conv.
    all: now escape.
  Qed.


  Lemma IdTmValid {Γ l A x y} 
    (VΓ : [||-v Γ]) 
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A : U | VΓ | VU]) 
    (VA := univValid VΓ VU VAU)
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) :
    [_ ||-v<one> tId A x y : _ | VΓ | VU].
  Proof. 
    unshelve econstructor; intros.
    - instValid Vσ. 
      unshelve eapply IdRedU; refold; tea.
      1: now eapply univValid.
      all: irrelevance.
    - instAllValid Vσ Vσ' Vσσ'.
      unshelve eapply IdCongRedU; refold; tea.
      1,2: now eapply univValid.
      all: irrelevance.
  Qed.
    
  Lemma IdTmCongValid {Γ l A A' x x' y y'}
    (VΓ : [||-v Γ]) 
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A : _ | VΓ | VU]) 
    (VA := univValid VΓ VU VAU)
    (VAU' : [_ ||-v<one> A' : _ | VΓ | VU]) 
    (VAAU' : [_ ||-v<one> A ≅ A' : _ | VΓ | VU]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) 
    (Vy' : [_ ||-v<l> y' : _ | _ | VA]) 
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<one> tId A x y ≅ tId A' x' y' : _ | VΓ | VU].
  Proof.
    constructor; intros; instValid Vσ.
    unshelve eapply IdCongRedU; refold; tea.
    1,2: now eapply univValid.
    2,5: eapply LRTmRedConv; [eapply univEqValid; irrValid|].
    all: irrelevance.
    Unshelve. 3,9: now eapply univValid.
    all: tea.
  Qed.


  Lemma reflValid {Γ l A x} 
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VId : [_ ||-v<l> tId A x x | VΓ]) :
    [_ ||-v<l> tRefl A x : _ | _ | VId].
  Proof.
    unshelve econstructor; intros.
    - instValid Vσ; now unshelve eapply reflRed.
    - instAllValid Vσ Vσ' Vσσ'; escape; now unshelve eapply reflCongRed.
  Qed.

  Lemma reflCongValid {Γ l A A' x x'}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VId : [_ ||-v<l> tId A x x | VΓ]) :
    [_ ||-v<l> tRefl A x ≅ tRefl A' x' : _ | _ | VId].
  Proof.
    constructor; intros; instValid Vσ.
    escape; unshelve eapply reflCongRed; refold; tea.
    now eapply ty_conv.
  Qed.

  Lemma subst_scons2 (P e y : term) (σ : nat -> term) : P[e .: y..][σ] = P [e[σ] .: (y[σ] .: σ)].
  Proof. now asimpl. Qed.
  
  Lemma subst_upup_scons2 (P e y : term) (σ : nat -> term) : P[up_term_term (up_term_term σ)][e .: y..] = P [e .: (y .: σ)].
  Proof. now asimpl. Qed.

  Lemma consSubstS' {Γ σ t l A Δ} 
    (VΓ : [||-v Γ])
    (VΓA : [||-v Γ ,, A])
    (wfΔ : [|- Δ])
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
    (VA : [Γ ||-v<l> A | VΓ])
    (Vt : [ Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]) :
    [Δ ||-v (t .: σ) : Γ ,, A | VΓA | wfΔ].
  Proof. 
    pose proof (invValiditySnoc VΓA) as [? [? [? ->]]].
    unshelve eapply consSubstS; [ irrValid| irrelevance].
  Qed.

  Lemma consSubstSEq'' {Γ σ σ' t u l A Δ} 
    (VΓ : [||-v Γ])
    (VΓA : [||-v Γ ,, A])
    (wfΔ : [|- Δ])
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
    (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
    (VA : [Γ ||-v<l> A | VΓ])
    (Vt : [Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ])
    (Vtu : [Δ ||-<l> t ≅ u : A[σ] | validTy VA wfΔ Vσ])
    (Vσt : [_ ||-v (t .: σ) : _ | VΓA | wfΔ]) :
    [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | VΓA | wfΔ | Vσt].
  Proof.
    pose proof (invValiditySnoc VΓA) as [? [? [? ->]]].
    pose proof (consSubstSEq' VΓ wfΔ Vσ Vσσ' VA Vt Vtu).
    irrValid.
  Qed.  


  Lemma idElimMotiveCtxIdValid {Γ l A x}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA]) :
    [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) | validSnoc VΓ VA].
  Proof.
    unshelve eapply IdValid.
    - now eapply wk1ValidTy.
    - now eapply wk1ValidTm.
    - exact (var0Valid VΓ VA).
  Qed.
  
  Lemma idElimMotiveCtxIdCongValid {Γ l A A' x x'}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA])
    (Vx : [_ ||-v<l> x : _ | _ | VA]) 
    (Vx' : [_ ||-v<l> x' : _ | _ | VA]) 
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]) 
    (VId : [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) | validSnoc VΓ VA]) :
    [_ ||-v<l> _ ≅ tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0) | validSnoc VΓ VA | VId].
  Proof.
    assert (h : forall t, t⟨@wk1 Γ A'⟩ = t⟨@wk1 Γ A⟩) by reflexivity.
    unshelve eapply IdCongValid.
    - now eapply wk1ValidTy.
    - rewrite h; now eapply wk1ValidTy.
    - rewrite h; now eapply wk1ValidTyEq.
    - now eapply wk1ValidTm.
    - rewrite h; now eapply wk1ValidTm.
    - rewrite h; now eapply wk1ValidTmEq.
    - eapply var0Valid.
    - eapply var0Valid.
    - eapply reflValidTm; eapply var0Valid.
  Qed.
  
  
  Lemma idElimMotiveScons2Valid {Γ l A x y e}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vy : [Γ ||-v<l> y : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e : _ | _ | VId]) 
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    Δ σ (wfΔ: [ |-[ ta ] Δ]) (vσ: [VΓ | Δ ||-v σ : _ | wfΔ]) :
      [VΓext | Δ ||-v (e[σ] .: (y[σ] .: σ)) : _ | wfΔ].
  Proof.
    intros; unshelve eapply consSubstS'; tea.
    2: now eapply consSubstSvalid.
    1: now eapply idElimMotiveCtxIdValid.
    instValid vσ; irrelevance.
  Qed.
  
  Lemma substIdElimMotive {Γ l A x P y e}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (Vy : [Γ ||-v<l> y : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e : _ | _ | VId]) : 
    [_ ||-v<l> P[e .: y ..] | VΓ].
  Proof.
    opector; intros.
    - rewrite subst_scons2; eapply validTy; tea; now eapply idElimMotiveScons2Valid.
    - irrelevance0 ; rewrite subst_scons2;[reflexivity|].
      unshelve eapply validTyExt.
      5,6: eapply idElimMotiveScons2Valid; cycle 1; tea.
      1: tea.
      eapply consSubstSEq''.
      + now unshelve eapply consSubstSEqvalid.
      + instValid vσ; irrelevance.
      + instAllValid vσ vσ' vσσ'; irrelevance.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
  Qed.
  

  Lemma subst_idElimMotive_substupup {Γ Δ l A x P y e σ}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (RVA := validTy VA wfΔ Vσ)
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (Ry : [ RVA |  _ ||- y : _])
    (RId : [Δ ||-<l> tId A[σ] x[σ] y])
    (Re : [RId | _ ||- e : _]) :
    [Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]].
  Proof.
    pose (VΓA := validSnoc VΓ VA). 
    rewrite subst_upup_scons2.
    unshelve eapply validTy; cycle 2; tea.
    unshelve eapply consSubstS'; tea.
    + now eapply consSubstS.
    + now eapply idElimMotiveCtxIdValid.
    + irrelevance.
  Qed.
  
  Lemma irrelevanceSubst' {Γ} (VΓ VΓ' : [||-v Γ]) {σ Δ Δ'} (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) : Δ = Δ' ->
    [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ' ||-v σ : Γ | VΓ' | wfΔ'].
  Proof.
    intros ->; eapply irrelevanceSubst.
  Qed.

  Lemma idElimMotive_Idsubst_eq {Γ Δ A x σ} : 
    tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) = (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0))[up_term_term σ].
  Proof. now bsimpl. Qed.
  
  Lemma red_idElimMotive_substupup {Γ Δ l A x P σ}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext]) :
    [(Δ ,, A[σ]),, tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) ||-<l> P[up_term_term (up_term_term σ)]].
  Proof.
    pose (VΓA := validSnoc VΓ VA). 
    instValid Vσ.
    unshelve eapply validTy; cycle 2; tea.
    * escape. 
      assert [|- Δ,, A[σ]] by now eapply wfc_cons.
      eapply wfc_cons; tea.
      eapply wft_Id.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      rewrite wk1_ren_on; now eapply ty_var0.
    * epose (v1:= liftSubstS' VA Vσ).
      epose (v2:= liftSubstS' _ v1).
      eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply v2.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
  Qed.

  Lemma irrelevanceSubstEq' {Γ} (VΓ VΓ' : [||-v Γ]) {σ σ' Δ Δ'} (wfΔ : [|- Δ]) (wfΔ' : [|- Δ'])
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) (Vσ' : [Δ' ||-v σ : Γ | VΓ' | wfΔ']) :
    Δ = Δ' ->
    [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] -> [Δ' ||-v σ ≅ σ' : Γ | VΓ' | wfΔ' | Vσ'].
  Proof.
    intros ->; eapply irrelevanceSubstEq.
  Qed.
  
  Lemma red_idElimMotive_substupup_cong {Γ Δ l A x P σ σ'}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (Vσ' : [_ ||-v σ' : _ | VΓ | wfΔ])
    (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ | Vσ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext]) 
    (RPσ : [(Δ ,, A[σ]),, tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) ||-<l> P[up_term_term (up_term_term σ)]]) :
    [RPσ | _ ||- _ ≅ P[up_term_term (up_term_term σ')]].
  Proof.
    pose (VΓA := validSnoc VΓ VA). 
    instAllValid Vσ Vσ' Vσσ'.
    irrelevanceRefl; unshelve eapply validTyExt; cycle 2; tea.
    * escape. 
      assert [|- Δ,, A[σ]] by now eapply wfc_cons.
      eapply wfc_cons; tea.
      eapply wft_Id.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      rewrite wk1_ren_on; now eapply ty_var0.
    * epose (v1:= liftSubstS' VA Vσ).
      epose (v2:= liftSubstS' _ v1).
      eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply v2.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
    * eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply liftSubstSrealign'.
      + now eapply liftSubstSEq'.
      + now eapply liftSubstSrealign'.
      Unshelve. 
      2: now eapply idElimMotiveCtxIdValid.
    * eapply irrelevanceSubstEq'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply liftSubstSEq'.
      now eapply liftSubstSEq'.
      Unshelve.
      2: now eapply idElimMotiveCtxIdValid.
  Qed.

  Lemma redEq_idElimMotive_substupup {Γ Δ l A A' x x' P P' σ}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | _ | VA])
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VP' : [_ ||-v<l> P' | VΓext])
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP]) 
    (VPsubstupup : [(Δ ,, A[σ]),, tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) ||-<l> P[up_term_term (up_term_term σ)]]) :
    [_ ||-<l> _ ≅ P'[up_term_term (up_term_term σ)] | VPsubstupup].
  Proof.
    pose (VΓA := validSnoc VΓ VA). 
    instValid Vσ.
    irrelevanceRefl; unshelve eapply validTyEq; cycle 2; tea.
    * escape. 
      assert [|- Δ,, A[σ]] by now eapply wfc_cons.
      eapply wfc_cons; tea.
      eapply wft_Id.
      1: now eapply wft_wk.
      1: now eapply ty_wk.
      rewrite wk1_ren_on; now eapply ty_var0.
    * epose (v1:= liftSubstS' VA Vσ).
      epose (v2:= liftSubstS' _ v1).
      eapply irrelevanceSubst'.
      1: now erewrite idElimMotive_Idsubst_eq.
      eapply v2.
      Unshelve. 2: now eapply idElimMotiveCtxIdValid.
  Qed.


  Lemma substEq_idElimMotive_substupupEq {Γ Δ l A x P y y' e e' σ σ'}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (Vσ' : [_ ||-v σ' : _ | VΓ | wfΔ])
    (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ | Vσ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (RVA := validTy VA wfΔ Vσ)
    (RVA' := validTy VA wfΔ Vσ')
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (Ry : [ RVA |  _ ||- y : _])
    (Ry' : [ RVA' |  _ ||- y' : _])
    (Ryy' : [ RVA |  _ ||- y ≅ y' : _])
    (RId : [Δ ||-<l> tId A[σ] x[σ] y])
    (RId' : [Δ ||-<l> tId A[σ'] x[σ'] y'])
    (Re : [RId | _ ||- e : _])
    (Re' : [RId' | _ ||- e' : _])
    (Ree' : [RId | _ ||- e ≅ e' : _])
    (RPsubst : [Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]) :
    [RPsubst | Δ ||- P[up_term_term (up_term_term σ)][e .: y ..] ≅ P[up_term_term (up_term_term σ')][e' .: y' ..]].
  Proof.
    pose (VΓA := validSnoc VΓ VA). 
    irrelevance0; rewrite subst_upup_scons2; [reflexivity|].
    unshelve eapply validTyExt; cycle 2; tea.
    - unshelve eapply consSubstS'; tea.
      + now eapply consSubstS.
      + now eapply idElimMotiveCtxIdValid.
      + irrelevance.
    - unshelve eapply consSubstS'; tea.
      + now eapply consSubstS.
      + now eapply idElimMotiveCtxIdValid.
      + irrelevance.
    - unshelve eapply consSubstSEq''; tea.
      4,5: irrelevance.
      2: now eapply idElimMotiveCtxIdValid.
      2: unshelve eapply consSubstSEq'; tea.
  Qed.

  Lemma substEq_idElimMotive_substupup {Γ Δ l A x P y y' e e' σ}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (RVA := validTy VA wfΔ Vσ)
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (Ry : [ RVA |  _ ||- y : _])
    (Ry' : [ RVA |  _ ||- y' : _])
    (Ryy' : [ RVA |  _ ||- y ≅ y' : _])
    (RId : [Δ ||-<l> tId A[σ] x[σ] y])
    (RId' : [Δ ||-<l> tId A[σ] x[σ] y'])
    (Re : [RId | _ ||- e : _])
    (Re' : [RId' | _ ||- e' : _])
    (Ree' : [RId | _ ||- e ≅ e' : _])
    (RPsubst : [Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]) :
    [RPsubst | Δ ||- P[up_term_term (up_term_term σ)][e .: y ..] ≅ P[up_term_term (up_term_term σ)][e' .: y' ..]].
  Proof.
    eapply substEq_idElimMotive_substupupEq; tea; eapply reflSubst.
  Qed.

  Set Printing Primitive Projection Parameters.

  Lemma substExt_idElimMotive_substupup {Γ Δ l A A' x x' P P' y y' e e' σ}
    (VΓ : [||-v Γ]) 
    (wfΔ : [|- Δ])
    (Vσ : [_ ||-v σ : _ | VΓ | wfΔ])
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | _ | VA])
    (RVA := validTy VA wfΔ Vσ)
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VP' : [_ ||-v<l> P' | VΓext])
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP]) 
    (Ry : [ RVA |  _ ||- y : _])
    (Ry' : [ RVA |  _ ||- y' : _])
    (Ryy' : [ RVA |  _ ||- y ≅ y' : _])
    (RId : [Δ ||-<l> tId A[σ] x[σ] y])
    (RId' : [Δ ||-<l> tId A[σ] x[σ] y'])
    (Re : [RId | _ ||- e : _])
    (Re' : [RId' | _ ||- e' : _])
    (Ree' : [RId | _ ||- e ≅ e' : _])
    (RPsubst : [Δ ||-<l> P[up_term_term (up_term_term σ)][e .: y ..]]) :
    [RPsubst | Δ ||- P[up_term_term (up_term_term σ)][e .: y ..] ≅ P'[up_term_term (up_term_term σ)][e' .: y' ..]].
  Proof.
    pose (VΓA := validSnoc VΓ VA). 
    eapply LRTransEq.
    eapply substEq_idElimMotive_substupup.
    2,4,8: tea. all:tea.
    irrelevance0; rewrite subst_upup_scons2; [reflexivity|].
    unshelve eapply validTyEq; cycle 2; tea.
    eapply irrelevanceSubst.
    unshelve eapply consSubstS.
    3: now eapply idElimMotiveCtxIdValid.
    1: now eapply consSubstS.
    irrelevance.
    Unshelve. 2: eapply subst_idElimMotive_substupup; cycle 1; tea.
  Qed.


  Lemma substExtIdElimMotive {Γ l A x P y y' e e'}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (Vy : [Γ ||-v<l> y : _ | _ | VA])
    (Vy' : [Γ ||-v<l> y' : _ | _ | VA])
    (Vyy' : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (VId' : [Γ ||-v<l> tId A x y' | VΓ])
    (Ve : [_ ||-v<l> e : _ | _ | VId]) 
    (Ve' : [_ ||-v<l> e' : _ | _ | VId']) 
    (Vee' : [_ ||-v<l> e ≅ e' : _ | _ | VId]) 
    (VPey : [_ ||-v<l> P[e .: y ..] | VΓ]) : 
    [_ ||-v<l> P[e .: y ..] ≅ P[e' .: y' ..] | VΓ | VPey].
  Proof.
    constructor; intros.
    irrelevance0; rewrite subst_scons2; [reflexivity|]. 
    unshelve eapply validTyExt.
    5,6: eapply idElimMotiveScons2Valid; cycle 1; tea.
    1: tea.
    instValid Vσ; unshelve eapply consSubstSEq''.
    4: now eapply idElimMotiveCtxIdValid.
    2: eapply consSubstSEq'; [now eapply reflSubst|]; irrelevance.
    all: irrelevance.
    Unshelve. 1:tea. irrelevance.
  Qed.

  Lemma substEqIdElimMotive {Γ l A A' x x' P P' y y' e e'}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | VΓ | VA]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VP' : [_ ||-v<l> P | VΓext])
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP])
    (Vy : [Γ ||-v<l> y : _ | _ | VA])
    (Vy' : [Γ ||-v<l> y' : _ | _ | VA])
    (Vyy' : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e : _ | _ | VId]) 
    (Ve' : [_ ||-v<l> e' : _ | _ | VId]) 
    (Vee' : [_ ||-v<l> e ≅ e' : _ | _ | VId]) 
    (VPey : [_ ||-v<l> P[e .: y ..] | VΓ]) : 
    [_ ||-v<l> P[e .: y ..] ≅ P'[e' .: y' ..] | VΓ | VPey].
  Proof.
    assert (VId' : [Γ ||-v<l> tId A x y' | VΓ]) by now eapply IdValid.
    assert [Γ ||-v< l > e' : tId A x y' | VΓ | VId'].
    1:{
      eapply conv; tea.
      eapply IdCongValid; tea.
      1: eapply reflValidTy.
      now eapply reflValidTm.
    }
    eapply transValidTyEq.
    - eapply substExtIdElimMotive.
      2: tea. all: tea.
      Unshelve. eapply substIdElimMotive; cycle 1; tea.
    - constructor; intros; irrelevance0; rewrite subst_scons2; [reflexivity|].
      unshelve eapply validTyEq.
      6: tea. 1: tea.
      eapply idElimMotiveScons2Valid; tea.
  Qed.
    
  (* Lemma liftSubstS' {Γ σ Δ lF F} 
    {VΓ : [||-v Γ]} 
    {wfΔ : [|- Δ]}
    (VF : [Γ ||-v<lF> F | VΓ])
    (VΓF : [||-v Γ,, F])
    {wfΔF : [|- Δ ,, F[σ]]}
    (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
    [Δ ,, F[σ] ||-v up_term_term σ : Γ ,, F | VΓF | wfΔF ].
  Proof.
    eapply irrelevanceSubst.
    now unshelve eapply liftSubstS'.
  Qed. *)


  Lemma IdElimValid {Γ l A x P hr y e}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx (IdValid VΓ VA Vx Vx) (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) 
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e : _ | _ | VPye].
  Proof.
    unshelve epose (h := _ : [||-v Γ,, A]). 1: now eapply validSnoc.
    constructor; intros.
    - instValid Vσ.
      irrelevance0.
      2: unshelve eapply idElimRed; refold; tea.
      1: refold; now rewrite subst_upup_scons2, subst_scons2.
      2,5: irrelevance.
      + intros; eapply subst_idElimMotive_substupup; cycle 1; tea.
      + now eapply red_idElimMotive_substupup.
      + intros; eapply substEq_idElimMotive_substupup; cycle 1; tea.
        eapply LRTmRedConv; tea; now eapply LRTyEqSym.
    - instAllValid Vσ Vσ' Vσσ'.
      irrelevance0.
      2: unshelve eapply idElimCongRed; refold.
      1: refold; now rewrite subst_upup_scons2, subst_scons2.
      all: try now eapply LRCumulative.
      all: tea; try irrelevanceCum.
      2,4: now eapply red_idElimMotive_substupup.
      + intros; eapply subst_idElimMotive_substupup; cycle 1; tea; irrelevanceCum.
        Unshelve. all: tea. irrelevanceCum.
      + intros; eapply subst_idElimMotive_substupup; cycle 1; tea; irrelevanceCum.
        Unshelve. all: tea.
      + now eapply red_idElimMotive_substupup_cong.
      + intros; eapply substEq_idElimMotive_substupupEq; cycle 2; tea; irrelevanceCum.
        Unshelve. all: tea. now eapply LRCumulative.
      + intros; eapply substEq_idElimMotive_substupup; cycle 1; tea.
        1,3-6: irrelevanceCum.
        eapply LRTmRedConv;[|irrelevanceCum]; eapply LRTyEqSym; irrelevanceCum.
        Unshelve. all: tea; now eapply LRCumulative.
      + Set Printing Primitive Projection Parameters.
        intros; eapply substEq_idElimMotive_substupup; cycle 1; tea.
        1,3: irrelevanceCum.
        eapply LRTmRedConv; [|irrelevanceCum]; eapply LRTyEqSym; irrelevanceCum.
        Unshelve. all: tea.
  Qed.

  Lemma IdElimCongValid {Γ l A A' x x' P P' hr hr' y y' e e'}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (VA' : [_ ||-v<l> A' | VΓ]) 
    (VAA' : [_ ||-v<l> A ≅ A' | _ | VA])
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (Vx' : [_ ||-v<l> x' : _ | _ | VA])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VP' : [_ ||-v<l> P' | VΓext])
    (VPP' : [_ ||-v<l> P ≅ P' | _ | VP])
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx (IdValid VΓ VA Vx Vx) (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ])
    (Vhr' : [_ ||-v<l> hr' : _ | _ | VPhr ])
    (Vhrhr' : [_ ||-v<l> hr ≅ hr' : _ | _ | VPhr])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) 
    (Vy' : [_ ||-v<l> y' : _ | _ | VA]) 
    (Vyy' : [_ ||-v<l> y ≅ y' : _ | _ | VA]) 
    (VId : [Γ ||-v<l> tId A x y | VΓ])
    (Ve : [_ ||-v<l> e : _ | _ | VId])
    (Ve' : [_ ||-v<l> e' : _ | _ | VId])
    (Vee' : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | _ | VPye].
  Proof.
    assert [_ ||-v<l> x' : _ | _ | VA'] by now eapply conv.
    assert [_ ||-v<l> y' : _ | _ | VA'] by now eapply conv.
    assert (VΓext' : [||-v (Γ ,, A'),, tId A'⟨@wk1 Γ A'⟩ x'⟨@wk1 Γ A'⟩ (tRel 0)]).
    1: eapply validSnoc; now eapply idElimMotiveCtxIdValid.
    assert (h : forall t, t⟨@wk1 Γ A'⟩ = t⟨@wk1 Γ A⟩) by reflexivity.
    assert (VPalt' : [_ ||-v<l> P' | VΓext']).
    1:{
      eapply convCtx2'; tea.
      1: eapply convCtx1; tea; [now eapply symValidTyEq| ].
      1,3: now eapply idElimMotiveCtxIdValid.
      eapply idElimMotiveCtxIdCongValid; tea.
      Unshelve. 1: now eapply idElimMotiveCtxIdValid. tea.
    }
    constructor; intros.
    instValid Vσ.
    irrelevance0.
    2: unshelve eapply idElimCongRed; refold.
    1: refold; now rewrite subst_upup_scons2, subst_scons2.
    all: first [now eapply LRCumulative | solve [irrelevance | irrelevanceCum] | now eapply LRTmRedConv | tea].
    + intros ; eapply subst_idElimMotive_substupup; cycle 1; tea; irrelevanceCum.
      Unshelve. all: tea. irrelevanceCum.
    + intros; eapply red_idElimMotive_substupup; tea.
    + intros; eapply subst_idElimMotive_substupup; cycle 1; tea.
      irrelevance.
      Unshelve. all: tea.
    + unshelve eapply IdRed; tea; eapply LRTmRedConv; tea.
    + eapply red_idElimMotive_substupup; tea.
    + eapply redEq_idElimMotive_substupup.
      6-8: tea. 3-5: tea. all: tea.
    + intros.
      assert [_ ||-<l> y'0 : _ | RVA] by (eapply LRTmRedConv; tea; now eapply LRTyEqSym).
      eapply substExt_idElimMotive_substupup.
      7: tea. 2,3,5,6: tea. all: tea; try solve [irrelevanceCum].
      1: eapply LRTmRedConv; tea; eapply LRTyEqSym; tea.
      eapply IdCongRed; tea; [now escape|  now eapply reflLRTmEq].
      Unshelve. 1: now eapply LRCumulative. 1,2: now eapply IdRed.
    + intros; eapply substEq_idElimMotive_substupup; cycle 1; tea; try solve [irrelevanceCum].
      eapply LRTmRedConv. 2:irrelevanceCum. eapply LRTyEqSym; irrelevanceCum.
      Unshelve. all: tea; now eapply LRCumulative.
    + intros; eapply substEq_idElimMotive_substupup; cycle 1; tea; try solve [irrelevanceCum].
      eapply LRTmRedConv. 2:irrelevanceCum. eapply LRTyEqSym; irrelevanceCum.
      Unshelve. all: tea; now eapply LRCumulative.
    + eapply LRTmRedConv; tea.
      rewrite subst_upup_scons2; change (tRefl A'[σ] x'[σ]) with (tRefl A' x')[σ].
      rewrite <- subst_scons2.
      eapply validTyEq. eapply substEqIdElimMotive.
      6,7: tea.  5-8: tea. 2-4: tea. 1: tea.
      2: eapply conv.
      1,3: now eapply reflValid.
      1: eapply symValidTyEq; now eapply IdCongValid.
      now eapply reflCongValid.
      Unshelve. all: now eapply IdValid.
    + eapply LRTmRedConv; tea.
      now eapply IdCongValid.
  Qed.


  Lemma IdElimReflValid {Γ l A x P hr y B z}
    (VΓ : [||-v Γ]) 
    (VA : [_ ||-v<l> A | VΓ]) 
    (Vx : [_ ||-v<l> x : _ | _ | VA])
    (VΓext : [||-v (Γ ,, A) ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)])
    (VP : [_ ||-v<l> P | VΓext])
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx (IdValid VΓ VA Vx Vx) (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ])
    (Vy : [_ ||-v<l> y : _ | _ | VA]) 
    (Vxy : [_ ||-v<l> x ≅ y : _ | _ | VA]) 
    (VB : [_ ||-v<l> B | VΓ])
    (VAB : [_ ||-v<l> _ ≅ B | VΓ | VA])
    (Vz : [_ ||-v<l> z : _ | _ | VB]) 
    (Vxz : [_ ||-v<l> x ≅ z : _ | _ | VA]) 
    (VId : [Γ ||-v<l> tId A x y | VΓ]) 
    (VRefl : [_ ||-v<l> tRefl B z : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId VRefl) :
    [_ ||-v<l> tIdElim A x P hr y (tRefl B z) ≅ hr : _ | _ | VPye].
  Proof.
    constructor; intros.
    assert [Γ ||-v< l > P[tRefl A x .: x..] ≅ P[tRefl B z .: y..] | VΓ | VPhr].
    1:{
      eapply substExtIdElimMotive; cycle 1; tea.
      1: now eapply reflValid.
      eapply reflCongValid; tea.
      eapply conv; tea.
      now eapply symValidTyEq.
      Unshelve. now eapply IdValid.
    }
    eapply redwfSubstValid; cycle 1.
    + eapply conv; tea.
    + constructor; intros.
      instValid Vσ0; escape.
      constructor.
      - eapply ty_conv; tea.
      - rewrite subst_scons2, <- subst_upup_scons2.
        eapply redtm_idElimRefl; refold; tea.
        * eapply escape. now eapply red_idElimMotive_substupup.
        * rewrite subst_upup_scons2; change (tRefl ?A[?σ] ?x[_]) with (tRefl A x)[σ].
          now rewrite <- subst_scons2.
        * now eapply ty_conv.
  Qed.

End Id.


  

