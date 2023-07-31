From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Induction.
From LogRel.Substitution Require Import Irrelevance.

Set Universe Polymorphism.

Section Properties.
Context `{GenericTypingProperties}.


Lemma wellformedSubst {Γ σ Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) :
  [Δ ||-v σ : Γ | VΓ| wfΔ] -> [Δ |-s σ : Γ ].
Proof.
  revert σ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply well_sempty.
  - intros * ih σ [tl hd].
    eapply well_scons.
    + now apply ih.
    + now escape.
Qed.

Lemma wellformedSubstEq {Γ σ σ' Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] -> [Δ |-s σ ≅ σ' : Γ].
Proof.
  revert σ σ' Vσ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply conv_sempty.
  - intros * ih ??? [tl hd]. apply conv_scons.
    + now eapply ih.
    + now escape.
Qed.

Lemma consSubstS {Γ σ t l A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [ Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]) :
  [Δ ||-v (t .: σ) : Γ ,, A | validSnoc VΓ VA | wfΔ].
Proof.  unshelve econstructor; eassumption. Defined.

Lemma consValid {Γ Δ σ a A l} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
  {VA : [Γ ||-v<l> A| VΓ]}
  (Va : [Γ ||-v<l> a : A | VΓ | VA])
  (VΓA := validSnoc VΓ VA) :
  [Δ ||-v (a[σ] .: σ) : Γ,, A | VΓA | wfΔ].
Proof.
  unshelve eapply consSubstS; tea; now eapply validTm.
Qed.


Lemma consSubstSEq {Γ σ σ' t l A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]) :
  [Δ ||-v (t .: σ) ≅  (t .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt].
Proof.
  unshelve econstructor.
  1: eassumption.
  eapply LRTmEqRefl; [apply (validTy VA wfΔ)| exact Vt].
Qed.

Lemma consSubstSEq' {Γ σ σ' t u l A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ])
  (Vtu : [Δ ||-<l> t ≅ u : A[σ] | validTy VA wfΔ Vσ]) :
  [Δ ||-v (t .: σ) ≅  (u .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt].
Proof.
  unshelve econstructor; tea.
Qed.  


Lemma consSubstSvalid {Γ σ t l A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [ Γ ||-v<l> t : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) : Γ ,, A | validSnoc VΓ VA | wfΔ].
Proof. unshelve eapply consSubstS; tea; now eapply validTm. Defined.

Set Printing Primitive Projection Parameters.

Lemma consSubstSEqvalid {Γ σ σ' t l A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) 
  (Vσ' : [Δ ||-v σ' : Γ | VΓ | wfΔ]) 
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) ≅  (t[σ'] .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ | consSubstSvalid VΓ wfΔ Vσ VA Vt].
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmExt.
Qed.

Lemma wkSubstS {Γ} (VΓ : [||-v Γ]) : 
  forall {σ  Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ),
  [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ' ||-v σ ⟨ ρ ⟩ : Γ | VΓ | wfΔ'].
Proof.
  pattern Γ, VΓ ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]. unshelve econstructor.
    + eapply ih; eassumption.
    + eapply LRTmRedIrrelevant'.
      2: eapply (wkTerm _ wfΔ') ; exact hd.
      now asimpl.
Defined.


Lemma wkSubstSEq {Γ} (VΓ : [||-v Γ]) :
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' | wkSubstS VΓ wfΔ wfΔ' ρ Vσ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply ih ; eassumption.
    + eapply LRTmEqIrrelevant'.
      2: eapply (wkTermEq _ wfΔ') ; exact hd.
      now asimpl.
Qed.

Lemma wk1SubstS {Γ σ Δ F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) (wfF : [Δ |- F]) :
  [Δ ||-v σ : Γ | VΓ | wfΔ ] ->
  [Δ ,, F ||-v σ ⟨ @wk1 Δ F ⟩ : Γ | VΓ | wfc_cons wfΔ wfF].
Proof. eapply wkSubstS. Defined.

Lemma wk1SubstSEq {Γ σ σ' Δ F} (VΓ : [||-v Γ])
  (wfΔ : [|- Δ]) (wfF : [Δ |- F])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  let ρ := @wk1 Δ F in
  [Δ ,, F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons wfΔ wfF | wk1SubstS VΓ wfΔ wfF Vσ].
Proof.
  intro vσσ'. eapply wkSubstSEq ; eassumption.
Qed.

Lemma consWkSubstS {Γ F Δ Ξ σ a l VΓ wfΔ } VF
  (ρ : Ξ ≤ Δ) wfΞ {RF}:
  [Δ ||-v σ : Γ | VΓ | wfΔ] ->
  [Ξ ||-<l> a : F[σ]⟨ρ⟩ | RF] ->
  [Ξ ||-v (a .: σ⟨ρ⟩) : Γ,, F | validSnoc (l:=l) VΓ VF | wfΞ].
Proof.
  intros. unshelve eapply consSubstS.  2: irrelevance.
  now eapply wkSubstS.
Qed.

Lemma consWkSubstSEq' {Γ Δ Ξ A σ σ' a b l} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VA : [Γ ||-v<l> A | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
  (ρ : Ξ ≤ Δ) wfΞ {RA}
  (Ra : [Ξ ||-<l> a : A[σ]⟨ρ⟩ | RA])
  (Rab : [Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | RA]) 
  (Vawkσ := consWkSubstS VA ρ wfΞ Vσ Ra) :
  [Ξ ||-v (a .: σ⟨ρ⟩) ≅  (b .: σ'⟨ρ⟩) : Γ ,, A | validSnoc VΓ VA | wfΞ | Vawkσ].
Proof.
  unshelve eapply consSubstSEq'.
  - unshelve eapply irrelevanceSubstEq.
    4: now eapply wkSubstSEq.
    tea.
  - irrelevance0; tea. now bsimpl.
Qed.  


Lemma liftSubstS {Γ σ Δ lF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; unshelve econstructor.
  - now eapply wk1SubstS.
  - eapply var0; unfold ρ; [now bsimpl|].
    now eapply escape, VF.
Defined.

Lemma liftSubstSrealign {Γ σ σ' Δ lF F} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]} :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ]  in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ ||-v σ' : Γ | VΓ | wfΔ ] ->
  [Δ ,, F[σ] ||-v (tRel 0 .: σ'⟨ρ⟩) : Γ ,, F | VΓF | wfΔF].
Proof.
  intros; unshelve econstructor.
  + now eapply wk1SubstS.
  + cbn.
    assert [Δ,, F[σ] |-[ ta ] tRel 0 : F[S >> (tRel 0 .: σ'⟨ρ⟩)]].
    { replace F[_ >> _] with F[σ']⟨S⟩ by (unfold ρ; now bsimpl).
      eapply ty_conv. 1: apply (ty_var wfΔF (in_here _ _)).
      cbn; renToWk. eapply convty_wk; tea.
      eapply escapeEq;  unshelve eapply validTyExt; cycle 3; tea. }
    apply neuTerm; tea.
    - apply convneu_var; tea.
Qed.

Lemma liftSubstS' {Γ σ Δ lF F} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v up_term_term σ : Γ ,, F | VΓF | wfΔF ].
Proof.
  eapply irrelevanceSubstExt.
  2: eapply liftSubstS.
  intros ?; now bsimpl.
Qed.

Lemma liftSubstSEq {Γ σ σ' Δ lF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  let Vliftσ := liftSubstS VΓ wfΔ VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF | Vliftσ].
Proof.
  intros; unshelve econstructor.
  + now apply wk1SubstSEq.
  + apply LREqTermRefl_; exact (validHead Vliftσ).
Qed.

Lemma liftSubstSEq' {Γ σ σ' Δ lF F} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]} :
  let VΓF := validSnoc VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  let Vliftσ := liftSubstS' VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ ,, F[σ] ||-v up_term_term σ ≅ up_term_term σ' : Γ ,, F | VΓF | wfΔF | Vliftσ].
Proof.
  intros.
  eapply irrelevanceSubstEq.
  unshelve eapply irrelevanceSubstEqExt.
  6: now eapply liftSubstSEq.
  all: intros ?; now bsimpl.
  Unshelve. all: tea.
Qed.

Lemma liftSubstSrealign' {Γ σ σ' Δ lF F} {VΓ : [||-v Γ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  {Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]} :
  let VΓF := validSnoc VΓ VF in
  let ρ := wk_up F (@wk_id Γ) in
  let wfΔF := wfc_cons wfΔ (escape (validTy VF wfΔ Vσ)) in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ ||-v σ' : Γ | VΓ | wfΔ ] ->
  [Δ ,, F[σ] ||-v up_term_term σ' : Γ ,, F | VΓF | wfΔF].
Proof.
  intros.
  eapply irrelevanceSubstExt.
  2: eapply liftSubstSrealign; tea.
  intros ?; now bsimpl.
Qed.

Lemma wk1ValidTy {Γ lA A lF F} {VΓ : [||-v Γ]} (VF : [Γ ||-v<lF> F | VΓ]) :
  [Γ ||-v<lA> A | VΓ] -> 
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ | validSnoc VΓ VF ].
Proof.
  assert (forall σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren) ;
  intros [VA VAext]; unshelve econstructor.
  - abstract (intros * [tl _]; rewrite h; exact (VA _ _ wfΔ tl)).
  - intros * [tl _] [tleq _].
    rewrite (h σ'); unshelve eapply LRTyEqSym.
    2: eapply VA; eassumption.
    rewrite (h σ).
    eapply VAext. 1: exact (validTail vσ).
    eapply symmetrySubstEq. eassumption.
Qed.

Lemma wk1ValidTyEq {Γ lA A B lF F} {VΓ : [||-v Γ]} (VF : [Γ ||-v<lF> F | VΓ]) 
  {VA : [Γ ||-v<lA> A | VΓ]} :
  [Γ ||-v<lA> A ≅ B | VΓ | VA] -> 
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ ≅ B ⟨ @wk1 Γ F ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  intros []; constructor; intros.
  rewrite h. irrelevance0.
  1: symmetry; apply h.
  unshelve intuition; tea; now eapply validTail.
Qed.

Lemma wk1ValidTm {Γ lA t A lF F} {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  (VA : [Γ ||-v<lA> A | VΓ])
  (Vt : [Γ ||-v<lA> t : A | VΓ | VA]) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros; repeat rewrite h.
  - instValid (validTail Vσ); irrelevance.
  - instValidExt (validTail Vσ') (eqTail Vσσ'); irrelevance.
Qed.

Lemma wk1ValidTmEq {Γ lA t u A lF F} {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<lF> F | VΓ])
  (VA : [Γ ||-v<lA> A | VΓ])
  (Vtu : [Γ ||-v<lA> t ≅ u : A | VΓ | VA]) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  constructor; intros; repeat rewrite h.
  instValid (validTail Vσ); irrelevance.
Qed.


Lemma embValidTy@{u i j k l} {Γ l l' A}
    {VΓ : [VR@{i j k l}| ||-v Γ]} (h : l << l')
    (VA : typeValidity@{u i j k l} Γ VΓ l A (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ VΓ l' A (*[Γ ||-v<l'> A |VΓ]*).
Proof.
  unshelve econstructor.
  - intros ??? Vσ; destruct (validTy VA _  Vσ) as [pack]; exists pack.
    eapply LR_embedding; tea.
  - intros; now eapply validTyExt.
Defined.

Lemma embValidTyOne @{u i j k l} {Γ l A}
    {VΓ : [VR@{i j k l}| ||-v Γ]}
    (VA : typeValidity@{u i j k l} Γ VΓ l A (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ VΓ one A (*[Γ ||-v<one> A |VΓ]*).
Proof.
  destruct l; tea; now eapply (embValidTy Oi).
Defined.

Lemma soundCtxId {Γ} (VΓ : [||-v Γ]) :
  ∑ wfΓ : [|- Γ], [Γ ||-v tRel : Γ | VΓ | wfΓ].
Proof.
  enough (G : ∑ Δ (e : Δ = Γ) (wfΔ : [|-Δ]), [VΓ |Δ ||-v tRel : Γ | wfΔ]).
  1: now destruct G as [? [-> ?]].
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - exists ε, eq_refl, wfc_nil; constructor.
  - intros * [Δ [e [wfΔ Vid]]].
    exists (Δ,, A[tRel]); unshelve eexists. 
    1: asimpl; now rewrite e.
    unshelve eexists.
    + apply wfc_cons; tea.
      eapply escape.
      apply (validTy VA wfΔ Vid).
    + eapply irrelevanceSubstExt.
      2: eapply irrelevanceSubst; now unshelve eapply liftSubstS.
      intros []; [| bsimpl]; reflexivity.
Qed.

Definition soundCtx {Γ} (VΓ : [||-v Γ]) : [|-Γ] := (soundCtxId VΓ).π1.

Definition idSubstS {Γ} (VΓ : [||-v Γ]) : [Γ ||-v tRel : Γ | VΓ | _] := (soundCtxId VΓ).π2.

Lemma reflIdSubstS {Γ} (VΓ : [||-v Γ]) : [Γ ||-v tRel ≅ tRel : Γ | VΓ | _ | idSubstS VΓ].
Proof.  apply reflSubst. Qed.

Lemma substS_wk {Γ Δ} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ])
  (VΔ : [||-v Δ]) 
  {Ξ σ} (wfΞ : [|- Ξ]), [VΔ | Ξ ||-v σ : _ | wfΞ] -> [VΓ | Ξ ||-v ρ >> σ : _ | wfΞ].
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; rewrite (invValidityEmpty VΓ); constructor.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    rewrite eq in X; cbn in X; inversion X.
    eapply irrelevanceSubstExt.
    1: rewrite <- (scons_eta' σ); reflexivity.
    cbn. asimpl.
    now eapply IHwwk.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    rewrite eq in X; cbn in X; inversion X.
    eapply irrelevanceSubstExt.
    1:{ rewrite <- (scons_eta' σ); cbn; unfold up_ren; rewrite scons_comp'; cbn. reflexivity. }
    asimpl.
    pose proof (invValiditySnoc VΓ) as [? [? [? eq']]].
    rewrite eq'.
    unshelve eapply consSubstS.
    * now eapply IHwwk.
    * irrelevance.
Defined.

Lemma substSEq_wk {Γ Δ} (ρ : Δ ≤ Γ) :
  forall (VΓ : [||-v Γ])
  (VΔ : [||-v Δ]) 
  Ξ σ σ' (wfΞ : [|- Ξ])
  (Vσ : [VΔ | Ξ ||-v σ : _ | wfΞ]),
  [VΔ | Ξ ||-v σ' : _ | wfΞ] -> 
  [VΔ | Ξ ||-v σ ≅ σ' : _ | wfΞ | Vσ] -> 
  [VΓ | Ξ ||-v ρ >> σ ≅ ρ >> σ' : _ | wfΞ | substS_wk ρ VΓ VΔ wfΞ Vσ].
Proof.
  destruct ρ as [? wwk]; induction wwk.
  + intros; rewrite (invValidityEmpty VΓ); constructor.
  + intros.
    pose proof (invValiditySnoc VΔ) as [? [? [? eq]]].
    revert Vσ X X0; rewrite eq; intros Vσ Vσ' Vσσ'.
    cbn; asimpl; eapply irrelevanceSubstEq.
    unshelve eapply IHwwk; tea.
    1,2: now eapply validTail.
    now eapply eqTail.
    Unshelve. tea.
+ intros ??????.
  set (ρ0 := {| well_wk := _ |}); unfold ρ0.
  pose proof (invValiditySnoc VΔ) as [? [VΓ0 [? eq]]].
  pose proof (invValiditySnoc VΓ) as [? [VΔ0 [? eqΓ]]].
  rewrite eq; intros Vσ Vσ' Vσσ'.
  assert (subst_eq : forall τ : nat -> term, τ var_zero .: (ρ >> ↑ >> τ) =1 (0 .: ρ >> S) >> τ).
  1:{ intros τ;  asimpl; reflexivity. }
  pose proof (v := substS_wk ρ0 VΓ _ wfΞ Vσ).
  cbn; asimpl ; eapply irrelevanceSubstEq; unshelve eapply irrelevanceSubstEqExt.
  2,5: apply subst_eq.
  - eapply irrelevanceSubstExt.
    1: symmetry; apply subst_eq.
    exact v.
  - eapply irrelevanceSubstEq.
    eapply consSubstSEq'.
    * exact (IHwwk VΔ0 VΓ0 Ξ (↑ >> σ) (↑ >> σ') wfΞ (validTail Vσ) (validTail Vσ') (eqTail Vσσ')).
    * irrelevance0. 
      2: now eapply eqHead. 
      now asimpl.
    Unshelve. 2: tea.
    rewrite eqΓ in v.
    irrelevanceRefl.
    eapply (validHead v).
Qed.

Lemma wkValid {l Γ Δ A} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ])
  (VΔ : [||-v Δ])
  (VA : [Γ ||-v<l> A | VΓ]) :
  [Δ ||-v<l> A⟨ρ⟩ | VΔ].
Proof.
  assert (h : forall σ, A⟨ρ⟩[σ] = A[ ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor.
  - intros; rewrite h.
    eapply validTy; tea.
    now eapply substS_wk.
  - intros; irrelevance0; rewrite h; [reflexivity|].
    eapply validTyExt.
    1: now eapply substS_wk.
    now eapply substSEq_wk.
    Unshelve. 2,3: tea.
Qed.

Lemma wkEqValid {l Γ Δ A B} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ])
  (VΔ : [||-v Δ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VAB : [Γ ||-v<l> A ≅ B | VΓ | VA]) :
  [Δ ||-v<l> A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ | wkValid ρ VΓ VΔ VA].
Proof.
  assert (h : forall A σ, A⟨ρ⟩[σ] = A[ ρ >> σ]) by (intros; now asimpl).
  unshelve econstructor; intros; irrelevance0; rewrite h; [reflexivity|].
  now eapply validTyEq.
  Unshelve. 1: tea.
    now eapply substS_wk.
Qed.


Lemma irrelevanceValidity' {Γ Γ' A A' l} (VΓ : [||-v Γ]) (VΓ' : [||-v Γ']) (VA : [Γ ||-v<l> A | VΓ]) : 
  A = A' -> Γ = Γ' -> [Γ' ||-v<l> A' | VΓ'].
Proof.
  intros eqA eqΓ; subst; now eapply irrelevanceValidity.
Qed.



End Properties.
