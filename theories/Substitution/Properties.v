From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
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
    + eapply escapeTerm; [apply (validTy VA wfΔ tl) | exact hd].
Qed.

Lemma wellformedSubstEq {Γ σ σ' Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] -> [Δ |-s σ ≅ σ' : Γ].
Proof.
  revert σ σ' Vσ; pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - intros. apply conv_sempty.
  - intros * ih ??? [tl hd]. apply conv_scons.
    + now eapply ih.
    + eapply escapeEqTerm; [eapply (validTy VA wfΔ) | exact hd].
Qed.

Lemma consSubstS {Γ σ t l nA A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [ Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]) :
  [Δ ||-v (t .: σ) : Γ ,, vass nA A | validSnoc nA VΓ VA | wfΔ].
Proof.  unshelve econstructor; eassumption. Defined.


Lemma consSubstSEq {Γ σ σ' t l nA A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) 
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Δ ||-<l> t : A[σ] | validTy VA wfΔ Vσ]) :
  [Δ ||-v (t .: σ) ≅  (t .: σ') : Γ ,, vass nA A | validSnoc nA VΓ VA | wfΔ | consSubstS VΓ wfΔ Vσ VA Vt].
Proof.
  unshelve econstructor. 
  1: eassumption.
  eapply LRTmEqRefl; [apply (validTy VA wfΔ)| exact Vt].
Qed.

Lemma consSubstSvalid {Γ σ t l nA A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [ Γ ||-v<l> t : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) : Γ ,, vass nA A | validSnoc nA VΓ VA | wfΔ].
Proof. unshelve eapply consSubstS; tea; now eapply validTm. Defined.

Set Printing Primitive Projection Parameters.

Lemma consSubstSEqvalid {Γ σ σ' t l nA A Δ} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) 
  (Vσ' : [Δ ||-v σ' : Γ | VΓ | wfΔ]) 
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) ≅  (t[σ'] .: σ') : Γ ,, vass nA A | validSnoc nA VΓ VA | wfΔ | consSubstSvalid VΓ wfΔ Vσ VA Vt].
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmExt.
Qed.



Lemma wkSubstS {Γ} (VΓ : [||-v Γ]) : 
  forall {σ  Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ),
  [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ' ||-v σ ⟨ ρ ⟩ : Γ | VΓ | wfΔ'].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply ih; eassumption.
    + irrelevance0.
      2: unshelve eapply wkTerm; [|assumption| |eassumption].
      now asimpl.
Qed.


Lemma wkSubstSEq {Γ} (VΓ : [||-v Γ]) : 
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ)
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] -> 
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' | wkSubstS VΓ wfΔ wfΔ' ρ Vσ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + unshelve eapply irrelevanceSubstEq.
      4: unshelve eapply (ih _ _ _ _ _ _ ρ _ tl).
      assumption.
    + irrelevance0.
      2: unshelve eapply wkTermEq ;[|assumption| | eassumption].
      now asimpl.
Qed.

Lemma wk1SubstS {Γ σ Δ nF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) (wfF : [Δ |- F]) :
  [Δ ||-v σ : Γ | VΓ | wfΔ ] ->
  [Δ ,, vass nF F ||-v σ ⟨ @wk1 Δ nF F ⟩ : Γ | VΓ | wfc_cons nF wfΔ wfF].
Proof.  eapply wkSubstS. Qed.

Lemma wk1SubstSEq {Γ σ σ' Δ nF F} (VΓ : [||-v Γ])
  (wfΔ : [|- Δ]) (wfF : [Δ |- F])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  let ρ := @wk1 Δ nF F in
  [Δ ,, vass nF F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons nF wfΔ wfF | wk1SubstS VΓ wfΔ wfF Vσ].
Proof. 
  intros; unshelve eapply irrelevanceSubstEq. 
  4: eapply wkSubstSEq; eassumption.
  gen_typing.
Qed.

Lemma liftSubstS {Γ σ Δ lF nF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc nF VΓ VF in 
  let ρ := @wk1 Δ nF F[σ] in
  let wfΔF := wfc_cons nF wfΔ (escape_ (validTy VF wfΔ Vσ)) in
  [Δ ,, vass nF F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) : Γ ,, vass nF F | VΓF | wfΔF ].
Proof.
  intros; unshelve econstructor.
  + now eapply wk1SubstS.
  + assert [Δ,, vass nF F[σ] |-[ ta ] tRel 0 : F[S >> (tRel 0 .: σ⟨ρ⟩)]].
    1: replace F[_ >> _] with F[σ]⟨S⟩ by (unfold ρ; now bsimpl); apply (ty_var wfΔF (in_here _ _)).  
    apply neuTerm; tea; constructor + apply convneu_var; tea.
Defined.

Lemma liftSubstSEq {Γ σ σ' Δ lF nF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc nF VΓ VF in 
  let ρ := @wk1 Δ nF F[σ] in
  let wfΔF := wfc_cons nF wfΔ (escape_ (validTy VF wfΔ Vσ)) in
  let Vliftσ := liftSubstS VΓ wfΔ VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ ,, vass nF F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, vass nF F | VΓF | wfΔF | Vliftσ].
Proof.
  intros; unshelve econstructor.
  + now apply wk1SubstSEq.
  + apply LREqTermRefl_; exact (validHead Vliftσ).
Qed.

Lemma wk1ValidTy {Γ lA A lF F} (VΓ : [||-v Γ]) nF (VF : [Γ ||-v<lF> F | VΓ]) :
  [Γ ||-v<lA> A | VΓ] -> 
  [Γ ,, vass nF F ||-v<lA> A ⟨ @wk1 Γ nF F ⟩ | validSnoc nF VΓ VF ].
Proof.
  assert (forall σ, (A ⟨@wk1 Γ nF F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren) ;
  intros [VA VAext]; unshelve econstructor.
  - abstract (intros * [tl _]; rewrite h; exact (VA _ _ wfΔ tl)).
  - intros * [tl _] [tleq _].
    rewrite (h σ'); unshelve eapply LRTyEqSym.
    2: eapply VA; eassumption.
    rewrite (h σ).
    eapply VAext. 1: exact (validTail vσ).
    eapply symmetrySubstEq. eassumption.
Qed.    

Lemma wk1ValidTyEq {Γ lA A B lF F} (VΓ : [||-v Γ]) nF (VF : [Γ ||-v<lF> F | VΓ]) 
  (VA : [Γ ||-v<lA> A | VΓ]) :
  [Γ ||-v<lA> A ≅ B | VΓ | VA] -> 
  [Γ ,, vass nF F ||-v<lA> A ⟨ @wk1 Γ nF F ⟩ ≅ B ⟨ @wk1 Γ nF F ⟩ | validSnoc nF VΓ VF | wk1ValidTy VΓ _ VF VA].
Proof.
  assert (forall A σ, (A ⟨@wk1 Γ nF F⟩)[σ] = A[↑ >> σ]) as h by (intros; asimpl; now rewrite wk1_ren).
  intros []; constructor; intros.
  rewrite h. irrelevance0.
  1: symmetry; apply h.
  unshelve intuition; tea; now eapply validTail.
Qed.

Lemma soundCtxId {Γ} (VΓ : [||-v Γ]) :
  ∑ wfΓ : [|- Γ], [Γ ||-v tRel : Γ | VΓ | wfΓ].
Proof.
  enough (G : ∑ Δ (e : Δ = Γ) (wfΔ : [|-Δ]), [VΓ |Δ ||-v tRel : Γ | wfΔ]).
  1: now destruct G as [? [-> ?]].
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - exists ε, eq_refl, wfc_nil; constructor.
  - intros * [Δ [e [wfΔ Vid]]].
    exists (Δ,, vass na A[tRel]); unshelve eexists. 
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



End Properties.


 


