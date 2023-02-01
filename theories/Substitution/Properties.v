From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Irrelevance Escape Reflexivity Validity.
From LogRel.Substitution Require Import Irrelevance.

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


Lemma wkSubstS {Γ} (VΓ : [||-v Γ]) : 
  forall {σ  Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ ≤ Δ'),
  [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ' ||-v σ ⟨ ρ ⟩ : Γ | VΓ | wfΔ'].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply ih; eassumption.
    + admit.
Admitted.


Lemma wkSubstSEq {Γ} (VΓ : [||-v Γ]) : 
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ ≤ Δ')
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] -> 
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' | wkSubstS VΓ wfΔ wfΔ' ρ Vσ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - constructor.
  - intros * ih * [tl hd]; unshelve econstructor.
    + admit. (* eapply ih; eassumption. *)
    + admit.
Admitted.

Lemma wk1SubstS {Γ σ Δ nF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ]) (wfF : [Δ |- F]) :
  [Δ ||-v σ : Γ | VΓ | wfΔ ] ->
  [Δ ,, vass nF F ||-v σ ⟨ @wk1 Γ nF F ⟩ : Γ | VΓ | wfc_cons nF wfΔ wfF].
Proof.
Admitted.

Lemma wk1SubstSEq {Γ σ σ' Δ nF F} (VΓ : [||-v Γ])
  (wfΔ : [|- Δ]) (wfF : [Δ |- F])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  let ρ := @wk1 Γ nF F in
  [Δ ,, vass nF F ||-v σ ⟨ ρ ⟩ ≅ σ ⟨ ρ ⟩ : Γ | VΓ | wfc_cons nF wfΔ wfF | wk1SubstS VΓ wfΔ wfF Vσ].
Proof.
Admitted.

Lemma liftSubstS {Γ σ Δ lF nF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc nF VΓ VF in 
  let ρ := wk_up nF F (@wk_id Γ) in
  let wfΔF := wfc_cons nF wfΔ (escape_ (validTy VF wfΔ Vσ)) in
  [Δ ,, vass nF F[σ] ||-v σ ⟨ ρ ⟩ : Γ ,, vass nF F | VΓF | wfΔF ].
Proof.
Admitted.

Lemma liftSubstSEq {Γ σ σ' Δ lF nF F} (VΓ : [||-v Γ]) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F | VΓ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc nF VΓ VF in 
  let ρ := wk_up nF F (@wk_id Γ) in
  let wfΔF := wfc_cons nF wfΔ (escape_ (validTy VF wfΔ Vσ)) in
  let Vliftσ := liftSubstS VΓ wfΔ VF Vσ in
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] ->
  [Δ ,, vass nF F[σ] ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ ,, vass nF F | VΓF | wfΔF | Vliftσ].
Proof.
Admitted.

Set Printing Primitive Projection Parameters.

Lemma wk1ValidTy {Γ lA A lF nF F} (VΓ : [||-v Γ]) (VF : [Γ ||-v<lF> F | VΓ]) :
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

Lemma soundCtxId {Γ} (VΓ : [||-v Γ]) :
  ∑ wfΓ : [|- Γ], [Γ ||-v tRel : Γ | VΓ | wfΓ].
Proof.
  pattern Γ, VΓ; apply validity_rect; clear Γ VΓ.
  - unshelve econstructor. 1: apply wfc_nil. constructor.
  - intros * [wfΓ idΓ]. unshelve econstructor.
    + apply wfc_cons. 1: assumption. eapply escape.  
      assert (A[tRel] = A) as <- by now asimpl.  
      apply (validTy VA wfΓ idΓ).
    + admit.
    (* unshelve eapply consSubstS.
      5:{ unshelve econstructor. }
    replace tRel with (tRel 0 .: S >> tRel). *)
Admitted.
 


End Properties.


 


