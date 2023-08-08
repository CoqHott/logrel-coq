From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Substitution Require Import Properties Irrelevance.

Set Universe Polymorphism.

Section Conversion.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma conv {Γ t A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Γ ||-v<l> t : B | VΓ | VB].
Proof.
  constructor; intros; [eapply LRTmRedConv| eapply LRTmEqRedConv].
  1,3: now unshelve now eapply validTyEq.
  1: now eapply validTm.
  now eapply validTmExt.
Qed.

Lemma convsym {Γ t A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t : B | VΓ | VB]) :
  [Γ ||-v<l> t : A | VΓ | VA].
Proof.
  constructor; intros; [eapply LRTmRedConv| eapply LRTmEqRedConv].
  1,3: unshelve eapply LRTyEqSym; tea; [|now unshelve now eapply validTyEq].
  1:  now unshelve now eapply validTm.
  now eapply validTmExt.
Qed.

Lemma convEq {Γ t u A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : B | VΓ | VB].
Proof.
  constructor; intros; eapply LRTmEqRedConv.
  1: now unshelve now eapply validTyEq.
  now eapply validTmEq.
Qed.


Lemma convSubstCtx1 {Γ Δ A B l σ} 
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA : [||-v Γ ,, A]) 
  (VΓB : [||-v Γ ,, B]) 
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (Vσ : [_ ||-v σ : _ | VΓA | wfΔ]) :
  [_ ||-v σ : _ | VΓB | wfΔ].
Proof.
  pose proof (invValiditySnoc VΓA) as [? [? [?]]]; subst.
  pose proof (invValiditySnoc VΓB) as [? [? [?]]]; subst.
  eapply irrelevanceSubstExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstS.
  1: epose (validTail Vσ); irrValid.
  eapply LRTmRedConv.
  2: irrelevanceRefl; eapply validHead.
  now eapply validTyEq.
  Unshelve. 6: tea.
    2: eapply irrelevanceSubst; now eapply validTail.
    tea.
Qed.

Lemma convSubstEqCtx1 {Γ Δ A B l σ σ'} 
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA : [||-v Γ ,, A]) 
  (VΓB : [||-v Γ ,, B]) 
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (Vσ : [_ ||-v σ : _ | VΓA | wfΔ]) 
  (Vσ' : [_ ||-v σ' : _ | VΓA | wfΔ]) 
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA | wfΔ | Vσ]) 
  (VσB : [_ ||-v σ : _ | VΓB | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB | wfΔ | VσB].
Proof.
  pose proof (invValiditySnoc VΓA) as [? [? [?]]]; subst.
  pose proof (invValiditySnoc VΓB) as [? [? [?]]]; subst.
  eapply irrelevanceSubstEq.
  eapply irrelevanceSubstEqExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstSEq'.
  8: now eapply eqTail.
  3: irrValid.
  3: eapply LRTmEqRedConv.
  4: now eapply eqHead.
  2: irrelevanceRefl; eapply validTyEq; irrValid.
  eapply LRTmRedConv.
  2: irrelevanceRefl; eapply validHead.
  eapply validTyExt.
  1: now eapply validTail.
  eapply reflSubst.
  Unshelve.
  1: now rewrite scons_eta'.
  9: tea.
  7: tea.
  2,6: irrValid.
  1,2: tea.
  1,2: eapply irrelevanceSubst; now eapply validTail.
Qed.


Lemma convCtx1 {Γ A B P l} 
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A]) 
  (VΓB : [||-v Γ ,, B]) 
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VP : [_ ||-v<l> P | VΓA]) :
  [_ ||-v<l> P | VΓB].
Proof.
  opector; intros.
  - eapply validTy; tea; eapply convSubstCtx1; tea; now eapply symValidEq.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea. 
    1,2:  eapply convSubstCtx1; tea; now eapply symValidEq.
    eapply convSubstEqCtx1; cycle 2; tea; now eapply symValidEq.
    Unshelve. all: tea.
Qed.

Lemma convEqCtx1 {Γ A B P Q l} 
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A]) 
  (VΓB : [||-v Γ ,, B]) 
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VP : [_ ||-v<l> P | VΓA])
  (VPB : [_ ||-v<l> P | VΓB])
  (VPQ : [_ ||-v<l> P ≅ Q | VΓA | VP]) :
  [_ ||-v<l> P ≅ Q | VΓB | VPB].
Proof.
  constructor; intros; irrelevanceRefl.
  eapply validTyEq; tea.
  Unshelve. 1: tea. 
  unshelve eapply convSubstCtx1; cycle 5; tea; now eapply symValidEq.
Qed.

Lemma convSubstCtx2 {Γ Δ A1 B1 A2 B2 l σ} 
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1) 
  (VΓB1 := validSnoc VΓ VB1) 
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2) 
  (VΓB12 := validSnoc VΓB1 VB2') 
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]) :
  [_ ||-v σ : _ | VΓB12 | wfΔ].
Proof.
  eapply irrelevanceSubstExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstS.
  + eapply convSubstCtx1; tea.
    now eapply validTail.
  + eapply LRTmRedConv.
    2: now eapply validHead.
    eapply validTyEq; tea.
  Unshelve. all: tea.
Qed.

Lemma convSubstCtx2' {Γ Δ A1 B1 A2 B2 l σ} 
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA1 : [||-v Γ ,, A1]) 
  (VΓA12 : [||-v Γ ,, A1 ,, A2]) 
  (VΓB12 : [||-v Γ ,, B1 ,, B2]) 
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]) :
  [_ ||-v σ : _ | VΓB12 | wfΔ].
Proof.
  eapply irrelevanceSubst.
  eapply convSubstCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.

Lemma convSubstEqCtx2 {Γ Δ A1 B1 A2 B2 l σ σ'} 
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1) 
  (VΓB1 := validSnoc VΓ VB1) 
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2) 
  (VΓB12 := validSnoc VΓB1 VB2') 
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]) 
  (Vσ' : [_ ||-v σ' : _ | VΓA12 | wfΔ]) 
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ | Vσ]) 
  (VσB : [_ ||-v σ : _ | VΓB12 | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ | VσB].
Proof.
  eapply irrelevanceSubstEq.
  eapply irrelevanceSubstEqExt.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstSEq'.
  8:{ eapply convSubstEqCtx1; tea.
    1: now eapply validTail.
    now eapply eqTail.
  }
  3,4: irrValid.
  2: eapply convSubstCtx1; tea; now eapply validTail. 
  3: eapply LRTmEqRedConv.
  4: now eapply eqHead.
  2: irrelevanceRefl; eapply validTyEq; irrValid.
  eapply LRTmRedConv.
  2: irrelevanceRefl; eapply validHead.
  eapply validTyExt.
  1: now eapply validTail.
  eapply reflSubst.
  Unshelve.
  1: now rewrite scons_eta'.
  11: tea.
  1,2,6: irrValid.
  1: tea.
  2: eapply convSubstCtx1; tea.
  1,2: now eapply validTail.
Qed. 

Lemma convSubstEqCtx2' {Γ Δ A1 B1 A2 B2 l σ σ'} 
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 : [||-v Γ ,, A1]) 
  (VΓB1 : [||-v Γ ,, B1]) 
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' : [_ ||-v<l> B2 | VΓB1])
  (VΓA12 : [||-v Γ ,, A1 ,, A2]) 
  (VΓB12 : [||-v Γ ,, B1,, B2]) 
  (Vσ : [_ ||-v σ : _ | VΓA12 | wfΔ]) 
  (Vσ' : [_ ||-v σ' : _ | VΓA12 | wfΔ]) 
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ | Vσ]) 
  (VσB : [_ ||-v σ : _ | VΓB12 | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ | VσB].
Proof.
  eapply irrelevanceSubstEq.
  eapply convSubstEqCtx2; irrValid.
  Unshelve.  all: tea; irrValid.
Qed.

Lemma convCtx2 {Γ A1 B1 A2 B2 P l} 
  (VΓ : [||-v Γ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1) 
  (VΓB1 := validSnoc VΓ VB1) 
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2) 
  (VΓB12 := validSnoc VΓB1 VB2') 
  (VP : [_ ||-v<l> P | VΓA12]) :
  [_ ||-v<l> P | VΓB12].
Proof.
  assert [_ ||-v<l> A2 | VΓB1] by now eapply convCtx1.
  assert [_ ||-v<l> B1 ≅ A1 | _ | VB1] by now eapply symValidEq.
  assert [_ ||-v<l> B2 ≅ A2 | _ | VB2'] by (eapply convEqCtx1; tea; now eapply symValidEq).
  opector; intros.
  - eapply validTy; tea; now eapply convSubstCtx2'.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea. 
    1,2:  now eapply convSubstCtx2'.
    eapply convSubstEqCtx2'; tea.
    Unshelve. tea.
Qed.

Lemma convCtx2' {Γ A1 A2 B1 B2 P l} 
  (VΓ : [||-v Γ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 : [||-v Γ ,, A1]) 
  (VΓB1 : [||-v Γ ,, B1]) 
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' : [_ ||-v<l> B2 | VΓB1])
  (VΓA12 : [||-v Γ ,, A1 ,, A2]) 
  (VΓB12 : [||-v Γ ,, B1,, B2])
  (VP : [_ ||-v<l> P | VΓA12]) :
  [_ ||-v<l> P | VΓB12].
Proof.
  eapply irrelevanceValidity; eapply convCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.


End Conversion.
