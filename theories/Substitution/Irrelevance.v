
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Irrelevance Validity.

Section Irrelevances.
Context `{GenericTypingProperties}.

Lemma irrelevanceSubst {Γ} : forall (VΓ VΓ' : [||-v Γ]) {σ Δ} (wfΔ wfΔ' : [|- Δ]),
  [Δ ||-v σ : Γ | VΓ | wfΔ] -> [Δ ||-v σ : Γ | VΓ' | wfΔ'].
Proof.
  intro VΓ. pattern Γ, VΓ. 
  apply validity_rect; clear Γ VΓ.
  - intros VΓ'; rewrite (invValidityEmpty VΓ'); constructor.
  - intros Γ na A l VΓ VA ih VΓA σ Δ ?? [Vtail Vhd].
    pose proof (h := invValiditySnoc VΓA).
    destruct h as [l' [VΓ' [VA' ->]]]; unshelve econstructor.
    + eapply ih. eassumption.
    + eapply LRTmRedIrrelevant; eassumption.
Qed.

Lemma irrelevanceSubstEq {Γ} : forall (VΓ VΓ' : [||-v Γ]) {σ σ' Δ} (wfΔ wfΔ' : [|- Δ])
  (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]) (Vσ' : [Δ ||-v σ : Γ | VΓ' | wfΔ']),
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ] -> [Δ ||-v σ ≅ σ' : Γ | VΓ' | wfΔ' | Vσ'].
Proof.
  intro VΓ. pattern Γ, VΓ.
  apply validity_rect; clear Γ VΓ.
  - intros VΓ'; rewrite (invValidityEmpty VΓ'); constructor.
  - intros ?????? ih VΓA * [].
    pose proof (h := invValiditySnoc VΓA).
    destruct h as [? [? [? ->]]]; unshelve econstructor.
    + eapply ih. eassumption.
    + eapply LRTmEqIrrelevant ; eassumption.
Qed.

Lemma irrelevanceValidity {Γ} : forall (VΓ VΓ' : [||-v Γ]) {l A},
  [Γ ||-v<l> A | VΓ] -> [Γ ||-v<l> A | VΓ'].
Proof.
  intros VΓ VΓ' l A [VA VAext]; unshelve econstructor; intros.
  - unshelve eapply VA. 2: eapply irrelevanceSubst. all:eassumption.
  - eapply VAext; [eapply irrelevanceSubst| eapply irrelevanceSubstEq]; eassumption.
Qed.  



