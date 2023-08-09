(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
Require Import PeanoNat Nat.
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Monotonicity.
  Context `{GenericTypingProperties}.

Lemma LRTy_Ltrans@{i i' j j' k k' l l'} {lA} (wl wl' : wfLCon) (f : wl' ≤ε wl)
    (Γ : context) (A : term) :
    [ LogRel@{i j k l} lA | Γ ||- A ]< wl > ->
    [ LogRel@{i j k l} lA | Γ ||- A ]< wl' >.
Proof.
  intros [ [] lrA ] ; cbn in lrA.
  induction lrA as [? ? ? [l1 lt1] | ? ? ? [] | ? ? ? [] [] IHdom IHcod|??? []|??? [] |??? []] ; intros.
  - unshelve eapply LRU_.
    unshelve econstructor ; try assumption.
    + now eapply wfc_Ltrans.
    + destruct red.
      split ; try now eapply redty_Ltrans.
      now eapply wft_Ltrans.
  - unshelve eapply LRne_.
    unshelve econstructor ; try assumption.
    + destruct red ; split ; try now eapply redty_Ltrans.
      now eapply wft_Ltrans.
    + now eapply ty_ne_Ltrans.
    + now eapply convneu_Ltrans.
  - unshelve eapply LRPi_.
    cbn in *.
    unshelve econstructor.
    + exact dom.
    + exact cod.
    + exact domN.
    + intros.
      unshelve eapply domRed ; try assumption.
      now eapply wfLCon_le_trans.
    + intros.
      unshelve eapply codomN ; try assumption.
      now eapply wfLCon_le_trans.
      assumption.
    + intros ; cbn in *.
      unshelve eapply codRed ; [ exact l' | ..] ; try assumption.
      * now eapply wfLCon_le_trans.
      * assumption.
      * assumption.
    + destruct red.
      split.
      2: unshelve eapply redty_Ltrans ; try assumption.
      now eapply wft_Ltrans.
    + now eapply wft_Ltrans.
    + now eapply wft_Ltrans.
    + now eapply convty_Ltrans.
    + intros ; now eapply codExt.
    + cbn in *.
      econstructor.
      * intros. now eapply domAd.
      * intros. now eapply codAd.
  - unshelve eapply LRNat_.
    econstructor.
    destruct red.
    split ; try now eapply redty_Ltrans.
    now eapply wft_Ltrans.
  - unshelve eapply LRBool_.
    destruct red.
    econstructor.
    split ; try now eapply redty_Ltrans.
    now eapply wft_Ltrans.
  - unshelve eapply LREmpty_.
    destruct red.
    econstructor.
    split ; try now eapply redty_Ltrans.
    now eapply wft_Ltrans.
Qed.

Lemma LRTyEq_Ltrans@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > ->
            [Γ ||-< lA' > A ≅ B | lrA']< wl' >.
Admitted.


Lemma LRTm_Ltrans@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > ->
            [Γ ||-< lA' > t : A | lrA']< wl' >.
Admitted.


Lemma LRTm_Ltrans'@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > ->
            [Γ ||-< lA' > t : A | lrA']< wl' >.
Admitted.


Lemma LRTmEq_Ltrans@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > ->
            [Γ ||-< lA' > t ≅ u : A | lrA']< wl' >.
Admitted.
(*  intros B eqB.
  destruct lrA as [ [] lrA] ; cbn in *.
  induction lrA.
  
  cbn.
  induction lrA as [? ? ? ? | ? | ? ? A [] [] IHdom IHcod|?? NEA|?? NEA |?? NEA].
  - cbn.
    unshelve eapply LRTyEqIrrelevantCum ; [exact lA |..].
    + eapply LRTy_Ltrans ; try eassumption.
      eapply LRU_ ; econstructor ; eassumption.
    + cbn.
  pattern lA, wl, Γ, A, lrA. apply LR_rect_TyUr. clear lA Γ A lrA.
*)

End Monotonicity.
