(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
Require Import PeanoNat Nat.
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProperties}.

  Lemma escape {l wl Γ A} :
      [Γ ||-< l > A ]< wl > ->
      [Γ |- A]< wl >.
  Proof.
    intros lr.
    pattern l, wl,  Γ, A, lr.
    eapply LR_rect_TyUr.
    - intros * [].
      now gen_typing.
    - intros ? * [].
      now gen_typing.
    - intros ???? [] **; cbn in *.
      now gen_typing.
    - intros ???? []; gen_typing.
    - intros ???? []; gen_typing.
    - intros ???? []; gen_typing.
  Qed.

  Lemma Wescape {l wl Γ A} : W[ Γ ||-< l > A ]< wl > -> [Γ |- A]< wl >.
  Proof.
    intros [].
    remember (WN - length wl).
    revert wl Heqn WRed.
    induction n.
    - intros.
      eapply escape.
      eapply WRed.
      + now eapply wfLCon_le_id.
      + eapply PeanoNat.Nat.sub_0_le.
        now rewrite Heqn.
    - intros.
      unshelve eapply wft_ϝ.
      + exact (LCon_newElt wl).
      + now eapply newElt_newElt.
      + eapply IHn.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
      + eapply IHn.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
  Qed.
         
  Lemma escapeEq {l wl Γ A B} (lr : [Γ ||-< l > A]< wl >) :
      [ Γ ||-< l > A ≅ B | lr ]< wl > ->
      [Γ |- A ≅ B]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    + intros ???? [] []. 
      gen_typing.
    + intros ???? [] [].
      cbn in *.
      eapply convty_exp.
      all: gen_typing.
    + intros ???? [] * ? ? [] ; cbn in *.
      gen_typing.
    + intros ???? [] []; gen_typing.
    + intros ???? [] []; gen_typing.
    + intros ???? [] []; gen_typing.
  Qed.

  Lemma WescapeEq {l wl Γ A B} (lr : W[Γ ||-< l > A]< wl >) :
      W[ Γ ||-< l > A ≅ B | lr ]< wl > ->
      [Γ |- A ≅ B]< wl >.
  Proof.
    intros [].
    destruct lr as [WN WRed].
    remember ((max WN WNEq) - length wl).
    revert wl Heqn WRed WRedEq.
    induction n ; intros.
    - eapply escapeEq.
      unshelve eapply WRedEq.
      + now eapply wfLCon_le_id.
      + etransitivity.
        eapply Nat.le_max_l.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
      + etransitivity.
        eapply Nat.le_max_r.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
    - unshelve eapply convty_ϝ.
      + exact (LCon_newElt wl).
      + now eapply newElt_newElt.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedEq.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedEq.
Qed.

  Definition escapeTerm {l wl Γ t A} (lr : [Γ ||-< l > A ]< wl >) :
    [Γ ||-< l > t : A | lr ]< wl > ->
    [Γ |- t : A]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ???? [] [] ; cbn in *.
      gen_typing.
    - intros ???? [] [] ; cbn in *.
      gen_typing.
    - intros ???? [] * ?? [] ; cbn in *.
      gen_typing.
    - intros ???? [] []; gen_typing.
    - intros ???? [] []; gen_typing.
    - intros ???? [] []; gen_typing.
  Qed.

  Definition WescapeTerm {l wl Γ t A} (lr : W[Γ ||-< l > A ]< wl >) :
    W[Γ ||-< l > t : A | lr ]< wl > ->
    [Γ |- t : A]< wl >.
  Proof.
   intros [].
    destruct lr as [WN WRed].
    remember ((max WN WNTm) - length wl).
    revert wl Heqn WRed WRedTm.
    induction n ; intros.
    - eapply escapeTerm.
      unshelve eapply WRedTm.
      + now eapply wfLCon_le_id.
      + etransitivity.
        eapply Nat.le_max_l.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
      + etransitivity.
        eapply Nat.le_max_r.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
    - unshelve eapply ty_ϝ.
      + exact (LCon_newElt wl).
      + now eapply newElt_newElt.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedTm.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedTm.
  Qed.
  
  Definition escapeEqTerm {l wl Γ t u A} (lr : [Γ ||-< l > A ]< wl >) :
    [Γ ||-< l > t ≅ u : A | lr ]< wl > ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ???? [] [[] []] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] [] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] * ?? [[termL] [termR]] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
  Qed.

  Definition WescapeEqTerm {l wl Γ t u A} (lr : W[Γ ||-< l > A ]< wl >) :
    W[Γ ||-< l > t ≅ u : A | lr ]< wl > ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    intros [].
    destruct lr as [WN WRed].
    remember ((max WN WNTmEq) - length wl).
    revert wl Heqn WRed WRedTmEq.
    induction n ; intros.
    - eapply escapeEqTerm.
      unshelve eapply WRedTmEq.
      + now eapply wfLCon_le_id.
      + etransitivity.
        eapply Nat.le_max_l.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
      + etransitivity.
        eapply Nat.le_max_r.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
    - unshelve eapply convtm_ϝ.
      + exact (LCon_newElt wl).
      + now eapply newElt_newElt.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedTmEq.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedTmEq.
  Qed.
  
  Lemma escapeConv {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) :
    forall B,
    [Γ ||-<l> A ≅ B | RA]< wl > ->
    [Γ |- B]< wl >.
  Proof.
    pattern l, wl, Γ, A, RA; eapply LR_rect_TyUr; clear l Γ A RA.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * ihdom ihcod ? []; gen_typing.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
  Qed.

  Lemma WescapeConv {l wl Γ A} (RA : W[Γ ||-<l> A]< wl >) :
    forall B,
    W[Γ ||-<l> A ≅ B | RA]< wl > ->
    [Γ |- B]< wl >.
  Proof.
    intros B [].
    destruct RA as [WN WRed].
    remember ((max WN WNEq) - length wl).
    revert wl Heqn WRed WRedEq.
    induction n ; intros.
    - eapply escapeConv.
      unshelve eapply WRedEq.
      + now eapply wfLCon_le_id.
      + etransitivity.
        eapply Nat.le_max_l.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
      + etransitivity.
        eapply Nat.le_max_r.
        eapply Nat.sub_0_le.
        now rewrite Heqn.
    - unshelve eapply wft_ϝ.
      + exact (LCon_newElt wl).
      + now eapply newElt_newElt.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedEq.
      + unshelve eapply IHn.
        * intros.
          unshelve eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * cbn.
          erewrite PeanoNat.Nat.sub_succ_r.
          rewrite <- Heqn.
          reflexivity.
        * intros.
          now unshelve eapply WRedEq.
  Qed.

  
  
End Escapes.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-< _ > _]< _ > |- _] => 
    let X := fresh "Esc" H in
    try pose proof (X := escape H) ;
    block H
  | [H : [_ ||-<_> _ ≅ _ | ?RA ]< _ > |- _] =>
    let X := fresh "Esc" H in
    try pose proof (X := escapeEq RA H) ;
    block H
  | [H : [_ ||-<_> _ : _ | ?RA]< _ > |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeTerm RA H) ;
    block H
  | [H : [_ ||-<_> _ ≅ _ : _ | ?RA]< _ > |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeEqTerm RA H) ;
    block H
  end; unblock.
