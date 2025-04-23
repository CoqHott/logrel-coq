(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms GenericTyping Monad LogicalRelation.
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
    - intros ???? []; gen_typing.
    - intros ???? []; gen_typing.
  Qed.

  Lemma Wescape {l wl Γ A} :
    W[ Γ ||-< l > A ]< wl > -> [Γ |- A]< wl >.
  Proof.
    intros [].
    revert WRed ; induction WT ; cbn ; intros.
    - eapply escape.
      eapply WRed.
      now eapply wfLCon_le_id.
    - unshelve eapply (wft_ϝ (ne := ne)).
      + intros m ; eapply X.
        intros wl' Hover ; eapply WRed.
        assert (Hyp := over_tree_le Hover _ _ (in_here_l _)).
        now erewrite (decidInLCon_true _ Hyp).
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
    + intros ???? [] * ? ? []; cbn in *.
      eapply convty_exp. all: try gen_typing.
    + intros ???? [???? red] ?? [???? red']; cbn in *. 
      eapply convty_exp; tea;[eapply red | eapply red'].
  Qed.

  Lemma WescapeEq {l wl Γ A B} (lr : W[Γ ||-< l > A]< wl >) :
      W[ Γ ||-< l > A ≅ B | lr ]< wl > ->
      [Γ |- A ≅ B]< wl >.
  Proof.
    intros [].
    destruct lr as [WT WRed] ; cbn in *.
    pose (d := DTree_fusion _ WT WTEq).
    assert ({dWRed : forall wl' : wfLCon, over_tree wl wl' d -> [Γ ||-< l > A ]< wl' > &
              forall (wl' : wfLCon) (Hover : over_tree wl wl' d), [dWRed wl' Hover | _ ||- _ ≅ B ]< _ >}) as [dWRed dWRedEq].
    { exists (fun wl' Hover => WRed wl' (over_tree_fusion_l Hover)).
      intros wl' Hover ; cbn. eapply WRedEq.
      eapply over_tree_fusion_r. eassumption.
    }
    revert dWRed dWRedEq ; generalize d ; clear d WT WRed WTEq WRedEq.
    intros d.
    induction d as [ | wl' n ne ? IHEqt ? IHEqf] ; cbn ; intros.
    - unshelve eapply escapeEq ; [assumption | ..].
      1: eapply dWRed.
      2: eapply dWRedEq.
      all: now apply wfLCon_le_id.
    - unshelve eapply (convty_ϝ (ne := ne)).
      + intros m ; eapply IHEqt.
        intros wl'' Hover ; eapply dWRedEq.
        Unshelve.
        assert (Hyp := over_tree_le Hover _ _ (in_here_l _)).
        now erewrite (decidInLCon_true _ Hyp).
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
    - intros ???? [] * ?? [] ; cbn in *.
      gen_typing.
    - intros ???? IA _ _ []. 
      unfold_id_outTy; destruct IA; cbn in *; gen_typing.
  Qed.

  Definition WescapeTerm {l wl Γ t A} (lr : W[Γ ||-< l > A ]< wl >) :
    W[Γ ||-< l > t : A | lr ]< wl > ->
    [Γ |- t : A]< wl >.
  Proof.
    intros [].
    destruct lr as [WT WRed].
    pose (d := DTree_fusion _ WT WTTm).
    assert ({dWRed : forall wl' : wfLCon, over_tree wl wl' d -> [Γ ||-< l > A ]< wl' > &
                      forall (wl' : wfLCon) (Hover : over_tree wl wl' d), [dWRed wl' Hover | _ ||- t : _ ]< _ >})
      as [dWRed dWRedTm].
    { exists (fun wl' Hover => WRed wl' (over_tree_fusion_l Hover)).
      intros wl' Hover ; cbn. eapply WRedTm.
      eapply over_tree_fusion_r. eassumption.
    }
    revert dWRed dWRedTm ; generalize d ; clear d WT WRed WTTm WRedTm.
    intros d.
    induction d as [ | wl' n ne ? IHEqt ? IHEqf] ; cbn ; intros.
    - unshelve eapply escapeTerm ; [assumption | ..].
      1: eapply dWRed ; [now eapply wfLCon_le_id | ..].
      now eapply dWRedTm.
    - unshelve eapply (ty_ϝ (ne := ne)).
      + intros m ; eapply IHEqt.
        intros wl'' Hover ; eapply dWRedTm.
        Unshelve.
        assert (Hyp := over_tree_le Hover _ _ (in_here_l _)).
        now erewrite (decidInLCon_true _ Hyp).
  Qed.
   
  Definition escapeEqTerm {l wl Γ t u A} (lr : [Γ ||-< l > A ]< wl >) :
    [Γ ||-< l > t ≅ u : A | lr ]< wl > ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ???? [] [[] []] ; cbn in *.
      eapply (convtm_conv (A := U)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [ty] [] ; cbn in *.
      assert (isPosType ty).
      {
      constructor.
      now eapply convneu_whne. 
      }
      eapply (convtm_conv (A := ty)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [dom cod] * ?? [[termL] [termR]] ; cbn in *.
      eapply (convtm_conv (A := tProd dom cod)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] []; cbn in *.
      eapply (convtm_conv (A := tNat)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [] []; cbn in *.
      eapply (convtm_conv (A := tBool)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [] []; cbn in *.
      eapply (convtm_conv (A := tEmpty)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [dom cod] * ?? [[termL] [termR]] ; cbn in *.
      eapply (convtm_conv (A := tSig dom cod)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [ty lhs rhs] _ _ []; unfold_id_outTy; cbn in *.
      eapply (convtm_conv (A := tId ty lhs rhs)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
  Qed.

  Definition WescapeEqTerm {l wl Γ t u A} (lr : W[Γ ||-< l > A ]< wl >) :
    W[Γ ||-< l > t ≅ u : A | lr ]< wl > ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    intros [].
    destruct lr as [WT WRed].
    pose (d := DTree_fusion _ WT WTTmEq).
    assert ({H : forall wl' : wfLCon, over_tree wl wl' d -> [Γ ||-< l > A ]< wl' > &
                   forall (wl' : wfLCon) (Hover : over_tree wl wl' d), [H wl' Hover | _ ||- t  ≅ u : _ ]< _ >})
      as [dWRed dWRedTmEq].
    { exists (fun wl' Hover => WRed wl' (over_tree_fusion_l Hover)).
      intros wl' Hover ; cbn ; eapply WRedTmEq.
      eapply over_tree_fusion_r ; eassumption.
    }
    revert dWRed dWRedTmEq ; generalize d ; clear d WT WRed WTTmEq WRedTmEq.
    intros d.
    induction d as [ | wl' n ne ? IHEqt ? IHEqf] ; cbn ; intros.
    - eapply escapeEqTerm.
      unshelve eapply dWRedTmEq.
      now eapply wfLCon_le_id.
    - unshelve eapply (convtm_ϝ (ne := ne)).
      + intros m ; eapply IHEqt.
        intros wl'' Hover ; unshelve eapply dWRedTmEq.
        assert (Hyp := over_tree_le Hover _ _ (in_here_l _)).
        now erewrite (decidInLCon_true _ Hyp).
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
    - intros * ??? []; gen_typing.
    - intros * _ _ ? []; gen_typing.
  Qed.

  Lemma WescapeConv {l wl Γ A} (RA : W[Γ ||-<l> A]< wl >) :
    forall B,
    W[Γ ||-<l> A ≅ B | RA]< wl > ->
    [Γ |- B]< wl >.
  Proof.
    intros B [].
    destruct RA as [WT WRed].
    pose (d := DTree_fusion _ WT WTEq) ; cbn in *.
    assert ({H : forall wl' : wfLCon, over_tree wl wl' d -> [Γ ||-< l > A ]< wl' > &
                   forall (wl' : wfLCon) (Hover : over_tree wl wl' d), [H wl' Hover | _ ||- _ ≅ B ]< _ >})
      as [dWRed dWRedEq].
    { exists (fun wl' Hover => WRed wl' (over_tree_fusion_l Hover)).
      intros wl' Hover ; cbn ; eapply WRedEq.
      eapply over_tree_fusion_r ; eassumption.
    }
    revert dWRed dWRedEq ; generalize d ; clear d WT WRed WTEq WRedEq.
    intros d.
    induction d as [ | wl' n ne ? IHEqt ? IHEqf] ; cbn ; intros.
    - eapply escapeConv.
      unshelve eapply dWRedEq.
      now eapply wfLCon_le_id.
    - unshelve eapply (wft_ϝ (ne := ne)).
      + intros m ; eapply IHEqt.
        intros wl'' Hover ; unshelve eapply dWRedEq.
        assert (Hyp := over_tree_le Hover _ _ (in_here_l _)).
        now erewrite (decidInLCon_true m Hyp).
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

Ltac Wescape :=
  repeat lazymatch goal with
  | [H : W[_ ||-< _ > _]< _ > |- _] => 
    let X := fresh "Esc" H in
    try pose proof (X := Wescape H) ;
    block H
  | [H : W[_ ||-<_> _ ≅ _ | ?RA ]< _ > |- _] =>
    let X := fresh "Esc" H in
    try pose proof (X := WescapeEq RA H) ;
    block H
  | [H : W[_ ||-<_> _ : _ | ?RA]< _ > |- _] =>
    let X := fresh "R" H in
    try pose proof (X := WescapeTerm RA H) ;
    block H
  | [H : W[_ ||-<_> _ ≅ _ : _ | ?RA]< _ > |- _] =>
    let X := fresh "R" H in
    try pose proof (X := WescapeEqTerm RA H) ;
    block H
  end; unblock.
