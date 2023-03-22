(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProperties}.

  Lemma escape {l Γ A} :
      [Γ ||-< l > A ] ->
      [Γ |- A].
  Proof.
    intros lr.
    pattern l, Γ, A, lr.
    eapply LR_rect_TyUr.
    - intros * [].
      now gen_typing.
    - intros ? * [].
      now gen_typing.
    - intros ??? [] **; cbn in *.
      now gen_typing.
    - intros ??? []; gen_typing.
  Qed.

  Lemma escapeEq {l Γ A B} (lr : [Γ ||-< l > A]) :
      [ Γ ||-< l > A ≅ B | lr ] ->
      [Γ |- A ≅ B].
  Proof.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr.
    + intros ??? [] []. 
      gen_typing.
    + intros ??? [] [].
      cbn in *.
      eapply convty_exp.
      all: gen_typing.
    + intros ??? [] * ? ? [] ; cbn in *.
      gen_typing.
    + intros ??? [] []; gen_typing.
  Qed.

  Definition escapeTerm {l Γ t A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t : A | lr ] ->
    [Γ |- t : A].
  Proof.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ??? [] [] ; cbn in *.
      gen_typing.
    - intros ??? [] [] ; cbn in *.
      gen_typing.
    - intros ??? [] * ?? [] ; cbn in *.
      gen_typing.
    - intros ??? [] []; gen_typing.
  Qed.

  Definition escapeEqTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof.
    pattern l, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ??? [] [[] []] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [] [] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [] * ?? [[termL] [termR]] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
  Qed.
  
End Escapes.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-< _ > _] |- _] => 
    let X := fresh "Esc" H in
    try pose proof (X := escape H) ;
    block H
  | [H : [_ ||-<_> _ ≅ _ | ?RA ] |- _] =>
    let X := fresh "Esc" H in
    try pose proof (X := escapeEq RA H) ;
    block H
  | [H : [_ ||-<_> _ : _ | ?RA] |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeTerm RA H) ;
    block H
  | [H : [_ ||-<_> _ ≅ _ : _ | ?RA] |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeEqTerm RA H) ;
    block H
  end; unblock.