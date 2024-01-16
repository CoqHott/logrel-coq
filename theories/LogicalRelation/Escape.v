(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProperties}.

  Lemma escape {l Γ s A} :
      [Γ ||-< l > A @ s] ->
      [Γ |- A @ s].
  Proof.
    intros lr.
    pattern l, Γ, s, A, lr.
    eapply LR_rect_TyUr.
    - intros * [].
      now gen_typing.
    - intros ? * [].
      now gen_typing.
    - intros ??? [] **; cbn in *.
      now gen_typing.
    - intros ??? []; gen_typing.
    - intros ??? []; gen_typing.
    - intros ??? [] **; gen_typing.
    - intros ??? [] **; gen_typing.
  Qed.

  Lemma escapeEq {l Γ s A B} (lr : [Γ ||-< l > A @ s]) :
      [ Γ ||-< l > A ≅ B | lr ] ->
      [Γ |- A ≅ B @ s].
  Proof.
    pattern l, Γ, s, A, lr ; eapply LR_rect_TyUr.
    + intros ??? [] [].
      gen_typing.
    + intros ???? [] [].
      cbn in *.
      eapply convty_exp.
      - gen_typing.
      - gen_typing.
      - induction has_univ.
        * gen_typing.
        * gen_typing.
    + intros ??? [] * ? ? [] ; cbn in *.
      gen_typing.
    + intros ??? [] []; gen_typing.
    + intros ??? [] []; gen_typing.
    + intros ??? [] * ? ? []; cbn in *.
      eapply convty_exp. all: gen_typing.
    + intros ??? [???? red] ?? [???? red']; cbn in *. 
      eapply convty_exp; tea;[eapply red | eapply red'].
  Qed.

  Definition escapeTerm {l Γ s t A} (lr : [Γ ||-< l > A @ s]) :
    [Γ ||-< l > t : A | lr ] ->
    [Γ |- t : A].
  Proof.
    pattern l, Γ, s, A, lr ; eapply LR_rect_TyUr.
    - intros ??? [] [] ; cbn in *.
      gen_typing.
    - intros ???? [] [] ; cbn in *.
      gen_typing.
    - intros ??? [] * ?? [] ; cbn in *.
      gen_typing.
    - intros ??? [] []; gen_typing.
    - intros ??? [] []; gen_typing.
    - intros ??? [] * ?? [] ; cbn in *.
      gen_typing.
    - intros ??? IA _ _ []. 
      unfold_id_outTy; destruct IA; cbn in *; gen_typing.
  Qed.

  Definition escapeEqTerm {l Γ s t u A} (lr : [Γ ||-< l > A @ s]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof.
    pattern l, Γ, s, A, lr ; eapply LR_rect_TyUr.
    - intros ??? [] [[] []] ; cbn in *.
      eapply (convtm_conv (A := U)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [ty] [] ; cbn in *.
      eapply (convtm_conv (A := ty)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [dom cod] * ?? [[termL] [termR]] ; cbn in *.
      eapply (convtm_conv (A := tProd dom cod)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [] []; cbn in *.
      eapply (convtm_conv (A := tNat)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ??? [] []; cbn in *.
      eapply (convtm_conv (A := tEmpty)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
    - intros ??? [dom cod] * ?? [[termL] [termR]] ; cbn in *.
      eapply (convtm_conv (A := tSig dom cod)).
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ??? [ty lhs rhs] _ _ []; unfold_id_outTy; cbn in *.
      eapply (convtm_conv (A := tId ty lhs rhs)); [|gen_typing].
      eapply convtm_exp; tea; gen_typing.
  Qed.

  Lemma escapeConv {l Γ s A} (RA : [Γ ||-<l> A @ s]) :
    forall B,
    [Γ ||-<l> A ≅ B | RA] ->
    [Γ |- B @ s].
  Proof.
    pattern l, Γ, s, A, RA; eapply LR_rect_TyUr; clear l Γ A RA.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * ihdom ihcod ? []; gen_typing.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * ??? []; gen_typing.
    - intros * _ _ ? []; gen_typing.
  Qed.
  
End Escapes.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-< _ > _ @ _] |- _] => 
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
