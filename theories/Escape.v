Require Import CRelationClasses.
From MetaCoq Require Import PCUICAst.
Require Import Notations Untyped GenericTyping LogicalRelation Properties Reduction LRInduction.
Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProp}.

  Definition escape {l Γ A eqTy redTm eqTm} :
    LRl l Γ A eqTy redTm eqTm ->
    [Γ |- A].
  Proof.
    induction 1 as [? [] | ? ? [] | ? ? [] ].
    all: gen_typing.
  Qed.

  Corollary escape_ {l Γ A} :
      [Γ ||-< l > A ] ->
      [Γ |- A].
  Proof.
    intros [[] lr].
    now eapply escape.
  Qed.

  Definition escapeEq {l Γ A eqTy redTm eqTm}
    (lr : LRl l Γ A eqTy redTm eqTm) {B} :
    eqTy B ->
    [Γ |- A ≅ B].
  Proof.
    induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod].
    + intros [->].
      gen_typing.
    + intros [].
      cbn in *.
      eapply convty_exp.
      all: gen_typing.
    + intros [].
      cbn in *.
      gen_typing.
  Qed.

  Corollary escapeEq_ {l Γ A B} (lr : [Γ ||-< l > A]) :
      [ Γ ||-< l > A ≅ B | lr ] ->
      [Γ |- A ≅ B].
  Proof.
    intros.
    destruct lr as [[] lr] ; cbn in *.
    now eapply escapeEq.
  Qed.

  Definition escapeTerm {l Γ A eqTy redTm eqTm}
    (lr : LRl l Γ A eqTy redTm eqTm) {t} :
    redTm t ->
    [Γ |- t : A].
  Proof.
    induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod].
    all: intros [] ; cbn in *.
    all: gen_typing.
  Qed. 

  Definition escapeTerm_ {l Γ t A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t : A | lr ] ->
    [Γ |- t : A].
  Proof.
    intros.
    destruct lr as [[] lr] ; cbn in *.
    now eapply escapeTerm.
  Qed.

  Definition escapeEqTerm {l Γ A eqTy redTm eqTm}
    (lr : LRl l Γ A eqTy redTm eqTm) {t u} :
    eqTm t u ->
    [Γ |- t ≅ u : A].
  Proof.
    induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod].
    - intros [[termL] [termR]] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros [] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros [[termL] [termR]] ; cbn in *.
      gen_typing.
  Qed.

  Definition escapeEqTerm_ {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof.
    intros.
    destruct lr as [[] lr] ; cbn in *.
    now eapply escapeEqTerm.
  Qed.
  
End Escapes.