Require Import CRelationClasses.
From MetaCoq Require Import PCUICAst.
Require Import Notations Untyped GenericTyping LogicalRelation Properties Reduction LRInduction.
Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProp}.

  Definition escape {l Γ A} :
      [Γ ||-< l > A ] ->
      [Γ |- A].
  Proof.
    intros [[] lr].
    cbn in lr.
    red in lr.
    induction lr as [? [] | ? ? [] | ? ? [] ].
    all: gen_typing.
  Qed.

  Definition escapeEq {l Γ A B} (lr : [Γ ||-< l > A]) :
      [ Γ ||-< l > A ≅ B | lr ] ->
      [Γ |- A ≅ B].
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod].
    + intros [->].
      gen_typing.
    + intros [].
      cbn in *.
      gen_typing.
    + intros [].
      cbn in *.
      gen_typing.
  Qed.

  Definition escapeTerm {l Γ t A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t : A | lr ] ->
    [Γ |- t : A].
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod].
    all: intros [] ; cbn in *.
    all: gen_typing.
  Qed.

  Definition escapeEqTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod].
    - intros [[termL] [termR]] ; cbn in *.
      gen_typing.
    - intros [] ; cbn in *.
      eapply convtm_exp.
      all: gen_typing.
    - intros [[termL] [termR]] ; cbn in *.
      gen_typing.
  Qed.