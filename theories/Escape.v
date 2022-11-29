From MetaCoq Require Import PCUICAst.
Require Import Automation Untyped DeclarativeTyping LogicalRelation Properties Reduction LRInduction.
Set Universe Polymorphism.

Definition escape {l Γ A} :
    [Γ ||-< l > A ] ->
    [Γ |- A].
Proof.
  intros [[] lr].
  cbn in lr.
  induction lr as [? [] | ? ? [] | ? ? [] ] using LR_rect.
  - mltt.
  - mltt.
  - mltt.
Qed.

Definition escapeEq {l Γ A B} (lr : [Γ ||-< l > A]) :
    [ Γ ||-< l > A ≅ B | lr ] ->
    [Γ |- A ≅ B].
Proof.
  destruct lr as [[] lr].
  cbn in *.
  induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod] using LR_rect.
  + intros [->].
    mltt.
  + intros [].
    do 2 eapply TypeTrans.
    all: mltt.
  + intros [] ; cbn in *.
    do 2 eapply TypeTrans.
    all: mltt.
Qed.

Definition escapeTerm {l Γ t A} (lr : [Γ ||-< l > A ]) :
  [Γ ||-< l > t : A | lr ] ->
  [Γ |- t : A].
Proof.
  destruct lr as [[] lr].
  cbn in *.
  induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod] using LR_rect.
  all: intros [] ; cbn in *.
  all: mltt.
Qed.

Definition escapeEqTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
  [Γ ||-< l > t ≅ u : A | lr ] ->
  [Γ |- t ≅ u: A].
Proof.
  destruct lr as [[] lr].
  cbn in *.
  induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod] using LR_rect.
  - intros [[termL] [termR]] ; cbn in *.
    eapply (TermTrans (t' := termL)).
    1: mltt.
    eapply (TermTrans (t' := termR)).
    1: mltt.
    eapply TermConv.
    all: mltt.
  - intros [] ; cbn in *.
    eapply (TermTrans (t' := termL)).
    1: mltt.
    eapply (TermTrans (t' := termR)).
    1: mltt.
    eapply TermConv.
    all: mltt.
  - intros [[termL] [termR]] ; cbn in *.
    eapply (TermTrans (t' := termL)).
    1: mltt.
    eapply (TermTrans (t' := termR)).
    1: mltt.
    eapply TermConv.
    all: mltt.
Qed.