From MetaCoq Require Import PCUICAst.
Require Import Automation Untyped MLTTTyping LogicalRelation Properties Reduction LRInduction.
Set Universe Polymorphism.

Definition escape {l Γ A} :
    [Γ ||-< l > A ] ->
    [Γ |- A].
Proof.
  eapply (LR_rect (fun l Γ A _ => [Γ |- A])).
  - intros ? [].
    mltt.
  - intros _ ? ? [] ; cbn in *.
    mltt.
  - intros ? ? ? [] ; cbn in *.
    mltt.
Qed.

Definition escapeEq {l Γ A B} (lr : [Γ ||-< l > A]) :
    [ Γ ||-< l > A ≅ B | lr ] ->
    [Γ |- A ≅ B].
Proof.
  eapply (LR_rect (fun l Γ A lr => forall B : term, [Γ ||-< l > A ≅ B | lr] -> [Γ |- A ≅ B])).
  + intros ? [] ? [->].
    mltt.
  + intros ? ? ? [] ? [].
    do 2 eapply TypeTrans.
    all: mltt.
  + intros ? ? ? [] _ _ _ ? [] ; cbn in *.
    do 2 eapply TypeTrans.
    all: mltt.
Qed.

Definition escapeTerm {l Γ t A} (lr : [Γ ||-< l > A ]) :
  [Γ ||-< l > t : A | lr ] ->
  [Γ |- t : A].
Proof.
  eapply (LR_rect (fun l Γ A lr => forall t : term, [Γ ||-< l > t : A | lr ] -> [Γ |- t : A])).
  - intros ? [] ? [] ; cbn in *.
    mltt.
  - intros ? ? ? [] ? [] ; cbn in *.
    mltt.
  - intros ? ? ? [] _ _ _ ? [] ; cbn in *.
    mltt.
Qed.

Definition escapeEqTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
  [Γ ||-< l > t ≅ u : A | lr ] ->
  [Γ |- t ≅ u: A].
Proof.
  eapply (LR_rect (fun l Γ A lr => forall t u, [Γ ||-< l > t ≅ u : A | lr] -> [Γ |- t ≅ u : A])).
  - intros ? [] ? ? [[termL] [termR]] ; cbn in *.
    eapply (TermTrans (t' := termL)).
    1: mltt.
    eapply (TermTrans (t' := termR)).
    1: mltt.
    eapply TermConv.
    all: mltt.
  - intros ? ? ? [] ? ? [] ; cbn in *.
    eapply (TermTrans (t' := termL)).
    1: mltt.
    eapply (TermTrans (t' := termR)).
    1: mltt.
    eapply TermConv.
    all: mltt.
  - intros ? ? ? [] _ _ _ ? ? [[termL] [termR]] ; cbn in *.
    eapply (TermTrans (t' := termL)).
    1: mltt.
    eapply (TermTrans (t' := termR)).
    1: mltt.
    eapply TermConv.
    all: mltt.
Qed.