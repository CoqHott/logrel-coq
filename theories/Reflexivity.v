From MetaCoq Require Import PCUICAst.
Require Import Notations Untyped Automation MLTTTyping LogicalRelation Properties Reduction LRInduction Escape.

Definition LRTyEqRefl {l Γ A eqTy redTm eqTm}
  (lr : LRl l Γ A eqTy redTm eqTm) : eqTy A.
Proof.
  induction lr as [ ? [] | ? ? [] | ? ? [] IHdom IHcod] using LR_rect.
  + econstructor.
    reflexivity.
  + now econstructor.
  + econstructor.
    all: mltt.
Qed.

Corollary LRTyEqRefl_ {l Γ A} (lr : [ Γ ||-< l > A ] ) : [ Γ ||-< l > A ≅ A | lr ].
Proof.
  destruct lr as [[] lr].
  cbn in *.
  now eapply LRTyEqRefl.
Qed.

Definition LRTmEqRefl {l Γ A eqTy redTm eqTm} (lr : LRl l Γ A eqTy redTm eqTm) :
  forall t, redTm t -> eqTm t t.
Proof.
  induction lr as [ ? [? []] | ? ? [] | ? ? [] IHdom IHcod] using LR_rect.
  - intros t [? ? ? [[] rel]] ; cbn in *.
    assert (eqTy t)
      by now eapply (LRTyEqRefl (l := zero)).
    unshelve econstructor.
    all : cbn.
    1-2: econstructor ; tea ; cbn.
    1-3,5: now eapply (LRbuild (l := zero)).
    all: cbn.
    all: mltt.
  - intros t [].
    econstructor ; cbn in *.
    1-4: eassumption.
    eapply TermConv.
    all: mltt.
  - intros t [].
    unshelve econstructor ; cbn in *.
    1-2: now econstructor.
    all: cbn.
    all: mltt.
Qed.

Definition LREqTermRefl_ {l Γ A t} (lr : [ Γ ||-< l > A ] ) : 
    [ Γ ||-< l > t : A | lr ] ->
    [ Γ ||-< l > t ≅ t : A | lr ].
Proof.
  destruct lr as [[] lr].
  cbn in *.
  now eapply LRTmEqRefl.
Qed.