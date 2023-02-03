From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction LRInduction Escape.

Set Universe Polymorphism.

Section Reflexivities.
  Context `{GenericTypingProperties}.

  Definition LRTyEqRefl0 {Γ A eqTy redTm eqTm}
    (lr : LogRel0 Γ A eqTy redTm eqTm) : eqTy A.
  Proof.
    induction lr as [ ? [] | ? ? [] | ? ? [] ? IHdom IHcod].
    all: now econstructor.
  Qed.

  Definition LRTyEqRefl {l Γ A eqTy redTm eqTm}
    (lr : LogRel l Γ A eqTy redTm eqTm) : eqTy A.
  Proof.
    induction lr as [ ? [] | ? ? [] | ? ? [] ? IHdom IHcod].
    all: now econstructor.
  Qed.

  Corollary LRTyEqRefl_ {l Γ A} (lr : [ Γ ||-< l > A ] ) : [ Γ ||-< l > A ≅ A | lr ].
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    now eapply LRTyEqRefl.
  Qed.

  Definition LRTmEqRefl {l Γ A eqTy redTm eqTm} (lr : LogRel l Γ A eqTy redTm eqTm) :
    forall t, redTm t -> eqTm t t.
  Proof.
    induction lr as [ ? [? []] | ? ? [] | ? ? [] IHdom IHcod].
    - intros t [? ? ? ? [[] rel]] ; cbn in *.
      assert (eqTy t) by now eapply LRTyEqRefl0.  
      unshelve econstructor.
      all : cbn.
      1-2: econstructor ; tea ; cbn.
      1-3,5: now eapply LRbuild0.
      all: easy.
    - intros t [].
      econstructor ; cbn in *.
      all: eassumption.
    - intros t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn.
      all: now eauto.
  Qed.

  Definition LREqTermRefl_ {l Γ A t} (lr : [ Γ ||-< l > A ] ) : 
      [ Γ ||-< l > t : A | lr ] ->
      [ Γ ||-< l > t ≅ t : A | lr ].
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    now eapply LRTmEqRefl.
  Qed.

End Reflexivities.
