(** * LogRel.LogicalRelation.Reflexivity: reflexivity of the logical relation. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.

Section Reflexivities.
  Context `{GenericTypingProperties}.

  Definition LRTyEqRefl {l Γ A eqTy redTm eqTm}
    (lr : LogRel l Γ A eqTy redTm eqTm) : eqTy A.
  Proof.
    pattern l, Γ, A, eqTy, redTm, eqTm, lr; eapply LR_rect; intros ?? [] **.
    all: try match goal with H : PolyRedPack _ _ _ |- _ => destruct H; econstructor; tea end.
    all: now econstructor.
  Qed.

  Corollary LRTyEqRefl_ {l Γ A} (lr : [ Γ ||-< l > A ] ) : [ Γ ||-< l > A ≅ A | lr ].
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    now eapply LRTyEqRefl.
  Qed.

  Lemma NeNfEqRefl {Γ k A} : [Γ ||-NeNf k : A] -> [Γ ||-NeNf k ≅ k : A].
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma reflNatRedTmEq {Γ A} {NA : [Γ ||-Nat A]} :
      (forall t : term, [Γ ||-Nat t : A | NA] -> [Γ ||-Nat t ≅ t : A | NA])
    × (forall t : term, NatProp NA t -> NatPropEq NA t t).
  Proof.
    eapply NatRedInduction.
    1-3: now econstructor.
    intros; econstructor.
    now eapply NeNfEqRefl.
  Qed.

  Lemma reflEmptyRedTmEq {Γ A} {NA : [Γ ||-Empty A]} :
      (forall t : term, [Γ ||-Empty t : A | NA] -> [Γ ||-Empty t ≅ t : A | NA])
    × (forall t : term, @EmptyProp _ _ _ Γ t -> @EmptyPropEq _ _ Γ t t).
  Proof.
    split.
    - intros t Ht. induction Ht.
      econstructor; eauto.
      destruct prop; econstructor.
      now eapply NeNfEqRefl.
    - intros ? []. econstructor. 
      now eapply NeNfEqRefl.
  Qed.

  Definition LRTmEqRefl@{h i j k l} {l Γ A eqTy redTm eqTm} (lr : LogRel@{i j k l} l Γ A eqTy redTm eqTm) :
    forall t, redTm t -> eqTm t t.
  Proof.
    pattern l, Γ, A, eqTy, redTm, eqTm, lr; eapply LR_rect; 
      clear Γ A eqTy redTm eqTm lr; intros Γ A.
    - intros h t [? ? ? ? [[] rel]%RedTyRecFwd] ; cbn in *.
      (* Need an additional universe level h < i *)
      assert (eqTy t) by (eapply LRTyEqRefl@{h i j k}; exact rel).
      unshelve econstructor.
      all : cbn.
      1-2: econstructor ; tea ; cbn.
      1-3,5: eapply RedTyRecBwd; apply (LRbuild@{h i j k} rel).
      1: cbn; easy.
      now eapply TyEqRecBwd.
    - intros [] t [].
      econstructor ; cbn in *.
      all: eassumption.
    - intros ???? t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn.
      all: now eauto.
    - intros; now apply reflNatRedTmEq.
    - intros; now apply reflEmptyRedTmEq.
    - intros ???? t [].
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
