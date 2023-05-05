(** * LogRel.LogicalRelation.Reflexivity: reflexivity of the logical relation. *)
Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst LContexts Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.

Section Reflexivities.
  Context `{GenericTypingProperties}.

  Definition LRTyEqRefl {l wl Γ A eqTy redTm eqTm}
    (lr : LogRel l wl Γ A eqTy redTm eqTm) : eqTy A.
  Proof.
    induction lr as [ ? ? ? [] | ? ? ? [] | ? ? ? [] ? IHdom IHcod | ??? [] | ??? [] | ??? []].
    all: try now unshelve econstructor.
    cbn in *.
    unshelve econstructor ; [exact dom | exact cod | .. ] ; try assumption ; cbn in *.
    - intros.
      now eapply (codomN Δ a l' ρ τ Ninfl h).
    - intros ; eapply IHdom.
    - intros ; now eapply IHcod.
  Qed.

  Corollary LRTyEqRefl_ {l wl Γ A} (lr : [ Γ ||-< l > A ]< wl > ) : [ Γ ||-< l > A ≅ A | lr ]< wl >.
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    now eapply LRTyEqRefl.
  Qed.

  Corollary WLRTyEqRefl_ {l wl Γ A} (lr : W[ Γ ||-< l > A ]< wl > ) : W[ Γ ||-< l > A ≅ A | lr ]< wl >.
  Proof.
    destruct lr.
    exists WN.
    intros.
    eapply LRTyEqRefl_.
  Qed.
  
  Lemma NeNfEqRefl {wl Γ k A} : [Γ ||-NeNf k : A]< wl > -> [Γ ||-NeNf k ≅ k : A]< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma reflNatRedTmEq {wl Γ A} {NA : [Γ ||-Nat A]< wl >} :
    (forall t : term, [Γ ||-Nat t : A | NA]< wl > ->
                      [Γ ||-Nat t ≅ t : A | NA]< wl >)
    × (forall t : term, NatProp NA t -> NatPropEq NA t t).
  Proof.
    eapply NatRedInduction.
    1-3: now econstructor.
    intros; econstructor.
    now eapply NeNfEqRefl.
  Qed.
  
  Lemma reflBoolRedTmEq {wl Γ A} {NA : [Γ ||-Bool A]< wl >} :
    (forall t : term, [Γ ||-Bool t : A | NA]< wl > ->
                      [Γ ||-Bool t ≅ t : A | NA]< wl >)
    × (forall t : term, BoolProp NA t -> BoolPropEq NA t t).
  Proof.
    split.
    - intros t Ht ; induction Ht.
      econstructor ; eauto.
      destruct prop; econstructor.
      now eapply NeNfEqRefl.
    - intros ? [] ;  econstructor. 
      now eapply NeNfEqRefl.
  Qed.

  Lemma reflEmptyRedTmEq {wl Γ A} {NA : [Γ ||-Empty A]< wl >} :
      (forall t : term, [Γ ||-Empty t : A | NA]< wl > -> [Γ ||-Empty t ≅ t : A | NA]< wl >)
    × (forall t : term, @EmptyProp _ _ _ _ wl Γ t -> @EmptyPropEq _ _ _ wl Γ t t).
  Proof.
    split.
    - intros t Ht. induction Ht.
      econstructor; eauto.
      destruct prop; econstructor.
      now eapply NeNfEqRefl.
    - intros ? []. econstructor. 
      now eapply NeNfEqRefl.
  Qed.

  Definition LRTmEqRefl@{h i j k l} {l wl Γ A eqTy redTm eqTm} (lr : LogRel@{i j k l} l wl Γ A eqTy redTm eqTm) :
    forall t, redTm t -> eqTm t t.
  Proof.
    induction lr as [ ? ? ? h | ? ? ? [] | ? ? ? [] IHdom IHcod| ??? NA | ??? NA | ??? NA].
    - intros t [? ? ? ? ? [[] rel]%RedTyRecFwd] ; cbn in *.
      (* Need an additional universe level h < i *)
      assert (eqTy t) by (eapply LRTyEqRefl@{h i j k}; exact rel).
      unshelve econstructor.
      all : cbn.
      1-2: econstructor ; tea ; cbn.
      1-3,5: eapply RedTyRecBwd; apply (LRbuild@{h i j k} rel).
      1: cbn; easy.
      now eapply TyEqRecBwd.
    - intros t [].
      econstructor ; cbn in *.
      all: eassumption.
    - intros t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn.
      all: now eauto.
    - apply reflNatRedTmEq.
    - apply reflBoolRedTmEq.
    - apply reflEmptyRedTmEq. 
  Qed.

  Definition LREqTermRefl_ {l wl Γ A t} (lr : [ Γ ||-< l > A ]< wl > ) : 
      [ Γ ||-< l > t : A | lr ]< wl > ->
      [ Γ ||-< l > t ≅ t : A | lr ]< wl >.
  Proof.
    destruct lr as [[] lr].
    cbn in *.
    now eapply LRTmEqRefl.
  Qed.

  Corollary WLREqTermRefl_ {l wl Γ A t} (lr : W[ Γ ||-< l > A ]< wl > ) : 
      W[ Γ ||-< l > t : A | lr ]< wl > ->
      W[ Γ ||-< l > t ≅ t : A | lr ]< wl >.
  Proof.
    intros [].
    destruct lr.
    exists WNTm.
    intros.
    eapply LREqTermRefl_.
    now eapply WRedTm.
  Qed.    

End Reflexivities.
