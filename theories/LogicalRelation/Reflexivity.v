(** * LogRel.LogicalRelation.Reflexivity: reflexivity of the logical relation. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape.

Set Universe Polymorphism.
Set Printing Universes.

Section Reflexivities.
  Context `{GenericTypingProperties}.

  Definition reflLRTyEq {l Γ A} (lr : [ Γ ||-< l > A ] ) : [ Γ ||-< l > A ≅ A | lr ].
  Proof.
    pattern l, Γ, A, lr; eapply LR_rect_TyUr; intros ??? [] **.
    all: try match goal with H : PolyRed _ _ _ _ |- _ => destruct H; econstructor; tea end.
    all: try now econstructor.
    (* econstructor; tea; now eapply escapeEqTerm. *)
  Qed.


  (* Deprecated *)
  Corollary LRTyEqRefl {l Γ A eqTy redTm eqTm}
    (lr : LogRel l Γ A eqTy redTm eqTm) : eqTy A.
  Proof.
    pose (R := Build_LRPack Γ A eqTy redTm eqTm). 
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    change [Rad | _ ||- _ ≅ A ]; now eapply reflLRTyEq.
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

  Lemma reflIdPropEq {Γ l A} (IA : [Γ ||-Id<l> A]) t (Pt : IdProp IA t) : IdPropEq IA t t.
  Proof.
    destruct Pt; constructor; tea; now eapply NeNfEqRefl.
  Qed.

  Lemma reflIdRedTmEq {Γ l A} (IA : [Γ ||-Id<l> A]) t (Rt : [Γ ||-Id<l> t : _ | IA]) : [Γ ||-Id<l> t ≅ t : _ | IA].
  Proof. destruct Rt; econstructor; tea; now eapply reflIdPropEq. Qed.

  Definition reflLRTmEq@{h i j k l} {l Γ A} (lr : [ LogRel@{i j k l} l | Γ ||- A ] ) :
    forall t,
      [ Γ ||-<l> t : A | lr ] ->
      [ Γ ||-<l> t ≅ t : A | lr ].
  Proof.
    pattern l, Γ, A, lr; eapply LR_rect_TyUr; clear l Γ A lr; intros l Γ A.
    - intros h t [? ? ? ? Rt%RedTyRecFwd@{j k h i k}] ; cbn in *.
      (* Need an additional universe level h < i *)
      Unset Printing Notations.
      pose proof (reflLRTyEq@{h i k j} Rt).
      unshelve econstructor.
      all : cbn.
      1-2: econstructor ; tea ; cbn.
      1-3,5: eapply RedTyRecBwd; tea.
      1: cbn; easy.
      now eapply TyEqRecBwd.
    - intros [] t [].
      econstructor ; cbn in *.
      all: eassumption.
    - intros ??? t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn; now eauto.
    - intros; now apply reflNatRedTmEq.
    - intros; now apply reflEmptyRedTmEq.
    - intros ??? t [].
      unshelve econstructor ; cbn in *.
      1-2: now econstructor.
      all: cbn; now eauto.
    - intros; now eapply reflIdRedTmEq.
  Qed.
  
  (* Deprecated *)
  Corollary LRTmEqRefl@{h i j k l} {l Γ A eqTy redTm eqTm} (lr : LogRel@{i j k l} l Γ A eqTy redTm eqTm) :
    forall t, redTm t -> eqTm t t.
  Proof.
    pose (R := Build_LRPack Γ A eqTy redTm eqTm). 
    pose (Rad := Build_LRAdequate (pack:=R) lr).
    intros t ?; change [Rad | _ ||- t ≅ t : _ ]; now eapply reflLRTmEq.
  Qed.

End Reflexivities.
