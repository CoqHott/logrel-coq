From MetaCoq Require Import PCUICAst.
Require Import Notations Automation MLTTTyping LogicalRelation Properties Reduction LRInduction Escape.

Set Universe Polymorphism.

(* Definition reflNe {Γ} {A} (neA : [Γ ||-ne A]) : [Γ ||-ne A ≅ A | neA].
Proof.
  destruct neA.
  now econstructor.
Qed.

Definition reflPi l {Γ} {A} (ΠA : [Γ ||-Πr A]) (ΠAvalid : TyPiRelValid (LR (LogRelRec l)) ΠA) :
(forall Δ (h : [  |- Δ]), (ΠA.(TyPiRel.domRel) h).(LRPack.eq) ΠA.(TyPiRel.dom)) ->
(forall Δ a (h1 : [  |- Δ])
  (h2 : [Δ ||-p a : ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
  (ΠA.(TyPiRel.codRel) h1 h2).(LRPack.eq) (ΠA.(TyPiRel.cod){0 := a})) ->
[Γ ||-Π A ≅ A | ΠA].
Proof.
  destruct ΠA.
  econstructor.
  all: mltt.
Qed. *)

Definition reflEq {l Γ A} (lr : [ Γ ||-< l > A ] ) : [ Γ ||-< l > A ≅ A | lr ].
Proof.
  eapply (LR_rect (fun l Γ A lr => [Γ ||-< l > A ≅ A | lr])).
  + intros ? [].
    econstructor.
    reflexivity.
  + intros ? ? ? [].
    now econstructor.
  + intros ? ? ? [] ; cbn in *.
    econstructor.
    all: mltt.
Qed.

(* Definition reflTermNe {Γ A t} : forall (neA : [Γ ||-ne A]), 
  [Γ ||-ne t : A | neA] -> [Γ ||-ne t ≅ t : A | neA].
Proof.
  intros [] [? ? []] ; cbn in *.
  econstructor.
  1-2: now mltt.
  econstructor.
  all: mltt.
Qed.

Definition reflTermPi {Γ A} l (ΠA : [Γ ||-Πr A]) (ΠAvalid : TyPiRelValid (LR (LogRelRec l)) ΠA):
(forall Δ (h : [  |- Δ]) t,
  (ΠA.(TyPiRel.domRel) h).(LRPack.term) t ->
  (ΠA.(TyPiRel.domRel) h).(LRPack.eqTerm) t t) ->

(forall Δ a (h1 : [  |- Δ])
   (h2 : [Δ ||-p a : ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]) t,
   (ΠA.(TyPiRel.codRel) h1 h2).(LRPack.term) t ->
   (ΠA.(TyPiRel.codRel) h1 h2).(LRPack.eqTerm) t t) ->

forall t,
  [Γ ||-Π t : A | ΠA] -> [Γ ||-Π t ≅ t : A | ΠA].
Proof.
  intros ? ? ? [].
  econstructor.
  all: mltt.
  econstructor.
  all: mltt.
Qed. *)

Definition reflEqTerm {l Γ A t} (lr : [ Γ ||-< l > A ] ) : 
    [ Γ ||-< l > t : A | lr ] ->
    [ Γ ||-< l > t ≅ t : A | lr ].
Proof.
  eapply (LR_rect (fun l Γ A lr => forall t, [Γ ||-< l > t : A | lr] -> [Γ ||-< l > t ≅ t : A | lr])).
  - intros Γ' [] t' [].
    assert [Γ' ||-< zero > t' ≅ t' | rel ] by apply reflEq.
    unshelve econstructor.
    1-2: now econstructor.
    all: try eassumption.
    mltt.
  - intros ? ? ? [] ? Hne.
    inversion Hne.
    econstructor ; tea.
    cbn in *.
    econstructor.
    mltt.
  - intros ? ? ? [] [] ? ? ? [] ; cbn in *.
    unfold PiRedTy.redPi in * ; cbn in *.
    unshelve econstructor ; cbn in *.
    1-2: econstructor ; tea.
    all: auto.
Qed.