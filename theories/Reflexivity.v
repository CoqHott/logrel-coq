From MetaCoq Require Import PCUICAst.
Require Import MLTTTyping LogicalRelation Properties Reduction LRInduction.

Set Universe Polymorphism.

Definition reflNe {Γ} {A} (neA : [Γ ||-ne A]) : [Γ ||-ne A ≅ A | neA].
Proof.
  destruct neA; now econstructor.
Defined.

Definition reflPi l {Γ} {A} (ΠA : [Γ ||-Πr A]) (ΠAvalid : TyPiRelValid (LR (recl l)) ΠA) :
(forall Δ (h : [  |- Δ]), (ΠA.(TyPiRel.domRel) h).(LRPack.eq) ΠA.(TyPiRel.dom)) ->
(forall Δ a (h1 : [  |- Δ])
  (h2 : [Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
  (ΠA.(TyPiRel.codRel) h1 h2).(LRPack.eq) (ΠA.(TyPiRel.cod){0 := a})) ->
[Γ ||-Π A ≅ A | ΠA].
Proof.
  destruct ΠA.
  econstructor.
  all: mltt.
Defined.

Definition reflEq0 {Γ} {A} (lr : [ Γ ||-< zero | A ] ) : [ Γ ||-< zero |  A ≅ A | lr ].
Proof.
  eapply (LR_rect0 (fun Γ A _ _ _ H => [Γ ||-< zero | A ≅ A | Build_LRValid H])).
  + intros. now apply reflNe.
  + intros. now eapply (reflPi zero).
Defined.

Definition reflEq1 {Γ} {A} (H : [ Γ ||-< one | A ] ) : [ Γ ||-< one |  A ≅ A | H].
Proof.
  eapply (LR_rect1' (fun Γ A _ _ _ H => [Γ ||-< zero | A ≅ A | Build_LRValid H])
    (fun Γ A _ _ _ H => [Γ ||-< one | A ≅ A | Build_LRValid H])).
  - intros ; eapply reflEq0.
  - now constructor.
  - intros ; eapply reflNe.
  - intros ; now eapply (reflPi one).
  - eauto.
Defined.

Definition reflTermNe {Γ0 A0 t} : forall (neA : [Γ0 ||-ne A0]), 
  [Γ0 ||-ne t ::: A0 | neA] -> [Γ0 ||-ne t ≅ t ::: A0 | neA].
Proof.
  intros [] [? ? []] ; cbn in *.
  econstructor.
  1-2: now mltt.
  econstructor.
  all: mltt.
Defined.

Definition reflTermPi {Γ A} l (ΠA : [Γ ||-Πr A]) (ΠAvalid : TyPiRelValid (LR (recl l)) ΠA):
(forall Δ (h : [  |- Δ]) t,
  (ΠA.(TyPiRel.domRel) h).(LRPack.term) t ->
  (ΠA.(TyPiRel.domRel) h).(LRPack.eqTerm) t t) ->

(forall Δ a (h1 : [  |- Δ])
   (h2 : [Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]) t,
   (ΠA.(TyPiRel.codRel) h1 h2).(LRPack.term) t ->
   (ΠA.(TyPiRel.codRel) h1 h2).(LRPack.eqTerm) t t) ->

forall t,
  [Γ ||-Π t ::: A | ΠA] -> [Γ ||-Π t ≅ t ::: A | ΠA].
Proof.
  intros ? ? ? [].
  econstructor.
  all: mltt.
  econstructor.
  all: mltt.
Defined.

Definition reflEqTerm0 {Γ} {A t} (H : [ Γ ||-< zero | A ] ) : 
    [ Γ ||-< zero | t ::: A | H ] ->
    [ Γ ||-< zero | t ≅ t ::: A | H ].
Proof.
  eapply (LR_rect0 (fun Γ A _ _ _ H => forall t, [ Γ ||-< zero | t ::: A | Build_LRValid H] ->
    [Γ ||-< zero | t ≅ t ::: A | Build_LRValid H])).
  - intros. now eapply reflTermNe.
  - intros. now eapply (reflTermPi zero).
Defined.

Definition reflEqTerm1 {Γ} {A t} (H : [ Γ ||-< one | A ] ) : 
    [ Γ ||-< one | t ::: A | H ] ->
    [ Γ ||-< one | t ≅ t ::: A | H ].
Proof.
  eapply (LR_rect1'
  (fun Γ A _ _ _ H => forall t,
    [Γ ||-< zero | t ::: A | Build_LRValid H] ->
    [Γ ||-< zero | t ≅ t ::: A | Build_LRValid H])
  (fun Γ A _ _ _ H => forall t,
    [Γ ||-< one | t ::: A | Build_LRValid H] ->
    [Γ ||-< one | t ≅ t ::: A | Build_LRValid H])).
  - intros. now eapply reflEqTerm0.
  - cbn.
    intros ? ? ? [].
    unshelve econstructor ; auto.
    1: mltt.
    cbn.
    now eapply reflEq0.
  - intros. now apply reflTermNe.
  - intros. now apply (reflTermPi one).
  - auto.
Defined.

  

      
      

      


    

    
    
    

