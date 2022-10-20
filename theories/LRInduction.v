From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import Notations Untyped MLTTTyping LogicalRelation.

Set Universe Polymorphism.

Theorem LR_rect0
  (rec : forall l', l' << zero -> LogRelKit)
  (P : forall {c t rEq rTe rTeEq}, LR rec c t rEq rTe rTeEq  -> Type) :
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne rec neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ]) (HAad : PiRedTyAdequate (LR rec) ΠA),
    (forall {Δ} (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) h)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
      P (HAad.(PiRedTy.codAd) h1 h2)) ->
    P (LRPi rec ΠA HAad)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR rec c t rEq rTe rTeEq), 
   P lr.
Proof.
  intros Hne HPi.
  fix HRec 6.
  intros c t rEq rTE rTeEq lr.
  case lr.
  - destruct H as [? l_].
    inversion l_.
  - eapply Hne.
  - destruct ΠAad ; unfold LRPackAdequate in * ; cbn in *.
    eapply HPi.
    all: intros ; eapply HRec.
Qed.

Theorem LR_rect0'
  (P : forall {c t rEq rTe rTeEq}, @LR zero rec0 c t rEq rTe rTeEq  -> Type) :
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne rec0 neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ]) (HAad : PiRedTyAdequate (LR rec0) ΠA),
    (forall {Δ} (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) h)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
      P (HAad.(PiRedTy.codAd) h1 h2)) ->
    P (LRPi rec0 ΠA HAad)) ->

  forall (Γ : context) (A : term) (lr : [Γ ||-< zero > A]),
  P (lr.(LRAd.adequate)).
Proof.
  intros.
  eapply LR_rect0.
  all: eassumption.
Qed.

Fixpoint LR_embedding {l l'} (l_ : l << l')
  {Γ A rEq rTe rTeEq} (lr : LRl l Γ A rEq rTe rTeEq) {struct lr} : (LRl l' Γ A rEq rTe rTeEq) :=
  match lr with
   | LRU Γ H =>
      match
        (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
      with end
   | LRne _ _ neA => LRne _ neA
   | LRPi _ _ ΠA ΠAad => LRPi _ ΠA
      {|
        PiRedTy.domAd :=
          fun (Δ : context) (h : [  |- Δ]) => LR_embedding l_ (ΠAad.(PiRedTy.domAd) h) ;
        PiRedTy.codAd :=
          fun (Δ : context) (a : term) (h : [  |- Δ])
            (ha : [PiRedTy.domRed ΠA h | _ ||- a : _]) =>
          LR_embedding l_ (ΠAad.(PiRedTy.codAd) h ha)
      |}
  end.

Theorem LR_rect1
  (rec : forall l', l' << one -> LogRelKit)
  (P : forall {c t rEq rTe rTeEq},
  @LR one rec c t rEq rTe rTeEq  -> Type) :

  (forall (Γ : context) (h : [Γ ||-U one]),
    P (LRU rec h)) ->

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne rec neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ]) (HAad : PiRedTyAdequate (LR rec) ΠA),
  (forall {Δ} (h : [ |- Δ]),
    P (HAad.(PiRedTy.domAd) h)) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
  P (HAad.(PiRedTy.codAd) h1 h2)) ->
  P (LRPi rec ΠA HAad)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR rec c t rEq rTe rTeEq),
    P lr.
Proof.
  cbn.
  intros HU Hne HPi.
  fix HRec 6.
  destruct lr.
  - eapply HU.
  - eapply Hne.
  - eapply HPi.
    all: intros ; eapply HRec.
Qed.

Theorem LR_rect (P : forall {l Γ A}, [Γ ||-< l > A] -> Type) :

  (forall (Γ : context) (h : [Γ ||-U one]),
    P (LRU_ h)) ->

  (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne_ l neA)) ->

  (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ]) (HAad : PiRedTyAdequate (LRl l) ΠA),
  (forall {Δ} (h : [ |- Δ]),
    P (LRbuild (HAad.(PiRedTy.domAd) h))) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
  P (LRbuild (HAad.(PiRedTy.codAd) h1 h2))) ->
  P (LRPi_ l ΠA HAad)) ->

  forall (l : TypeLevel) (Γ : context) (A : term) (lr : [Γ ||-< l > A]),
    P lr.
Proof.
  intros HU Hne HPi [] Γ A lr.
  - apply (LR_rect0 rec0 (fun Γ A _ _ _ lr => P zero Γ A (LRbuild lr))).
    + intros.
      apply Hne.
    + intros.
      apply HPi ; try eassumption.
  - apply (LR_rect1 rec1 (fun Γ A _ _ _ lr => P one Γ A (LRbuild lr))).
    + assumption.
    + intros.
      apply Hne.
    + intros.
      apply HPi.
      all: eassumption.
Qed.

Theorem LR_rec (P : RedRel) :
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
  P Γ A (fun B : term => [Γ ||-ne A ≅ B | neA])
  (fun t : term => [Γ ||-ne t : A | neA])
  (fun t u : term => [Γ ||-ne t ≅ u : A | neA])) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ])
  (HAad : {l & PiRedTyAdequate (LRl l) ΠA}),
  (forall {Δ} (h : [ |- Δ]),
    P Δ (PiRedTy.dom ΠA) (LRPack.eqTy (PiRedTy.domRed ΠA h))
    (LRPack.redTm (PiRedTy.domRed ΠA h)) (LRPack.eqTm (PiRedTy.domRed ΠA h))) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
    P Δ ((PiRedTy.cod ΠA) {0 := a}) (LRPack.eqTy (PiRedTy.codRed ΠA h1 h2))
    (LRPack.redTm (PiRedTy.codRed ΠA h1 h2))
    (LRPack.eqTm (PiRedTy.codRed ΠA h1 h2))) ->
  P Γ A (fun B : term => [Γ ||-Π A ≅ B | ΠA])
  (fun t : term => [Γ ||-Π t : A | ΠA])
  (fun t u : term => [Γ ||-Π t ≅ u : A | ΠA])) ->

  (forall (Γ : context) (h : [Γ ||-U one ]),
  P Γ U (fun B : term => [Γ ||-U≅ B])
  (fun t : term => [rec1 | Γ ||-U t :U | h])
  (fun t u : term => [rec1 | Γ ||-U t ≅ u :U | h])) ->

  forall (l : TypeLevel) (Γ : context) (t : term) (rEq rTe : term -> Type)
  (rTeEq  : term -> term -> Type) (lr : LR (LogRelRec l) Γ t rEq rTe rTeEq),
  P Γ t rEq rTe rTeEq.
Proof.
  intros Hne HPi HU [].
  - apply LR_rect0.
    + assumption.
    + intros.
      apply HPi ; try eassumption.
      exists zero.
      eassumption.
  - apply LR_rect1.
    + assumption.
    + assumption.
    + intros.
      apply HPi ; try eassumption.
      exists one.
      eassumption.
Qed.

Theorem LR_rec' (P : context -> term -> Type) :
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
  P Γ A) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ])
    (HAad : {l & PiRedTyAdequate (LRl l) ΠA}),
    (forall {Δ} (h : [ |- Δ]),
      P Δ (PiRedTy.dom ΠA)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
      P Δ ((PiRedTy.cod ΠA) {0 := a})) ->
    P Γ A) ->

  (forall (Γ : context) (h : [Γ ||-U one ]),
    P Γ U) ->

  forall (l : TypeLevel) (Γ : context) (A : term),
    [Γ ||-< l > A] -> P Γ A.
Proof.
  intros Hne HPi HU l Γ A [[] lr].
  red in lr ; cbn in lr.
  eapply (LR_rec (fun Γ A _ _ _ => P Γ A)).
  all: eassumption.
Qed.