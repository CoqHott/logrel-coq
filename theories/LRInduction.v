From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import Notations Untyped MLTTTyping LogicalRelation.

#[universes(polymorphic)]Fixpoint LR_embedding {l l'} (l_ : l << l')
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

#[universes(polymorphic)]Theorem LR_rect
  (l : TypeLevel)
  (rec : forall l', l' << l -> LogRelKit)
  (P : forall {c t rEq rTe rTeEq},
    LR rec c t rEq rTe rTeEq  -> Type) :

  (forall (Γ : context) (h : [Γ ||-U l]),
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

Theorem LR_rect_LogRelRec
  (P : forall {l Γ t rEq rTe rTeEq},
  LRl l Γ t rEq rTe rTeEq  -> Type) :

  (forall (Γ : context) (h : [Γ ||-U one]),
    P (LRU (rec1) h)) ->

  (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne (LogRelRec l) neA)) ->

  (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ])
    (HAad : PiRedTyAdequate (LRl l) ΠA),
  (forall {Δ} (h : [ |- Δ]),
    P (HAad.(PiRedTy.domAd) h)) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : [ ΠA.(PiRedTy.domRed) h1 | Δ ||- a : ΠA.(PiRedTy.dom) ]),
  P (HAad.(PiRedTy.codAd) h1 h2)) ->
  P (LRPi (LogRelRec l) ΠA HAad)) ->

  forall (l : TypeLevel) (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR (LogRelRec l) c t rEq rTe rTeEq),
    P lr.
Proof.
  intros.
  apply LR_rect.
  - intros.
    destruct l.
    2: auto.
    destruct h as [? lt].
    inversion lt.
  - auto.
  - auto.
Qed.

Theorem LR_rect_TyUr
  (P : forall {l Γ A}, [Γ ||-< l > A] -> Type) :

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
  intros HU Hne HPi l Γ A lr.
  apply (LR_rect_LogRelRec (fun l Γ A _ _ _ lr => P l Γ A (LRbuild lr))).
  all: auto.
Qed.