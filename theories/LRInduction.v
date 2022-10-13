From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping LogicalRelation.

Theorem LR_rect0
  (P : forall {c t rEq rTe rTeEq}, @LR zero rec0 c t rEq rTe rTeEq  -> Type) :
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne rec0 neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πr A ]) (HAvalid : TyPiRelValid (LR rec0) ΠA),
    (forall {Δ} (h : [ |- Δ]),
      P (HAvalid.(TyPiRel.domValid) h)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
      P (HAvalid.(TyPiRel.codValid) h1 h2)) ->
    P (LRPi rec0 ΠA HAvalid)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR rec0 c t rEq rTe rTeEq), 
   P lr.
Proof.
  intros Hne HPi.
  fix HRec 6.
  intros c t rEq rTE rTeEq lr.
  case lr.
  - destruct H as [? l_].
    inversion l_.
  - eapply Hne.
  - destruct ΠAvalid ; unfold LRPackValid in * ; cbn in *.
    eapply HPi.
    all: intros ; eapply HRec.
  - inversion l_.
Defined.

(*TODO : get a good induction principle*)
(*Scheme LR_rect := Induction for LR Sort Type.*)
Theorem LR_rect1
  (P0 : forall {c t rEq rTe rTeEq},
  @LR zero rec0 c t rEq rTe rTeEq  -> Type)
  (P1 : forall {c t rEq rTe rTeEq},
  @LR one rec1 c t rEq rTe rTeEq  -> Type) :

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P0 (LRne rec0 neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πr A ]) (HAvalid : TyPiRelValid (LR rec0) ΠA),
    (forall {Δ} (h : [ |- Δ]),
      P0 (HAvalid.(TyPiRel.domValid) h)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
      P0 (HAvalid.(TyPiRel.codValid) h1 h2)) ->
    P0 (LRPi rec0 ΠA HAvalid)) ->

  (forall (Γ : context) (h : [Γ ||-U]),
    P1 (LRU rec1 h)) ->

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P1 (LRne rec1 neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πr A ]) (HAvalid : TyPiRelValid (LR rec1) ΠA),
  (forall {Δ} (h : [ |- Δ]),
    P1 (HAvalid.(TyPiRel.domValid) h)) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : [ Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
  P1 (HAvalid.(TyPiRel.codValid) h1 h2)) ->
  P1 (LRPi rec1 ΠA HAvalid)) ->

  (forall (Γ : context) (A : term) {l' l_}
    (H : [Γ ||-< zero | A]),
    P0 H.(LRValid.valid) ->
    P1 (@LREmb _ _ _ _ l' l_ H)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR rec1 c t rEq rTe rTeEq),
    P1 lr.
Proof.
  cbn.
  intros Hne0 HPi0 HU Hne1 HPi1 Hemb.
  fix HRec 6.
  destruct lr.
  - eapply HU.
  - eapply Hne1.
  - eapply HPi1.
    all: intros ; eapply HRec.
  - inversion l_ ; subst.
    cbn in *.
    eapply Hemb.
    eapply LR_rect0.
    all: assumption.
Defined.

(* Not reproving the lemmas for the lower level, since we can prove it using LR_rect0*)
Theorem LR_rect1'
  (P0 : forall {c t rEq rTe rTeEq},
  @LR zero rec0 c t rEq rTe rTeEq  -> Type)
  (P1 : forall {c t rEq rTe rTeEq},
  @LR one rec1 c t rEq rTe rTeEq  -> Type) :

  (forall (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR rec0 c t rEq rTe rTeEq), 
   P0 lr) ->

  (forall (Γ : context) (h : [Γ ||-U]),
    P1 (LRU rec1 h)) ->

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P1 (LRne rec1 neA)) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πr A ]) (HAvalid : TyPiRelValid (LR rec1) ΠA),
  (forall {Δ} (h : [ |- Δ]),
    P1 (HAvalid.(TyPiRel.domValid) h)) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : [ Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
  P1 (HAvalid.(TyPiRel.codValid) h1 h2)) ->
  P1 (LRPi rec1 ΠA HAvalid)) ->

  (forall (Γ : context) (A : term) {l' l_}
    (H : [ Γ ||-< zero | A]),
    P0 H.(LRValid.valid) ->
    P1 (@LREmb _ _ _ _ l' l_ H)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR rec1 c t rEq rTe rTeEq),
    P1 lr.
Proof.
  cbn.
  intros H0 HU Hne1 HPi1 Hemb.
  eapply LR_rect1.
  all: try solve [eauto].
  all: intros ; eapply H0.
Defined.

(*The nice, combined induction principle we would like to have… But sadly the naïve proof fails due to universe constraints.*)

Theorem LR_rect (P : RedRel) :

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P Γ A (fun B : term => [Γ ||-ne A ≅ B | neA])
    (fun t : term => [Γ ||-ne t ::: A | neA])
    (fun t u : term => [Γ ||-ne t ≅ u ::: A | neA])) ->

  (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πr A ])
    (HAvalid : {l & TyPiRelValid (LRL l) ΠA}),
    (forall {Δ} (h : [ |- Δ]),
      P Δ (TyPiRel.dom ΠA) (LRPack.eq (TyPiRel.domRel ΠA h))
      (LRPack.term (TyPiRel.domRel ΠA h)) (LRPack.eqTerm (TyPiRel.domRel ΠA h))) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ Δ ||-p a ::: ΠA.(TyPiRel.dom) | ΠA.(TyPiRel.domRel) h1 ]),
      P Δ ((TyPiRel.cod ΠA) {0 := a}) (LRPack.eq (TyPiRel.codRel ΠA h1 h2))
      (LRPack.term (TyPiRel.codRel ΠA h1 h2))
      (LRPack.eqTerm (TyPiRel.codRel ΠA h1 h2))) ->
    P Γ A (fun B : term => [Γ ||-Π A ≅ B | ΠA])
    (fun t : term => [Γ ||-Π t ::: A | ΠA])
    (fun t u : term => [Γ ||-Π t ≅ u ::: A | ΠA])) ->

  (forall (Γ : context) (h : [Γ ||-U]),
    P Γ U (fun B : term => [Γ ||-U≅ B])
    (fun t : term => [rec1 | Γ ||-U t :::U | URel.lt h])
    (fun t u : term => [rec1 | Γ ||-U t ≅ u :::U | URel.lt h])) ->

  (forall (Γ : context) (A : term)
    (H : [kit0 | Γ ||- A]),
    P Γ A H.(LRValid.eq) H.(LRValid.term) H.(LRValid.eqTerm) ->
    P Γ A (fun B : term => LRKit.EqTyRel kit0 Γ A B H)
    (fun t : term => LRKit.TeRel kit0 Γ t A H)
    (fun t u : term => LRKit.EqTeRel kit0 Γ t u A H)) ->

  forall (l : TypeLevel) (Γ : context) (t : term) (rEq rTe : term -> Type)
    (rTeEq  : term -> term -> Type) (lr : LR (recl l) Γ t rEq rTe rTeEq),
    P Γ t rEq rTe rTeEq.
Proof.
  cbn.
  intros Hne HPi HU Hemb l.
  case l ; cbn.
  - eapply LR_rect0.
    + eauto.
    + intros.
      eapply HPi ; tea.
      now exists zero.
  - Fail eapply (LR_rect1 (fun Γ t rEq rTe rTeEq _ => P Γ t rEq rTe rTeEq) (fun Γ t rEq rTe rTeEq _ => P Γ t rEq rTe rTeEq)).
Abort.