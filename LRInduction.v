From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping LogicalRelation.

Fixpoint LR_rec0
  (c : context) (t : term) (rEq rTe : term -> Type)
  (rTeEq  : term -> term -> Type) (lr : LR rec0 c t rEq rTe rTeEq ) : 
  forall 
  (P0 : forall {c t rEq rTe rTeEq} ,
   @LR zero rec0 c t rEq rTe rTeEq  -> Type),
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P0 (LRne rec0 neA))
  ->
  (forall (Γ : context) (A : term) (H0 : [ Γ ||-0Π A ]) (H1 : TyPiRel1 (LR rec0) H0),
    (forall {Δ} (h : [ |- Δ]),
      P0(H1.(_F1) h)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : @Rel1Te _ rec0 Δ a (F H0) (_F H0 h1; H1.(_F1) h1)),
      P0 (_G1 H1 h1 h2)) ->
    P0 (LRPi rec0 H0 H1)) 
  ->
   P0 lr.
Proof.   
   intros.
   destruct lr.
   1,4 : inversion l_.
   eapply X; try eassumption.
   eapply X0; try eassumption;
   destruct H1; destruct H0;
   intros;
   apply LR_rec0; try assumption.
Defined.

Check LR_rec0.

(*TODO : get a good induction principle*)
(*Scheme LR_rect := Induction for LR Sort Type.*)
Fixpoint LR_rec1 
  (c : context) (t : term) (rEq rTe : term -> Type)
  (rTeEq  : term -> term -> Type) (lr : LR rec1 c t rEq rTe rTeEq ) : 
  forall 
  (P0 : forall {c t rEq rTe rTeEq} ,
   @LR zero rec0 c t rEq rTe rTeEq  -> Type)
  (P1 : forall {c t rEq rTe rTeEq} ,
   @LR one rec1 c t rEq rTe rTeEq  -> Type),
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P0 (LRne rec0 neA)) 
  ->
  (forall (Γ : context) (A : term) (H0 : [ Γ ||-0Π A ]) (H1 : TyPiRel1 (LR rec0) H0),
    (forall {Δ} (h : [ |- Δ]),
      P0 (H1.(_F1) h)) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : @Rel1Te _ rec0 Δ a (F H0) (_F H0 h1; H1.(_F1) h1)),
      P0 (_G1 H1 h1 h2)) ->
    P0 (LRPi rec0 H0 H1)) 
  ->


  (forall (Γ : context) (h : [  |- Γ]) {l' l_},
    P1 (LRU rec1 h l' l_)) 
  ->
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P1 (LRne rec1 neA)) 
  ->
  (forall (Γ : context) (A : term) (H0 : [ Γ ||-0Π A ]) (H1 : TyPiRel1 (LR rec1) H0),
  (forall {Δ} (h : [ |- Δ]),
    P1 (H1.(_F1) h)) ->
  (forall {Δ a} (h1 : [ |- Δ ]) 
    (h2 : @Rel1Te _ rec1 Δ a (F H0) (_F H0 h1; H1.(_F1) h1)),
    P1 (_G1 H1 h1 h2)) ->
  P1 (LRPi rec1 H0 H1)) 
  ->


  (forall (Γ : context) (A : term) {l' l_}
    (H : [kit0 | Γ ||- A]),
    
    P0 (projT2 H) ->
    P1 (@LRemb _ _ _ _ l' l_ H)) ->

    P1 lr.
Proof.
  intros.
  destruct lr.
  eapply X1; try eassumption.
  eapply X2; try eassumption.
  destruct H1;destruct H0.
  eapply X3;
  intros;
  eapply LR_rec1; try eassumption.
  eapply X4.
  destruct H.
  inversion l.
  1, 4 : inversion l_0.
  all : eapply LR_rec0; assumption.
Defined.


(*Definition LR_rect : forall 
  (l : TypeLevel)
  (rec : forall l' : TypeLevel, (l') << (l) -> LogRelKit)
  (P : forall {c : context} {t : term} {rEq rTe : term -> Type}
          {rTeEq  : term -> term -> Type}, LR rec c t rEq rTe rTeEq  -> Type),

  (forall (Γ : context) (h : [  |- Γ]) (l' : TypeLevel)
    (l_ : (l') << (l)),
    P (LRU rec h l' l_)) ->

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne rec neA)) ->

  (forall (Γ : context) (A : term) (H : [Γ ||-1Π A | LR rec]),
    (forall {Δ} (h : [ |- Δ]),
      P (relLR (_F H h))) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ Δ  ||-0 a ::: (F H) | _F H h1 ]),
      P (relLR (_G H h1 h2))) ->
    P (LRPi rec H)) ->

  (forall (Γ : context) (A : term) (l' : TypeLevel) 
    (l_ : (l') << (l)) (H : [rec l' l_ | Γ ||- A]),
    P (LRemb rec l_ H)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
   (rTeEq  : term -> term -> Type) (lr : LR rec c t rEq rTe rTeEq ),

  P lr.
Proof.
  intros.
  apply LR_rec1; assumption.
Defined.

Polymorphic Definition LR_ind : forall 
  (l : TypeLevel)
  (rec : forall l' : TypeLevel, (l') << (l) -> LogRelKit)
  (P : forall {c : context} {t : term} {rEq rTe : term -> Type}
          {rTeEq  : term -> term -> Type}, LR rec c t rEq rTe rTeEq  -> Prop),

  (forall (Γ : context) (h : [  |- Γ]) (l' : TypeLevel)
    (l_ : (l') << (l)),
    P (LRU rec h l' l_)) ->

  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (LRne rec neA)) ->

  (forall (Γ : context) (A : term) (H : [Γ ||-1Π A | LR rec]),
    (forall {Δ} (h : [ |- Δ]),
      P (relLR (_F H h))) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ Δ  ||-0 a ::: (F H) | _F H h1 ]),
      P (relLR (_G H h1 h2))) ->
    P (LRPi rec H)) ->

  (forall (Γ : context) (A : term) (l' : TypeLevel) 
    (l_ : (l') << (l)) (H : [rec l' l_ | Γ ||- A]),
    P (LRemb rec l_ H)) ->

  forall (c : context) (t : term) (rEq rTe : term -> Type)
   (rTeEq  : term -> term -> Type) (lr : LR rec c t rEq rTe rTeEq ),

  P lr := LR_rect.
*)