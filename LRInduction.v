From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping LogicalRelation Context.


(*TODO : get a good induction principle*)
(*Scheme LR_rect := Induction for LR Sort Type.*)




Fixpoint LR_rec1 
  (l : TypeLevel)  
  (rec : forall l' : TypeLevel, (l') << (l) -> LogRelKit)
  (c : context) (t : term) (rEq rTe : term -> Type)
  (rTeEq  : term -> term -> Type) (lr : LR rec c t rEq rTe rTeEq ) : 
  forall 
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
  P lr.
Proof.
  intros.
  destruct lr.
  eapply X; try eassumption.
  eapply X0; try eassumption.
  2 : eapply X2; try eassumption.
  destruct H.
  eapply X1;
  intros;
  apply LR_rec1; try assumption.
Defined.

Polymorphic Definition LR_rect : forall 
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
  


