From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.
Require Import MLTTTyping LogicalRelation Context.

(*TODO : get a good induction principle*)
(*Scheme LR_rect := Induction for LR Sort Type.*)

Definition TyRelToLR {l l' l_ Γ A} : 
  [LogRelRec l l' l_ | Γ ||- A] -> [Γ ||-< l | A].
  intro.
  unfold TyUr.
  destruct l.
  inversion l_.
  unfold LogRelRec in X.
  cbn in *.
  destruct X.
  eapply (@LRPackMk Γ A _ relEq relTerm relEqTerm).
  inversion relLR;
  subst.
  inversion l_0.
  econstructor.
  assert ([Γ ||-1Π A | LR (LogRelRec one)]).
  destruct H.
  econstructor; try eassumption.
  eapply G_ext.
  eapply (@LRPi one (LogRelRec one) Γ A).
  inversion l_0.
Admitted.

Check recl one zero Oi.

Definition test {Γ A}: [recl one zero Oi | Γ ||- A] -> True.
  intro H.
  cbn in H.
  unfold Rel1Ty in H.
  destruct H.
Admitted.

Print LR.
Fixpoint LR_rec1 
  (l : TypeLevel)  
  (c : context) (t : term) (rEq rTe : term -> Type)
  (rTeEq  : term -> term -> Type) (lr : LR (recl l) c t rEq rTe rTeEq ) : 
  forall 
  (P : forall {l} (rec' : _) {c t rEq rTe rTeEq} ,
   @LR l rec' c t rEq rTe rTeEq  -> Type),
  (forall (Γ : context) (h : [  |- Γ]) (l' : TypeLevel)
    (l_ : (l') << (l)),
    P (recl l) (LRU (recl l) h l' l_)) 
  ->
  (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
    P (recl l) (LRne (recl l) neA)) 
  ->
  (forall (Γ : context) (A : term) (H : [Γ ||-1Π A | LR (recl l)]),
    (forall {Δ} (h : [ |- Δ]),
      P (recl l) (relLR (_F H h))) ->
    (forall {Δ a} (h1 : [ |- Δ ]) 
      (h2 : [ Δ  ||-0 a ::: (F H) | _F H h1 ]),
      P (recl l) (relLR (_G H h1 h2))) ->
    P (recl l) (LRPi (recl l) H)) 
  ->
  (forall (Γ : context) (A : term) (heq : l = one)
    (H : [(recl one) zero Oi | Γ ||- A]),
    
    P _ H.(relLR) ->
    P _ (LRemb _ Oi H)) ->

  P _ lr.
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
  


