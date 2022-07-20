Require Import MLTTTyping LogicalRelation Reduction LRInduction.

Set Universe Polymorphism.

Definition reflNe {Γ} {A} (neA : [Γ ||-ne A]) : [Γ ||-ne A ≅ A | neA].
Proof. 
  destruct neA; now econstructor.
Defined.

Definition reflPi l {Γ} {A} 
(H0 : [Γ ||-0Π A]) (H1 : TyPiRel1 (LR (recl l)) H0) :
(forall Δ (h : [  |- Δ]), relEq (_F H0 h) (F H0)) ->
(forall Δ a (h1 : [  |- Δ])
 (h2 : [Δ ||-1 a ::: F H0 | {| pack := _F H0 h1; valid := _F1 H1 h1 |}]),
relEq (_G H0 h1 h2) (PCUICAst.subst1 a 0 (G H0))) -> 
[Γ ||-1Π A ≅ A | H0].
  destruct H0; econstructor; eauto.
  intros. apply TypePiCong; try eapply TypeRefl; eauto.
Defined.

Definition reflEq0 {Γ} {A} (H : [ Γ ||-< zero | A ] ) : [ Γ ||-< zero |  A ≅ A | H].
  destruct H as [[] ?]. 
  revert Γ A relEq relTerm relEqTerm valid.
  eapply LR_rect0; cbn; intros ; 
  [apply reflNe | eapply (reflPi zero); eauto].
Defined.

Definition reflEq1 {Γ} {A} (H : [ Γ ||-< one | A ] ) : [ Γ ||-< one |  A ≅ A | H].
  destruct H as [[] ?]. 
  revert Γ A relEq relTerm relEqTerm valid.
  eapply (LR_rect1 
  (fun Γ A T T0 T1 H => 
    [Γ ||-< zero | A ≅ A | LRValidMk (@LRPackMk Γ A T T0 T1) H]));
  intros.
  1, 4 : apply reflNe.
  1 : eapply (reflPi zero); eauto.
  2 : eapply (reflPi one); eauto.
  -  now econstructor.
  - eauto.
Defined.

Definition reflTermNe {Γ0 A0 t} : forall (neA : [Γ0 ||-ne A0])  ,
  [Γ0 ||-ne t ::: A0 | neA] -> [Γ0 ||-ne t ≅ t ::: A0 | neA].
Proof.
  intros.
  destruct neA.
  destruct X.
  gen_conv.
  pose proof (TypeSym X).
  econstructor; try eassumption.
  destruct nf.
  econstructor; try eassumption.
  constructor.
  exact (wfTermConv tkTy X2).
Defined.

Definition reflTermPi {Γ0 A0} l (H0 : [Γ0 ||-0Π A0]) (H1 : TyPiRel1 (LR (recl l)) H0):
(forall Δ (h : [  |- Δ]) t,
 relTerm (_F H0 h) t ->
 relEqTerm (_F H0 h) t t) ->
(forall Δ a (h1 : [  |- Δ])
   (h2 : [Δ ||-1 a ::: F H0 | {| pack := _F H0 h1; valid := _F1 H1 h1 |}]) t,
 relTerm (_G H0 h1 h2) t ->
 relEqTerm (_G H0 h1 h2) t t) ->
  forall t,
  [Γ0 ||-1Π t ::: A0 | H0] -> [Γ0 ||-1Π t ≅ t ::: A0 | H0].
Proof.
  intros.
  destruct X1.
  econstructor; try eassumption.
  econstructor; try eassumption.
  intros. eapply appEq; try eassumption.
  eapply X; try eassumption.
Defined.

Definition reflEqTerm0 {Γ} {A t} (H : [ Γ ||-< zero | A ] ) : 
    [ Γ ||-< zero | t ::: A | H ] ->
    [ Γ ||-< zero | t ≅ t ::: A | H ].
   
Proof.
    destruct H.
    destruct pack.
    revert t.
    eapply (LR_rec0 Γ A relEq relTerm relEqTerm valid).
    + intros. now eapply reflTermNe.
    + intros. now eapply (reflTermPi zero).
    Unshelve. assumption.
Defined.




Definition reflEqTerm1 {Γ} {A t} (H : [ Γ ||-< one | A ] ) : 
    [ Γ ||-< one | t ::: A | H ] ->
    [ Γ ||-< one | t ≅ t ::: A | H ].
   
Proof.
    destruct H.
    destruct pack.
    revert t.
    eapply (LR_rec1 Γ A relEq relTerm relEqTerm valid
    (fun Γ A T T0 T1 H => forall t,
      [Γ ||-< zero | t ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] ->
      [Γ ||-< zero | t ≅ t ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H])).
    1, 4 : intros; now eapply reflTermNe.
    1 : intros; now eapply (reflTermPi zero).
    2 : intros; now eapply (reflTermPi one).
    + cbn. intros. 
      destruct X.
      econstructor; try eassumption.
      destruct dd. constructor. assumption.
      assert [rec1 l' l_ | Γ0 ||- t ≅ t | tyrel].
      eapply reflEq0.
      exact X.
    + cbn in *.
      intros.
      eapply X; try eassumption.
    Unshelve.
    all : assumption.
Defined.

  

      
      

      


    

    
    
    

