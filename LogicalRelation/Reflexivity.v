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

Definition reflEqTerm0 {Γ} {A t} (H : [ Γ ||-< zero | A ] ) : 
    [ Γ ||-< zero | t ::: A | H ] ->
    [ Γ ||-< zero | t ≅ t ::: A | H ].
   
Proof.
    destruct H.
    destruct pack.
    eapply (LR_rec0 Γ A relEq relTerm relEqTerm valid).
    + intros. cbn in *.
      destruct X.
      econstructor.
      destruct neA.
      try econstructor; try gen_conv.
    + destruct neA;
      destruct X; cbn in *.
      eapply neTeEq.
      * gen_conv.
        destruct d.
        gen_conv. eassumption. 
      * gen_conv. eassumption.
      * destruct nf.
        constructor; try assumption.
        apply TermRefl.
        eapply wfTermConv.
        eassumption.
        destruct D.      
        exact (TypeSym (RedConvTyC D)).
    + destruct X.
      econstructor;
      try eassumption.
      econstructor; try eassumption.      
      intros.
      eapply appEq.
      assumption.
      exact (reflEqTerm _ _ _ _ _ ha).
    + exact todo. 
      (*exact (reflEqTerm _ _ _ _ _ X).*)
    Unshelve. assumption.
Defined.
  

      
      

      


    

    
    
    

