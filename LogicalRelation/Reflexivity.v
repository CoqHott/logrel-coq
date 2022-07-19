Require Import MLTTTyping LogicalRelation Reduction LRInduction.

Set Universe Polymorphism.
Require Import Arith.

Definition reflEq0 {Γ} {A} (H : [ Γ ||-< zero | A ] ) : [ Γ ||-< zero |  A ≅ A | H].
    cbn in H.
    unfold Rel1Ty in H.
    destruct H.
    destruct pack.
    revert Γ A relEq relTerm relEqTerm valid.      
    eapply LR_rect0.
    - intros.
      cbn. 
      destruct neA.
      econstructor;try eassumption.
    - intros. cbn in *.
      destruct H0.  
      econstructor; try eassumption.
      cbn in *.
      intros. apply TypePiCong.
      assumption.
      apply TypeRefl.
      assumption.
      apply TypeRefl.
      exact (conG _).
Defined.

Definition reflEq1 {Γ} {A} (H : [ Γ ||-< one | A ] ) : [ Γ ||-< one |  A ≅ A | H].
  cbn in H.
  unfold Rel1Ty in H.
  destruct H.  
  destruct pack.           
  cbn in *.
  eapply (LR_rect1 
  (fun Γ A T T0 T1 H => 
    [Γ ||-< zero | A ≅ A | LRValidMk (@LRPackMk Γ A T T0 T1) H])
  (fun Γ A T T0 T1 H => 
  [Γ ||-< one  | A ≅ A | LRValidMk (@LRPackMk Γ A T T0 T1) H])). 
  - intros.
    cbn. 
    destruct neA.
    econstructor;try eassumption.
  - intros. cbn in *.
    destruct H0.  
    econstructor; try eassumption.
    cbn in *.
    intros. apply TypePiCong.
    assumption.
    apply TypeRefl.
    assumption.
    apply TypeRefl.
    exact (conG _).
  - intros.
    cbn.
    constructor. reflexivity.
  - intros.
    cbn. 
    destruct neA.
    econstructor;try eassumption.
  - intros. cbn in *.
    destruct H0.  
    econstructor; try eassumption.
    cbn in *.
    intros. apply TypePiCong.
    assumption.
    apply TypeRefl.
    assumption.
    apply TypeRefl.
    exact (conG _).
  - intros. cbn in *.
    exact X.
  Unshelve. 
  all : assumption.
Defined.

Fixpoint reflEqTerm {Γ} {A t} (H : [ Γ ||-< zero | A ] ) : 
    [ Γ ||-< zero | t ::: A | H ] ->
    [ Γ ||-< zero | t ≅ t ::: A | H ].
    
Proof.
    destruct H.
    destruct pack.
    revert Γ A relEq relTerm relEqTerm valid.      
    eapply LR_rect0.
    exact valid.
    + intros.
      cbn.
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
  

      
      

      


    

    
    
    

