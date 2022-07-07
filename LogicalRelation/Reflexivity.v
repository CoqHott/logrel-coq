Require Import MLTTTyping LogicalRelation Reduction LRInduction.

Set Universe Polymorphism.
Check LR_rect.

Axiom todo : forall {A}, A.

Fixpoint reflEq {l} {Γ} {A} (H : [ Γ ||-< l | A ] ) : [ Γ ||-< l |  A ≅ A | H].
    cbn in H.
    unfold Rel1Ty in H.
    destruct H.
    cbn.
    induction relLR.
    + constructor.
      reflexivity.
    + destruct neA.
      econstructor; try eassumption.
      destruct D.
      constructor; try eassumption.
      constructor. assumption.
      exact (TypeRefl (wfB _ _ _ D)).
    + induction H.
      eapply TyPiEqRel1Mk.      
      intro.
      destruct (D'_ na).
      apply mkTypeRedWF;
      eassumption.
      intros.
      cbn.
      apply TypePiCong.
      assumption.
      apply TypeRefl.
      assumption.
      apply TypeRefl.
      exact (conG _).
      intros.
      cbn.
      apply X. assumption.
    + inversion l_.
      subst.
      cbn in reflEq.
      (*exact (reflEq _ _ _ H).*)
      admit.
Admitted.



Fixpoint reflEqTerm {l} {Γ} {A t} (H : [ Γ ||-< l | A ] ) : 
    [ Γ ||-< l | t ::: A | H ] ->
    [ Γ ||-< l | t ≅ t ::: A | H ].
Proof.
    intro.
    destruct H.
    cbn in X.
    induction relLR.
    all : cbn in *.
    + destruct X.
      econstructor;
      try eassumption.
      exact (TermRefl (wfu _ _ _ _ dd)).
      (*eapply reflEq.*)
      exact todo.
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
  

      
      

      


    

    
    
    

