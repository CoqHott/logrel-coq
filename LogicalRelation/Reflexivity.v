Require Import MLTTTyping LogicalRelation Reduction.

Set Universe Polymorphism.
Axiom todo : forall {A}, A.

Fixpoint reflEq {l} {Γ} {A} (H : [ Γ ||-< l | A ] ) : [ Γ ||-< l |  A ≅ A | H].
    cbn in H.
    unfold Rel1Ty in H.
    destruct H.
    cbn.
    induction relLR.
    + apply URelEqMk.
      reflexivity.
    + destruct neA.
      eapply nee.
      destruct D.
      eapply mkTypeRedWF;
      try eassumption.
      apply typeRedId.
      assumption.
      exact neK.
      cbn.
      apply TypeRefl.
      destruct D.
      assumption.
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
      apply (reflEq l).
      cbn.
      intros.
      apply (reflEq l).
    + inversion l_.
      subst.
      cbn in *.
      unfold Rel1TyEq.
      exact todo.
      (*eapply reflEq.*)
Admitted.



Fixpoint reflEqTerm {l} {Γ} {A t} (H : [ Γ ||-< l | A ] ) : 
    [ Γ ||-< l | t ::: A | H ] ->
    [ Γ ||-< l | t ≅ t ::: A | H ].
    intro.
    destruct H.
    cbn in X.
    destruct l;
    destruct relLR.
    all : cbn in *.
    + destruct X.      
      eapply UTeEqMk ; try eassumption;
      destruct dd.
      eapply TermRefl.
      assumption.
      cbn in *.
      admit.
    + destruct neA;
      destruct X; cbn in *.

      eapply neTeEq.
      * assert [Γ |- A ≅ K].
        destruct D.
        exact (RedConvTyC D).
        destruct d.
        gen_conv. eassumption.
        
        constructor.
        eapply wfTermConv. eassumption.
        apply TypeSym. assumption.
        eapply wfTermConv. eassumption.
        apply TypeSym. assumption.
        eapply ClosureConv. eassumption.
        exact (TypeSym X).
      * assert [Γ |- A ≅ K].
        destruct D.
        exact (RedConvTy_ D).

        destruct d.
        constructor.
        eapply wfTermConv. eassumption.
        apply TypeSym. assumption.
        eapply wfTermConv. eassumption.
        apply TypeSym. assumption.
        eapply ClosureConv. eassumption.
        exact (TypeSym X).
      * destruct nf.
        constructor; try assumption.
        apply TermRefl.
        eapply wfTermConv.
        eassumption.
        destruct D.      
        exact (TypeSym (RedConvTy_ D)).
    + inversion X.
      econstructor;
      try eassumption.
      intros.
      eapply appf.

    + admit.
    +

  

      
      

      


    

    
    
    

