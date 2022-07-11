Require Import MLTTTyping LogicalRelation Reduction LRInduction.

Set Universe Polymorphism.
Check LR_rect.
Require Import Arith.
From Equations Require Import Equations.
Axiom todo : forall {A}, A.
(*Derive NoConfusion Subterm for LR.
Print LR_direct_subterm.*)
Check TyPiEqRel1Mk.
Equations reflEq {l} {Γ} {A} (H : [ Γ ||-< l | A ] ) : [ Γ ||-< l |  A ≅ A | H] :=
  reflEq (LRPackMk (LRU _ c a b)) := 
    URelEqMk _ _  eq_refl;
  reflEq (LRPackMk (LRne _ (ne _ _ k d nek kk))) :=
    nee _ _ A (ne _ _ k d nek kk) k d nek kk;
  reflEq (LRPackMk (LRemb _ l_ h)) :=
    (*reflEq h;*) todo; 
  reflEq (LRPackMk (LRPi _ (TyPiRelMk _ _ a b c d e f g h i)))
    (*Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext*) :=
    TyPiEqRel1Mk _ _ D f
       (fun h => reflEq (g h))
       (fun h2 ha => reflEq (h h2 ha)).

    (*cbn in H.
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
Admitted.*)



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
  

      
      

      


    

    
    
    

