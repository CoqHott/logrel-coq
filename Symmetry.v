Require Import Untyped MLTTTyping LogicalRelation Properties Reduction LRInduction.

Set Universe Polymorphism.

Definition Sym0 {Γ A B} (ha : [Γ ||-< zero | A]) (hb : [Γ ||-< zero | B]) :
    [Γ ||-< zero | A ≅ B | ha ] ->
    [Γ ||-< zero | B ≅ A | hb ].
Proof.
    dependent inversion ha.
    dependent inversion hb. cbn in *.
    inversion valid; inversion valid0; cbn in *;
    try (inversion l_);try (inversion l_0); subst.
    + intro.
      destruct neA.
      econstructor;
      try eassumption. 
      destruct X.
      destruct neA0.
      cbn in *.
      eapply TypeTrans.
      exact (TypeSym (TypeRedWFConv D0)).
      eapply TypeTrans.
      exact (TypeRedWFConv D').
      apply TypeSym;assumption.
    + destruct neA.
      destruct H4.
      cbn in *.
      intro. 
      destruct X. cbn in *.
      admit.
    + admit. (*needs ShapeView*)
    + intro. 
      destruct H0,H6,H1,H7,X.
      all : cbn in *.
      econstructor; try eassumption.
      all : cbn in *.
      intros.
      eapply TypeTrans.
      exact (TypeSym (TypeRedWFConv (D'_0 _))).
      eapply TypeTrans.
      exact (TypeRedWFConv (D'' na)).
      exact (TypeSym (AeqB _ _)).
      intros.
      econstructor.


