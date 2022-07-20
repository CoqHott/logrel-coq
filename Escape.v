Require Import Untyped MLTTTyping LogicalRelation Properties Reduction LRInduction.
Set Universe Polymorphism.

Definition escape0 {Γ A} :
    [Γ ||-< zero | A ] ->
    [Γ |- A].
Proof.
    intros.
    destruct X.
    destruct pack.
    eapply (LR_rec0 Γ A). exact valid.
    + intros. destruct neA.
      destruct D. assumption.
    + intros. destruct H0. cbn in *.
      destruct (D'_ emptyName).
      assumption.
Defined.

Definition escape1 {Γ A} :
    [Γ ||-< one | A ] ->
    [Γ |- A].
Proof.
    intros.
    destruct X.
    inversion pack.
    refine (LR_rec1 Γ A _ _ _ valid 
      (fun Γ A T T0 T1 H => 
        [Γ ||-< zero | A] ->
        [Γ |- A]) 
      (fun Γ A T T0 T1 H => 
        [Γ ||-< one | A] ->
        [Γ |- A]) _ _ _ _ _ _ _).
    1, 4 : intros; destruct neA;
      destruct D; exact wfA.
    1, 3 : intros; destruct H0; 
      destruct (D'_ emptyName);
      assumption.
    + intros.
      constructor. assumption.
    + intros.
      eapply X.
      exact H.
    + econstructor; eassumption.
Defined.

Definition escapeEqNe {Γ0 A0 B} : forall (neA : [Γ0 ||-ne A0]),
    [Γ0 ||-ne A0 ≅ B | neA] ->
    [Γ0 |- A0 ≅ B].
Proof.
    intros. destruct neA.
    destruct X.
    pose proof (TypeRedWFConv D).
    pose proof (TypeSym (TypeRedWFConv D')).
    eapply TypeTrans. eassumption.
    eapply TypeTrans. eassumption.
    eassumption.
Defined.

Definition escapeEqPi {Γ0 A0} l : forall (H0 : [Γ0 ||-0Π A0]) 
    (H1 : TyPiRel1 (LR (recl l)) H0),
    (forall (Δ : PCUICAst.PCUICEnvironment.context) (h : [  |- Δ])
       (B : PCUICAst.term), LogicalRelation.relEq (_F H0 h) B -> [Δ |- F H0 ≅ B]) ->
    (forall (Δ : PCUICAst.PCUICEnvironment.context) (a : PCUICAst.term)
       (h1 : [  |- Δ])
       (h2 : [Δ ||-1 a ::: F H0 | {| pack := _F H0 h1; valid := _F1 H1 h1 |}])
       (B : PCUICAst.term),
     LogicalRelation.relEq (_G H0 h1 h2) B ->
     [Δ |- PCUICAst.subst1 a 0 (G H0) ≅ B]) ->
    forall B, [Γ0 ||-1Π A0 ≅ B | H0] -> [Γ0 |- A0 ≅ B].
Proof.
    intros. destruct H0.
    pose proof (TypeRedWFConv (D'_ emptyName)).
    eapply TypeTrans. eassumption.
    destruct X1.
    pose proof (TypeRedWFConv (D'' emptyName)).
    eapply TypeTrans.
    2 : exact (TypeSym X1).
    exact (AeqB _ _).
Defined.

Definition escapeEq0 {Γ A B H} :
    [ Γ ||-< zero | A ≅ B | H ] ->
    [Γ |- A ≅ B].
Proof.
    intros.
    destruct H.
    destruct pack.
    revert B X.
    eapply (LR_rec0 Γ A _ _ _ valid
      (fun Γ A T T0 T1 H => forall B : PCUICAst.term,
        [Γ ||-< zero | A ≅ B | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
        [Γ |- A ≅ B])).
    + intros; now eapply escapeEqNe. 
    + intros; now eapply (escapeEqPi zero).
    Unshelve.
    all : assumption.
Defined.

Definition escapeEq1 {Γ A B H} :
    [ Γ ||-< one | A ≅ B | H ] ->
    [Γ |- A ≅ B].
Proof.
    intros.
    destruct H.
    destruct pack.
    revert B X.
    eapply (LR_rec1 Γ A _ _ _ valid
      (fun Γ A T T0 T1 H => forall B : PCUICAst.term,
        [Γ ||-< zero | A ≅ B | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
        [Γ |- A ≅ B])
    (fun Γ A T T0 T1 H => forall B : PCUICAst.term,
        [Γ ||-< one | A ≅ B | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
        [Γ |- A ≅ B])).
    all :cbn in *.
    1, 4 : intros; now eapply escapeEqNe.
    1 : intros; now eapply (escapeEqPi zero).
    2 : intros; now eapply (escapeEqPi one).
    + intros.
      destruct H. rewrite Beq; constructor.
      constructor. assumption.
    + intros.
      eapply X; eassumption.
    Unshelve.
    all : eassumption.
Defined.

Definition escapeTermNe {Γ0 A0 t}: forall
  (neA : [Γ0 ||-ne A0]),
  [Γ0 ||-ne t ::: A0 | neA] -> 
  [Γ0 |- t ::: A0].
Proof.
  intros. 
  destruct neA.
  destruct X.
  gen_conv.
  destruct X1.
  exact (redFirstCTerm C).
Defined.

Definition escapeTermPi {Γ0 A0} l : forall   
  (H0 : [Γ0 ||-0Π A0]) 
  (H1 : TyPiRel1 (LR (recl l)) H0),
  (forall (Δ : PCUICAst.PCUICEnvironment.context) 
     (h : [  |- Δ]) (t : PCUICAst.term),
   LogicalRelation.relTerm (_F H0 h) t -> [Δ |- t ::: F H0]) ->
  (forall (Δ : PCUICAst.PCUICEnvironment.context) 
     (a : PCUICAst.term) (h1 : [  |- Δ])
     (h2 : [Δ ||-1 a ::: F H0 | {| pack := _F H0 h1; valid := _F1 H1 h1 |}])
     (t : PCUICAst.term),
   LogicalRelation.relTerm (_G H0 h1 h2) t ->
   [Δ |- t ::: PCUICAst.subst1 a 0 (G H0)]) ->
  forall t : PCUICAst.term, 
  [Γ0 ||-1Π t ::: A0 | H0] -> 
  [Γ0 |- t ::: A0].
Proof.
  intros. destruct H0.      
  destruct X1. cbn in *.
  eapply wfTermConv.
  destruct (redf emptyName).
  exact wft.
  exact (TypeSym (TypeRedWFConv (D'_ emptyName))).
Defined.

Definition escapeTerm0 {Γ t A} : forall 
    (H : [Γ ||-< zero | A ]),
    [Γ ||-< zero | t ::: A | H ] ->
    [Γ |- t ::: A].
Proof.
    intros.
    destruct H.
    destruct pack.
    revert t X.
    eapply (LR_rec0 Γ A _ _ _ valid
      (fun Γ A T T0 T1 H => forall t : PCUICAst.term,
        [Γ ||-< zero | t ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
        [Γ |- t ::: A])).
    + intros. now eapply escapeTermNe.
    + intros. now eapply (escapeTermPi zero).
    Unshelve.
    all : assumption.
Defined.

Definition escapeTerm1 {Γ t A} : forall 
    (H : [Γ ||-< one | A ]),
    [Γ ||-< one | t ::: A | H ] ->
    [Γ |- t ::: A].
Proof.
    intros.
    destruct H.
    destruct pack.
    revert t X.
    eapply (LR_rec1 Γ A _ _ _ valid
      (fun Γ A T T0 T1 H => forall t : PCUICAst.term,
        [Γ ||-< zero | t ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
        [Γ |- t ::: A])
        (fun Γ A T T0 T1 H => forall t : PCUICAst.term,
        [Γ ||-< one | t ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
        [Γ |- t ::: A])).
    1, 4 : intros; now eapply escapeTermNe.
    1 : intros; now eapply (escapeTermPi zero).
    2 : intros; now eapply (escapeTermPi one).
    + intros. cbn in *.
      destruct X.
      exact (redFirstCWFTerm dd).
    + intros. cbn in *.
      apply X; eassumption.
    Unshelve.
    all : eassumption.
Defined.

Definition escapeEqTermNe {Γ0 A0 t u}: forall  
  (neA : [Γ0 ||-ne A0]),
  [Γ0 ||-ne t ≅ u ::: A0 | neA] -> 
  [Γ0 |- t ≅ u ::: A0].
Proof.
  intros.
  destruct X.
  destruct kNFEqm.
  eapply TermTrans.
  exact (RedConvTeWFC d').
  eapply TermTrans. exact kEqm.
  exact (TermSym (RedConvTeWFC d'')).
Defined.

Definition escapeEqTermPi {Γ0 A0} l : forall 
  (H0 : [Γ0 ||-0Π A0]) (H1 : TyPiRel1 (LR (recl l)) H0),
  (forall Δ (h : [  |- Δ]) t u,
   LogicalRelation.relEqTerm (_F H0 h) t u -> [Δ |- t ≅ u ::: F H0]) ->
  (forall Δ a
     (h1 : [  |- Δ])
     (h2 : [Δ ||-1 a ::: F H0 | {| pack := _F H0 h1; valid := _F1 H1 h1 |}])
     t u,
   LogicalRelation.relEqTerm (_G H0 h1 h2) t u ->
   [Δ |- t ≅ u ::: PCUICAst.subst1 a 0 (G H0)]) ->
  forall t u,
  [Γ0 ||-1Π t ≅ u ::: A0 | H0] -> 
  [Γ0 |- t ≅ u ::: A0].
Proof.
  intros.
  destruct X1.
  destruct H0. cbn in *.
  eapply TermConv.
  2 : exact (TypeSym (TypeRedWFConv (D'_ emptyName))).
  eapply TermTrans.
  exact (RedConvTeWFC (redf' emptyName)).
  eapply TermTrans.
  exact (fEqg emptyName).
  exact (TermSym (RedConvTeWFC (redg' emptyName))).
Defined.

Definition escapeEqTerm0 {Γ t u A} : forall 
    (H : [Γ ||-< zero | A ]),
    [Γ ||-< zero | t ≅ u ::: A | H ] ->
    [Γ |- t ≅ u::: A].
Proof.
  intros.
  destruct H.
  destruct pack.
  revert t u X.
  eapply (LR_rec0 Γ A _ _ _ valid
  (fun Γ A T T0 T1 H => forall t u,
    [Γ ||-< zero | t ≅ u ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
    [Γ |- t ≅ u ::: A])).
  cbn in *.
  + intros; now eapply escapeEqTermNe.
  + intros; eapply (escapeEqTermPi zero).
  Unshelve.
  all : eassumption.
Defined.

Definition escapeEqTerm1 {Γ t u A} : forall 
    (H : [Γ ||-< one | A ]),
    [Γ ||-< one | t ≅ u ::: A | H ] ->
    [Γ |- t ≅ u::: A].
Proof.
  intros.
  destruct H.
  destruct pack.
  revert t u X.
  eapply (LR_rec1 Γ A _ _ _ valid
  (fun Γ A T T0 T1 H => forall t u,
    [Γ ||-< zero | t ≅ u ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
    [Γ |- t ≅ u ::: A])
  (fun Γ A T T0 T1 H => forall t u,
    [Γ ||-< one | t ≅ u ::: A | LRValidMk (@LRPackMk Γ A T T0 T1) H] -> 
    [Γ |- t ≅ u ::: A])).
  1, 4 : intros; now eapply escapeEqTermNe.
  1 : intros; now eapply (escapeEqTermPi zero).
  2 : intros; now eapply (escapeEqTermPi one).
  + intros.
    destruct X.
    eapply TermTrans.
    exact (RedConvTeWFC d_).
    eapply TermTrans.
    exact AeqBU.
    exact (TermSym (RedConvTeWFC dd')).
  + intros. cbn in *.
    eapply X; try eassumption.
  Unshelve.
  all : eassumption.
Defined.
