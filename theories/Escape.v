From MetaCoq Require Import PCUICAst.
Require Import Automation Untyped MLTTTyping LogicalRelation Properties Reduction LRInduction.
Set Universe Polymorphism.

Definition escape0 {Γ A} :
    [Γ ||-< zero | A ] ->
    [Γ |- A].
Proof.
  destruct 1.
  eapply (LR_rect0 (fun Γ A _ _ _ _ => [Γ |- A])).
  3: eassumption.
  - intros ? ? neA.
    now destruct neA as [? []].
  - intuition.
Qed.

Definition escape1 {Γ A} :
    [Γ ||-< one | A ] ->
    [Γ |- A].
Proof.
  intros [? ? ? valid].
  red in valid ; cbn in *.
  eapply (LR_rect1' (fun Γ A _ _ _ _ => [Γ |- A]) (fun Γ A _ _ _ _ => [Γ |- A])).
  6: eassumption.
  - intros.
    eapply escape0.
    logrel.
  - intros ? [].
    mltt.
  - intros ? ? [].
    now destruct red.
  - intros ? ? [].
    now destruct red.
  - easy.
Qed.

Definition escapeEqNe {Γ0 A0 B} : forall (neA : [Γ0 ||-ne A0]),
    [Γ0 ||-ne A0 ≅ B | neA] ->
    [Γ0 |- A0 ≅ B].
Proof.
    intros [] [] ; cbn in *.
    do 2 eapply TypeTrans.
    all: mltt.
Qed.

Definition escapeEqPi {Γ A} : forall (ΠA : [Γ ||-Πr A]),
    forall B, [Γ ||-Π A ≅ B | ΠA] -> [Γ |- A ≅ B].
Proof.
  intros [] ? [].
  do 2 eapply TypeTrans.
  all: mltt.
Qed.

Definition escapeEq0 {Γ A B} (H : [Γ ||-< zero | A]) :
    [ Γ ||-< zero | A ≅ B | H ] ->
    [Γ |- A ≅ B].
Proof.
  eapply (LR_rect0
    (fun Γ A T T0 T1 H => forall B : term,
      [Γ ||-< zero | A ≅ B | Build_LRValid H] -> 
      [Γ |- A ≅ B])).
  + intros; now eapply escapeEqNe. 
  + intros; now eapply escapeEqPi.
Qed.

Definition escapeEq1 {Γ A B} (H : [Γ ||-< one | A]) :
    [ Γ ||-< one | A ≅ B | H ] ->
    [Γ |- A ≅ B].
Proof.
    eapply (LR_rect1'
      (fun Γ A T T0 T1 H => forall B : term,
        [Γ ||-< zero | A ≅ B | Build_LRValid H] -> 
        [Γ |- A ≅ B])
    (fun Γ A T T0 T1 H => forall B : term,
        [Γ ||-< one | A ≅ B | Build_LRValid H] -> 
        [Γ |- A ≅ B])). 
    all: cbn in *.
    - intros.
      now eapply (escapeEq0 (LRbuild lr)).
    - intros ? [] _ [->].
      mltt.
    - intros ? ? [] ? [] ; cbn in *.
      do 2 eapply TypeTrans.
      all: mltt.
    - intros.
      now eapply escapeEqPi.
    - eauto.
Qed.

Definition escapeTermNe {Γ0 A0 t}: forall
  (neA : [Γ0 ||-ne A0]),
  [Γ0 ||-ne t ::: A0 | neA] -> 
  [Γ0 |- t ::: A0].
Proof.
  intros [] [? []] ; cbn in *.
  mltt.
Qed.

Definition escapeTermPi {Γ A} : forall (ΠA : [Γ ||-Πr A]) (t : term), 
  [Γ ||-Π t ::: A | ΠA] -> 
  [Γ |- t ::: A].
Proof.
  intros [? ? ? ? []] ? [? []]; cbn in *.
  mltt.
Qed.

Definition escapeTerm0 {Γ t A} (H : [Γ ||-< zero | A ]) :
  [Γ ||-< zero | t ::: A | H ] ->
  [Γ |- t ::: A].
Proof.
  eapply (LR_rect0
    (fun Γ A T T0 T1 H => forall t : term,
      [Γ ||-< zero | t ::: A | Build_LRValid H] -> 
      [Γ |- t ::: A])).
  all: eauto using escapeTermNe, escapeTermPi.
Qed.

Definition escapeTerm1 {Γ t A} (H : [Γ ||-< one | A ]) :
  [Γ ||-< one | t ::: A | H ] ->
  [Γ |- t ::: A].
Proof.
  eapply (LR_rect1'
    (fun Γ A T T0 T1 H => forall t : term,
      [Γ ||-< zero | t ::: A | Build_LRValid H] -> 
      [Γ |- t ::: A])
      (fun Γ A T T0 T1 H => forall t : term,
      [Γ ||-< one | t ::: A | Build_LRValid H] -> 
      [Γ |- t ::: A])).
  all: cbn.
  - intros.
    now eapply (escapeTerm0 (LRbuild lr)).
  - intuition.
  - eauto using escapeTermNe.
  - eauto using escapeTermPi.
  - auto.
Qed.

Definition escapeEqTermNe {Γ0 A0 t u}: forall
  (neA : [Γ0 ||-ne A0]),
  [Γ0 ||-ne t ≅ u ::: A0 | neA] -> 
  [Γ0 |- t ≅ u ::: A0].
Proof.
  intros [] [? ? [] [] []].
  do 2 eapply TermTrans.
  all: mltt.
Qed.

Definition escapeEqTermPi {Γ A} : forall (ΠA: [Γ ||-Πr A]) t u,
  [Γ ||-Π t ≅ u ::: A | ΠA] -> 
  [Γ |- t ≅ u ::: A].
Proof.
  intros [? ? ? ? []] ? ? [? ? [] [] ? ? ?] ; cbn in *.
  eapply (TermTrans (t' := nfL)).
  1: mltt.
  assert [Γ |- redPi ≅ A] by mltt.
  eapply (TermTrans (t' := nfR)).
  all: mltt.
Qed.

Definition escapeEqTerm0 {Γ t u A} (H : [Γ ||-< zero | A ]) :
  [Γ ||-< zero | t ≅ u ::: A | H ] ->
  [Γ |- t ≅ u::: A].
Proof.
  eapply (LR_rect0
  (fun Γ A T T0 T1 H => forall t u,
    [Γ ||-< zero | t ≅ u ::: A | Build_LRValid H] -> 
    [Γ |- t ≅ u ::: A])).
  all: eauto using escapeEqTermNe, escapeEqTermPi.
Qed.

Definition escapeEqTerm1 {Γ t u A} (H : [Γ ||-< one | A ]) :
  [Γ ||-< one | t ≅ u ::: A | H ] ->
  [Γ |- t ≅ u::: A].
Proof.
  eapply (LR_rect1'
  (fun Γ A T T0 T1 H => forall t u,
    [Γ ||-< zero | t ≅ u ::: A | Build_LRValid H] -> 
    [Γ |- t ≅ u ::: A])
  (fun Γ A T T0 T1 H => forall t u,
    [Γ ||-< one | t ≅ u ::: A | Build_LRValid H] -> 
    [Γ |- t ≅ u ::: A])).
  all: cbn in *.
  - intros.
    now eapply (escapeEqTerm0 (LRbuild lr)).
  - intros ? [] ? ? [] ; cbn in *.
    do 2 eapply TermTrans.
    all: mltt.
  - eauto using escapeEqTermNe.
  - eauto using escapeEqTermPi.
  - eauto.
Qed.