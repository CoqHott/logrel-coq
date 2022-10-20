From MetaCoq Require Import PCUICAst.
From LogRel Require Import Automation Untyped MLTTTyping LogicalRelation Properties Reduction.

Set Universe Polymorphism.

Inductive ShapeView l Γ :
    forall A B, [Γ ||-< l > A] -> [Γ ||-< l > B] -> Type 
:=
    | SVU (Ured Ured' : [ Γ ||-U l]):
        ShapeView l Γ U U (LRU_ Ured) (LRU_ Ured')

    | SVne {A B} neA neB :
        ShapeView l Γ A B (LRne_ l neA) (LRne_ l neB)

    | SVPi {A B} ΠA ΠB ΠAvalid ΠBvalid:
        ShapeView l Γ A B (LRPi_ l ΠA ΠAvalid) (LRPi_ l ΠB ΠBvalid).


Lemma ShapeView0_conv {l Γ A B} (lrA : [Γ ||-< l > A]) (lrB : [Γ ||-< l > B]) :
  [Γ ||-< l > A ≅ B | lrA] ->
  ShapeView l Γ A B lrA lrB.
Proof.
  destruct lrA as [[] vA], lrB as [[] vB] ; cbn in *.
  do 2 red in vA, vB ; cbn in *.
  destruct vA.
  - destruct vB.
    + econstructor.
    + intros [->].
      exfalso.
      inversion neA.
      enough (ty = U) as -> by (now eapply neU).
      eapply nred_det_ty.
      all: mltt.
    + intros [->].
      exfalso.
      inversion ΠA.
      enough (U = redPi) by (unfold U, redPi in * ; congruence).
      eapply nred_det_ty.
      2: mltt.
      mltt.
  - destruct vB.
    + intros [].
      exfalso.
      inversion neA.
      enough (ty = U) as -> by (now eapply neU).
      eapply nred_det_ty.
      all: mltt.
    + econstructor.
    + intros [].
      exfalso.
      destruct ΠA ; cbn in *.
      enough (ty = redPi) as -> by (now eapply nePi).
      unfold redPi.
      eapply nred_det_ty.
      all: mltt.
  - destruct vB.
    + intros [].
      exfalso.
      inversion ΠA.
      enough (U = redPi) by (unfold U, redPi in * ; congruence).
      eapply nred_det_ty.
      2: mltt.
      mltt.
    + intros [].
      exfalso.
      destruct neA.
      enough (ty = redPi) as -> by now (eapply nePi).
      unfold redPi.
      eapply nred_det_ty.
      all: mltt.
    + econstructor.
Qed.