From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context NormalForms UntypedReduction GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity.

Set Universe Polymorphism.

Section ShapeViews.
  Context `{GenericTypingProperties}.

  Definition ShapeView@{i j k l i' j' k' l'} Γ
    A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA redTyA) (lrB : LogRel@{i' j' k' l'} lB Γ B eqTyB redTmB redTyB) : Set :=
    match lrA, lrB with
      | LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _ => True
      | _, _ => False
    end.

    (* | SVU (UredA UredB : [ Γ ||-U l]):
          ShapeView l Γ U U (LRU (LogRelRec l) UredA) (LRU (LogRelRec l) UredB)

      | SVne {A B} neA neB :
          ShapeView l Γ A B (LRne (LogRelRec l) neA) (LRne (LogRelRec l) neB)

      | SVPi {A B} ΠA ΠB ΠAad ΠBad:
          ShapeView l Γ A B (LRPi (LogRelRec l) ΠA ΠAad) (LRPi (LogRelRec l) ΠB ΠBad). *)

  Arguments ShapeView Γ A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB}
  !lrA !lrB.


  Lemma red_whnf@{i j k l} {Γ A lA eqTyA redTmA eqTmA}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) : 
    ∑ nf, [Γ |- A :⇒*: nf] × whnf nf.
  Proof.
    destruct lrA as [?? []| ??[] | ??[]]; eexists; split; tea; constructor; tea.
  Defined.
  
  Lemma eqTy_red_whnf@{i j k l} {Γ A lA eqTyA redTmA eqTmA B}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) : 
    eqTyA B -> ∑ nf, [Γ |- B :⇒*: nf] × whnf nf.
  Proof.
    destruct lrA as [?? []| ??[] | ??[]] ; intros []; eexists; split; tea; constructor; tea.
  Defined.



  Lemma ShapeViewConv@{i j k l i' j' k' l'} {Γ A lA eqTyA redTmA eqTmA B lB eqTyB redTmB eqTmB}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) (lrB : LogRel@{i' j' k' l'} lB Γ B eqTyB redTmB eqTmB) :
    eqTyA B ->
    ShapeView@{i j k l i' j' k' l'} Γ A B lrA lrB.
  Proof.
    intros eqAB.
    pose (x := eqTy_red_whnf lrA eqAB).
    pose (y:= red_whnf lrB).
    pose proof (h := redtywf_det _ _ _ _ (snd x.π2) (snd y.π2) (fst x.π2) (fst y.π2)).
    revert eqAB x y h. 
    destruct lrA; destruct lrB; intros []; cbn; try easy; try discriminate.
    2-3: intros e; rewrite e in ne; inversion ne.
    all: intros e; destruct neA as [? ? ne]; rewrite <- e in ne; inversion ne.
  Qed.

  Corollary ShapeViewRefl@{i j k l i' j' k' l'} {Γ A lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel@{i' j' k' l'} lA' Γ A eqTyA' redTmA' eqTmA') :
    ShapeView@{i j k l i' j' k' l'} Γ A A lrA lrA'.
  Proof.
    now eapply ShapeViewConv, LRTyEqRefl.
  Qed.


  Definition ShapeView3 Γ
    A {lA eqTyA redTmA redTyA}
    B {lB eqTyB redTmB redTyB}
    C {lC eqTyC redTmC redTyC}
    (lrA : LogRel lA Γ A eqTyA redTmA redTyA)
    (lrB : LogRel lB Γ B eqTyB redTmB redTyB)
    (lrC : LogRel lC Γ C eqTyC redTmC redTyC)
    : Set :=
    match lrA, lrB, lrC with
      | LRU _ _, LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _, LRPi _ _ _ => True
      | _, _, _ => False
    end.


  Arguments ShapeView3 Γ A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB} C {lC eqTyC redTmC redTyC}
  !lrA !lrB !lrC.

  Lemma combine Γ
    A {lA eqTyA redTmA redTyA}
    B {lB eqTyB redTmB redTyB}
    C {lC eqTyC redTmC redTyC}
    (lrA : LogRel lA Γ A eqTyA redTmA redTyA)
    (lrB : LogRel lB Γ B eqTyB redTmB redTyB)
    (lrC : LogRel lC Γ C eqTyC redTmC redTyC) :
    ShapeView Γ A B lrA lrB -> ShapeView Γ B C lrB lrC -> ShapeView3 Γ A B C lrA lrB lrC.
  Proof.  destruct lrA, lrB, lrC; easy. Qed.

End ShapeViews.
