From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Untyped UntypedReduction GenericTyping LogicalRelation DeclarativeInstance.
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

  Lemma ShapeViewConv@{i j k l i' j' k' l'} {Γ A lA eqTyA redTmA eqTmA B lB eqTyB redTmB eqTmB}
    (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) (lrB : LogRel@{i' j' k' l'} lB Γ B eqTyB redTmB eqTmB) :
    eqTyA B ->
    ShapeView@{i j k l i' j' k' l'} Γ A B lrA lrB.
  Proof.
    destruct lrA.
    - destruct lrB.
      + constructor.
      + intros [red]; destruct neA as [? red' ne ?] .
        unshelve epose proof (redtywf_det _ _ _ _ _ _ red red'); subst.
        3: exfalso.
        all: apply ty_ne_whne in ne; gen_typing.
      + intros [red]. destruct ΠA as [??? red'].
        unshelve epose proof (e:= redtywf_det _ _ _ _ _ _ red red').
        1,2: gen_typing.
        discriminate e.
    - destruct lrB as [?? [??? red]| |].
      + intros [? red' ne].
        unshelve epose proof (redtywf_det _ _ _ _ _ _ red red'); subst.
        3: exfalso.
        all: apply ty_ne_whne in ne; gen_typing.
      + econstructor.
      + intros [].
        destruct ΠA ; cbn in *.
        apply ty_ne_whne in ne.
        enough (ty = tProd na dom cod) as -> by (now eapply nePi).
        eapply whredty_det.
        all: gen_typing.
    - destruct lrB as [?? [??? red]| |].
      + intros [??? red'].
        unshelve epose proof (e:= redtywf_det _ _ _ _ _ _ red red').
        1,2: gen_typing.
        discriminate e.
      + intros [].
        destruct neA.
        simpl; apply ty_ne_whne in ne.
        enough (ty = tProd na dom cod) as -> by (now eapply nePi).
        eapply whredty_det.
        all: gen_typing.
      + now econstructor.
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
