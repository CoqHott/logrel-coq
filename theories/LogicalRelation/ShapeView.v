(** * LogRel.LogicalRelation.ShapeView: relating reducibility witnesses of reducibly convertible types.*)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst LContexts Context Notations NormalForms UntypedReduction GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity.

Set Universe Polymorphism.

Section ShapeViews.
  Context `{GenericTypingProperties}.

(** ** Definition *)

(** A shape view is inhabited exactly on the diagonal, ie when the two types are reducible
  in the same way. *)

  Definition ShapeView@{i j k l i' j' k' l'} wl Γ
    A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB}
    (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA redTyA) (lrB : LogRel@{i' j' k' l'} lB wl Γ B eqTyB redTmB redTyB) : Set :=
    match lrA, lrB with
      | LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _ => True
      | LRNat _ _, LRNat _ _ => True
      | LRBool _ _, LRBool _ _ => True
      | LREmpty _ _, LREmpty _ _ => True
      | _, _ => False
    end.

  Arguments ShapeView wl Γ A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB}
  !lrA !lrB.

(** ** The main property *)

(** We show that two reducibly convertible types must have the same shape view. Said otherwise,
if two reducible types are reducibly convertible, then they must be reducible in the same way.
This lets us relate different reducibility proofs when we have multiple such proofs, typically
when showing symmetry or transitivity of the logical relation. *)

  Arguments ShapeView wl Γ A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB}
  !lrA !lrB.


  Lemma red_whnf@{i j k l} {wl Γ A lA eqTyA redTmA eqTmA}
    (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA) : 
    ∑ nf, [Γ |- A :⇒*: nf]< wl > × whnf wl nf.
  Proof.
    destruct lrA as [??? []| ??? [] | ??? []| ??? [] | ??? [] | ??? []];
      eexists; split; tea; constructor; tea.
    now eapply ty_ne_whne.
  Defined.

  Lemma eqTy_red_whnf@{i j k l} {wl Γ A lA eqTyA redTmA eqTmA B}
    (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA) : 
    eqTyA B -> ∑ nf, [Γ |- B :⇒*: nf]< wl > × whnf wl nf.
  Proof.
    destruct lrA as [??? []| ???[] | ???[]| ???[] | ???[] | ???[]] ; intros []; eexists; split; tea; constructor; tea.
    now eapply ty_ne_whne.
  Defined.


  Lemma ShapeViewConv@{i j k l i' j' k' l'} {wl Γ A lA eqTyA redTmA eqTmA B lB eqTyB redTmB eqTmB}
    (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA) (lrB : LogRel@{i' j' k' l'} lB wl Γ B eqTyB redTmB eqTmB) :
    eqTyA B ->
    ShapeView@{i j k l i' j' k' l'} wl Γ A B lrA lrB.
  Proof.
    intros eqAB.
    pose (x := eqTy_red_whnf lrA eqAB).
    pose (y:= red_whnf lrB).
    pose proof (h := redtywf_det _ _ _ _ _ (snd x.π2) (snd y.π2) (fst x.π2) (fst y.π2)).
    revert eqAB x y h. 
    destruct lrA; destruct lrB; intros []; cbn; try easy; try discriminate.
    all: try now (intros e; rewrite e in ne; apply ty_ne_whne in ne; inversion ne).
    all: try now (intros e; destruct neA as [? ? ne]; rewrite <- e in ne; apply ty_ne_whne in ne; inversion ne).
  Qed.

(** ** More properties *)

  Corollary ShapeViewRefl@{i j k l i' j' k' l'} {wl Γ A lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
    (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel@{i' j' k' l'} lA' wl Γ A eqTyA' redTmA' eqTmA') :
    ShapeView@{i j k l i' j' k' l'} wl Γ A A lrA lrA'.
  Proof.
    now eapply ShapeViewConv, LRTyEqRefl.
  Qed.


  Definition ShapeView3 wl Γ
    A {lA eqTyA redTmA redTyA}
    B {lB eqTyB redTmB redTyB}
    C {lC eqTyC redTmC redTyC}
    (lrA : LogRel lA wl Γ A eqTyA redTmA redTyA)
    (lrB : LogRel lB wl Γ B eqTyB redTmB redTyB)
    (lrC : LogRel lC wl Γ C eqTyC redTmC redTyC)
    : Set :=
    match lrA, lrB, lrC with
      | LRU _ _, LRU _ _, LRU _ _ => True
      | LRne _ _, LRne _ _, LRne _ _ => True
      | LRPi _ _ _, LRPi _ _ _, LRPi _ _ _ => True
      | LRNat _ _, LRNat _ _, LRNat _ _ => True
      | LRBool _ _, LRBool _ _, LRBool _ _ => True
      | LREmpty _ _, LREmpty _ _, LREmpty _ _ => True
      | _, _, _ => False
    end.


  Arguments ShapeView3 wl Γ A {lA eqTyA redTmA redTyA} B {lB eqTyB redTmB redTyB} C {lC eqTyC redTmC redTyC}
  !lrA !lrB !lrC.

  Lemma combine wl Γ
    A {lA eqTyA redTmA redTyA}
    B {lB eqTyB redTmB redTyB}
    C {lC eqTyC redTmC redTyC}
    (lrA : LogRel lA wl Γ A eqTyA redTmA redTyA)
    (lrB : LogRel lB wl Γ B eqTyB redTmB redTyB)
    (lrC : LogRel lC wl Γ C eqTyC redTmC redTyC) :
    ShapeView wl Γ A B lrA lrB -> ShapeView wl Γ B C lrB lrC -> ShapeView3 wl Γ A B C lrA lrB lrC.
  Proof.  destruct lrA, lrB, lrC; easy. Qed.

End ShapeViews.
