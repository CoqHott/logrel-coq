
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping DeclarativeInstance Weakening GenericTyping.

From LogRel Require Import DirectedDirections.
From LogRel Require DirectedDeclarativeTyping DirectedContext.


Import DeclarativeTypingData.
Import DeclarativeTypingProperties.

Fixpoint erase_dir (ctx: DirectedContext.context) : context :=
  match ctx with
  | nil => nil
  | cons {| DirectedContext.ty := T |} l => cons T (erase_dir l)
  end.


Lemma in_ctx_erased {Θ n decl} :
  DirectedContext.in_ctx Θ n decl ->
  in_ctx (erase_dir Θ) n (DirectedContext.ty decl).
Proof.
  induction 1; now constructor.
Qed.

Lemma typing_erased :
  (forall Θ : DirectedContext.context,
      DirectedDeclarativeTyping.WfContextDecl Θ -> [ |- erase_dir Θ ])
    × (forall (Θ : DirectedContext.context) (d: direction) (A : term),
        DirectedDeclarativeTyping.WfTypeDecl Θ d A -> [ erase_dir Θ |- A ])
    × (forall (Θ : DirectedContext.context) (dt: direction) (A: term) (dA: direction) (t : term),
        DirectedDeclarativeTyping.TypingDecl Θ dt A dA t -> [ erase_dir Θ |- t : A ])
    × (forall (Θ : DirectedContext.context) (d: direction) (A B : term),
        DirectedDeclarativeTyping.ConvTypeDecl Θ d A B -> [ erase_dir Θ |- A ≅ B ])
    × (forall (Θ : DirectedContext.context) (dt: direction) (A : term) (dA: direction) (t u : term),
        DirectedDeclarativeTyping.ConvTermDecl Θ dt A dA t u -> [ erase_dir Θ |- t ≅ u : A ]).
Proof.
  eapply DirectedDeclarativeTyping.WfDeclInduction.
  all: try now econstructor.
  - intros Θ ? n ? A ? ? ? inctx ?.
    constructor; tea.
    now apply (in_ctx_erased inctx).
Qed.

