
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping DeclarativeInstance Weakening GenericTyping.

From LogRel Require Import DirectedDirections.
From LogRel Require Import DirectedDeclarativeTyping DirectedContext.


Import Notations.
Import DeclarativeTypingData.
Import DeclarativeTypingProperties.

Definition erase_dir (ctx: DirectedContext.context) : Context.context := List.map DirectedContext.ty ctx.

Lemma in_ctx_erased {Θ n decl} :
  DirectedContext.in_ctx Θ n decl ->
  Context.in_ctx (erase_dir Θ) n (DirectedContext.ty decl).
Proof.
  induction 1; now constructor.
Qed.


Lemma typing_erased :
  (forall Θ, [ |-( ) Θ ] -> [ |- erase_dir Θ ])
    × (forall Θ d A,
        [ Θ |-( d ) A] -> [ erase_dir Θ |- A ])
    × (forall Θ dt A dA t,
        [ Θ |-( dt ) t : A @( dA ) ] -> [ erase_dir Θ |- t : A ])
    × (forall Θ d A B,
        [ Θ |-( d ) A ≅ B ] -> [ erase_dir Θ |- A ≅ B ])
    × (forall Θ dt A dA t u,
        [ Θ |-( dt ) t ≅ u : A @( dA ) ] -> [ erase_dir Θ |- t ≅ u : A ]).
Proof.
  eapply DirectedDeclarativeTyping.WfDeclInduction.
  all: try now econstructor.
  - intros Θ ? n ? A ? ? ? inctx ?.
    constructor; tea.
    now apply (in_ctx_erased inctx).
Qed.

