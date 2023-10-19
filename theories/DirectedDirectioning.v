(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations DirectedDirections DirectedContext DeclarativeTyping.

Set Primitive Projections.


Import DeclarativeTypingData.
(* Import DeclarativeTypingProperties. *)
(* Import Notations. *)

Reserved Notation "[ δ |- t @ d ]" (at level 0, δ, d, t at level 50, only parsing).

(* TODO [TL]: note this is a "declarative" version, but we could also go algorithmic *)
Inductive DirDecl : list direction -> direction -> term -> Type :=
| dirU {δ d} : [ δ |- U @ d ]
| dirVar {δ d d' n} :
  List.nth_error δ n = Some d ->
  dir_leq d d' ->
  [ δ |- tRel n @ d' ]
| dirProd {δ d A B} :
  [ δ |- A @ dir_op d ] ->
  [ cons Discr δ |- B @ d ] ->
  [ δ |- tProd A B @ d ]
| dirLam {δ d A t} :
  [ cons Discr δ |- t @ d ] ->
  [ δ |- tLambda A t @ d ]
| dirApp {δ d f a} :
  [ δ |- f @ d ] ->
  [ δ |- a @ Discr ] ->
  [ δ |- tApp f a @ d ]
where "[ δ |- t @ d ]" := (DirDecl δ d t).

(* TODO: check substitution lemmata for typing *)
(* Lemma DirSubst {δ dB B da a} : *)
(*   [ δ |- a @ da ] -> [ cons da δ |- B @ dB ] -> [ δ |- B[a..] @ dB ]. *)
(* Proof. *)
(*   intros wda wdB. *)
(*   induction wdB. *)
(*   - constructor. *)
(*   - admit. *)
(*   - cbn. *)


Reserved Notation "[ |-( ) Γ ]" (at level 0, Γ at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ]" (at level 0, Γ, d, A at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t : A @( dA ) ]" (at level 0, Γ, dt, t, A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅ t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).
(* Reserved Notation "[ Γ |-( dt ) t ⤳* u ∈ A @( dA ) ]" (at level 0, Γ, dt, t, u, A, dA at level 50). *)

Fixpoint WfCtx (ctx: context) : Type :=
  match ctx with
  | nil => unit
  | cons {| ty := A ; ty_dir := dA ; dir := _ |} Θ =>
      [ |-( ) Θ ] × [ List.map ty Θ |- A ] × [ List.map dir Θ |- A @ dA ]
  end
    where "[ |-( ) Θ ]" := (WfCtx Θ).


Lemma WfCtx_erased {Θ: context} : [ |-( ) Θ ] -> [ |- List.map ty Θ ].
Proof.
  induction Θ.
  - intros. constructor.
  - intros [wfΘ [? ?]]. now constructor.
Qed.

Definition WfType (Θ: context) (d: direction) (A: term) : Type :=
  [ |-( ) Θ ] × [ List.map ty Θ |- A ] × [ List.map dir Θ |- A @ d ].
Notation "[ Θ |-( d ) A ]" := (WfType Θ d A).

Lemma WfCtx_in_ctx {Θ d dA A} :
  [ |-( ) Θ ] -> forall n, in_ctx Θ n {| ty := A; ty_dir := dA; dir := d |} ->
  ([ List.map ty Θ |- A ] × [ List.map dir Θ |- A @ dA ]).
Proof.
Admitted.

Lemma wfTypeU {Θ d} : [ |-( ) Θ ] -> [ Θ |-( d ) U ].
Proof.
  intros wfΘ.
  constructor ; [ now trivial | split ].
  - constructor. now eapply WfCtx_erased.
  - constructor.
Qed.

Lemma wfTypeProd {Γ d} {A B} :
  [ Γ |-( dir_op d ) A ] ->
  [Γ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B ] ->
  [ Γ |-( d ) tProd A B ].
Proof.
  intros [wfA [? ?]] [wfB [? ?]].
  constructor ; [ now trivial | split ].
  all: now constructor.
Qed.

Definition Typing (Θ: context) (dt: direction) (T: term) (dT: direction) (t: term) :=
  [ Θ |-( dT ) T ] × [ List.map ty Θ |- t : T ] × [ List.map dir Θ |- t @ dt ].
Notation "[ Γ |-( dt ) t : T @( dT ) ]" := (Typing Γ dt T dT t).

Lemma wfTypeUniv {Θ d} {A} :
  [ Θ |-( d ) A : U @( Discr ) ] ->
  [ Θ |-( d ) A ].
Proof.
  intros [[wfθ ?] [wtA wdA]].
  constructor ; [ now trivial | split ].
  - now apply wfTypeUniv.
  - assumption.
Qed.


Lemma wfVar {Θ d'} {n d T dT} :
  [ |-( ) Θ ] ->
  in_ctx Θ n {| ty := T; ty_dir := dT; dir := d |} ->
  dir_leq d d' ->
  [ Θ |-( d' ) tRel n : T @( dT ) ].
Proof.
  intros wfΘ inΘ dleq.
  split.
  - constructor ; [ now trivial | split ].
    + eapply WfCtx_in_ctx; tea.
    + eapply WfCtx_in_ctx; tea.
  - split.
    + constructor.
      * now apply WfCtx_erased.
      * admit.
    + eapply dirVar; tea.
      clear wfΘ dleq d'.
      revert Θ T dT d inΘ.
      induction n.
      * intros Θ T dT d inΘ. inversion inΘ; subst. reflexivity.
      * intros Θ T dT d inΘ. inversion inΘ; subst; cbn.
        now eapply IHn.
Admitted.

Lemma wfTermProd {Θ d} {A B} :
  [ Θ |-( dir_op d ) A : U @( Discr ) ] ->
  [ Θ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B : U @( Discr ) ] ->
  [ Θ |-( d ) tProd A B : U @( Discr ) ].
Proof.
  intros [[wfΘ ?] [wtA wdA]] [? [wtB wdB]].
  split.
  - constructor ; [ now trivial | split ].
    all: now trivial.
  - split.
    1-2: now constructor.
Qed.


Lemma wfTermLam {Θ d} {dT A B t} :
  [ Θ |-( dir_op dT ) A ] ->
  [ Θ ,, {| ty := A ; ty_dir := dir_op dT ; dir := Discr |} |-( d ) t : B @( dT ) ] ->
  [ Θ |-( d ) tLambda A t : tProd A B @( dT ) ].
Proof.
  intros [wfΘ [wtA wdA]] [[? [wtB wdB]] [wtt wdt]].
  split.
  - apply wfTypeProd. all: now constructor.
  - split. all: now constructor.
Qed.


Lemma wfTermApp {Θ d} {dT f a A B} :
  [ Θ |-( d ) f : tProd A B @( dT ) ] ->
  [ Θ |-( Discr ) a : A @( dir_op dT ) ] ->
  [ Θ |-( d ) tApp f a : B[a..] @( dT ) ].
Proof.
  intros [[wfΘ [wfProd wdProd]] [wtf wdf]] [[wfΘ' [wfA wdA]] [wta wda]].
  split.
  - constructor ; [ now trivial | split ].
    + admit.
    + (* will need substitution lemma *)
      admit.
  - split.
    + now econstructor.
    + now constructor.
Admitted.
