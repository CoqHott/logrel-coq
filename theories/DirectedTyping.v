(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations DirectedDirections DirectedContext DirectedDirectioning GenericTyping.

Set Primitive Projections.

Reserved Notation "[ |-( ) Γ ]" (at level 0, Γ at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ]" (at level 0, Γ, d, A at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t : A @( dA ) ]" (at level 0, Γ, dt, t, A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅ t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).
(* Reserved Notation "[ Γ |-( dt ) t ⤳* u ∈ A @( dA ) ]" (at level 0, Γ, dt, t, u, A, dA at level 50). *)


Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!GenericTypingProperties ta _ _ _ _ _ _ _ _ _ _}.

Record WfDirectedCtx (Θ: context) :=
  { wf_ctx: [ |- List.map ty Θ ]
  ; wf_ctx_dir: dir_ctx (List.map ty Θ) (List.map dir Θ) (List.map ty_dir Θ)
  }.
Notation "[ |-( ) Θ ]" := (WfDirectedCtx Θ).

Record WfType (Θ: context) (d: direction) (A: term) :=
  { wft: [ List.map ty Θ |- A ]
  ; wft_ctx_dir: dir_ctx (List.map ty Θ) (List.map dir Θ) (List.map ty_dir Θ)
  ; wft_dir: [ List.map dir Θ |- A ◃ d ]
  }.
Notation "[ Θ |-( d ) A ]" := (WfType Θ d A).

(* TODO: note that I prove rules using naming convention from DeclarativeTyping *)
Lemma wfTypeU {Θ d} : [ |-( ) Θ ] -> [ Θ |-( d ) U ].
Proof.
  intros [].
  constructor; tea.
  - now apply wft_U.
  - now apply dirU'.
Qed.

Lemma wfTypeProd {Γ d} {A B} :
  [ Γ |-( dir_op d ) A ] ->
  [Γ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B ] ->
  [ Γ |-( d ) tProd A B ].
Proof.
  intros [] [].
  constructor; tea.
  - now apply wft_prod.
  - now apply dirProd'.
Qed.

Record Typing (Θ: context) (dt: direction) (T: term) (dT: direction) (t: term) :=
  { wt: [ List.map ty Θ |- t : T ]
  ; wt_ctx_dir: dir_ctx (List.map ty Θ) (List.map dir Θ) (List.map ty_dir Θ)
  ; wt_dir: [ List.map dir Θ |- t ◃ dt ]
  ; wt_ty_dir: [ List.map dir Θ |- T ◃ dT ]
  }.
Notation "[ Γ |-( dt ) t : T @( dT ) ]" := (Typing Γ dt T dT t).

Lemma wfTypeUniv {Θ d} {A} :
  [ Θ |-( d ) A : U @( Discr ) ] ->
  [ Θ |-( d ) A ].
Proof.
  intros [].
  constructor; tea.
  now apply wft_term.
Qed.


Lemma in_ctx_erased {Θ n decl} :
  in_ctx Θ n decl -> Context.in_ctx (list_map ty Θ) n (ty decl).
Proof.
  induction 1; now constructor.
Qed.

Lemma in_ctx_nth_dir {Θ n decl} :
  in_ctx Θ n decl -> List.nth_error (list_map dir Θ) n = Some (dir decl).
Proof.
  induction 1; tea.
  reflexivity.
Qed.

Lemma in_ctx_nth_ty_dir {Θ n decl} :
  in_ctx Θ n decl -> List.nth_error (list_map ty_dir Θ) n = Some (ty_dir decl).
Proof.
  induction 1; tea.
  reflexivity.
Qed.

Lemma wfVar {Θ d'} {n d T dT} :
  [ |-( ) Θ ] ->
  in_ctx Θ n {| ty := T; ty_dir := dT; dir := d |} ->
  dir_leq d d' ->
  [ Θ |-( d' ) tRel n : T @( dT ) ].
Proof.
  intros [] inΘ leq.
  split; tea.
  - apply ty_var; tea.
    now apply (in_ctx_erased (decl := {| ty := T; ty_dir := dT; dir := d |})).
  - eapply dirVar'; tea.
    now apply (in_ctx_nth_dir (decl := {| ty := T; ty_dir := dT; dir := d |})).
  - eapply dir_ctx_nth_ty; tea.
    + now apply (in_ctx_erased (decl := {| ty := T; ty_dir := dT; dir := d |})).
    + now apply (in_ctx_nth_ty_dir (decl := {| ty := T; ty_dir := dT; dir := d |})).
Qed.

Lemma wfTermProd {Θ d} {A B} :
  [ Θ |-( dir_op d ) A : U @( Discr ) ] ->
  [ Θ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B : U @( Discr ) ] ->
  [ Θ |-( d ) tProd A B : U @( Discr ) ].
Proof.
  intros [] [].
  split; tea.
  - now apply ty_prod.
  - now apply dirProd'.
Qed.


Lemma wfTermLam {Θ d} {dT A B t} :
  [ Θ |-( dir_op dT ) A ] ->
  [ Θ ,, {| ty := A ; ty_dir := dir_op dT ; dir := Discr |} |-( d ) t : B @( dT ) ] ->
  [ Θ |-( d ) tLambda A t : tProd A B @( dT ) ].
Proof.
  intros [] [].
  split; tea.
  - now apply ty_lam.
  - now apply dirLam'.
  - now apply dirProd'.
Qed.

Lemma wfTermApp {Θ d} {dT f a A B} :
  [ Θ |-( d ) f : tProd A B @( dT ) ] ->
  [ Θ |-( Discr ) a : A @( dir_op dT ) ] ->
  [ Θ |-( d ) tApp f a : B[a..] @( dT ) ].
Proof.
  intros [? ? ? wdProd] [].
  split; tea.
  - now eapply ty_app.
  - now apply dirApp'.
  - apply dir_subst_Discr; tea.
    inversion wdProd; subst.
    inversion X; subst.
    econstructor; tea.
    etransitivity; tea.
    now eapply MaxDirProp.upper_bound2.
Qed.
