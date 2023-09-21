
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping Weakening.

From LogRel Require Import Directions.
From LogRel Require DirectedDeclarativeTyping.

Reserved Notation "[ Γ |- t -( d )- u : A ]" (at level 0, Γ, d, t, u, A at level 50).

Import DeclarativeTypingData.

Inductive TermRel (Δ: Context.context) (t u: term) : direction -> term -> Type :=
| termRelFun { f } :
  [ Δ |- f : arr t u ] ->
  [ Δ |- t -( Fun )- u : U ]
| termRelCofun { f } :
  [ Δ |- f : arr u t ] ->
  [ Δ |- t -( Cofun )- u : U ]
| termRelDiscr { A } :
  [ Δ |- t ≅ u : A ] ->
  [ Δ |- t -( Discr )- u : A ]
| termRelPiFun { A B }:
  [ Δ ,, A |- tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Fun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
  [ Δ |- t -( Fun )- u : tProd A B ]
| termRelPiCofun { A B }:
  [ Δ ,, A |- tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Cofun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
  [ Δ |- t -( Cofun )- u : tProd A B ]

where "[ Δ |- t -( d )- u : A ]" := (TermRel Δ t u d A).

From Equations Require Import Equations.

Lemma TermRel_Fun_is_kind {Δ t u A} :
  [ Δ |- t -( Fun )- u : A ] -> DirectedDeclarativeTyping.is_kind A.
Proof.
  intro h.
  depind h.
  all: try inversion H.
  all: by cbn.
Qed.

Lemma TermRel_Cofun_is_kind {Δ t u A} :
  [ Δ |- t -( Cofun )- u : A ] -> DirectedDeclarativeTyping.is_kind A.
Proof.
  intro h.
  depind h.
  all: try inversion H.
  all: by cbn.
Qed.
