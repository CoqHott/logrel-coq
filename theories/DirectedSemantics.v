
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping Weakening GenericTyping.

From LogRel Require Import DirectedDirections DirectedErasure.
From LogRel Require DirectedDeclarativeTyping DirectedContext.

Reserved Notation "[ Δ |- t -( d )- u : A ]" (at level 0, Δ, d, t, u, A at level 50).
Reserved Notation "[ Δ |- σ -( Θ )- τ ]" (at level 0, Δ, Θ, σ, τ at level 50).

Import DeclarativeTypingData.

Inductive TermRel (Δ: context) (t u: term) : direction -> term -> Type :=
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

Lemma TermRel_WellTyped_l {Δ t u d A} :
  [ Δ |- t -( d )- u : A ] -> [ Δ |- t : A ].
Proof.
Admitted.

Lemma TermRel_WellTyped_r {Δ t u d A} :
  [ Δ |- t -( d )- u : A ] -> [ Δ |- u : A ].
Proof.
Admitted.

Inductive SubstRel (Δ: context) :
  (nat -> term) -> (nat -> term) -> DirectedContext.context -> Type :=
| substRelSEmpty : forall σ τ, [ Δ |- σ -( nil )- τ ]
| substRelSConsDiscr : forall σ τ Θ d A,
    [ Δ |- (↑ >> σ) -( Θ )- (↑ >> τ) ] ->
    [ Δ |- A[↑ >> σ] ≅ A[↑ >> τ] ] ->
    [ Δ |- (σ var_zero) -( d )- (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- σ -( cons (d, A) Θ )- τ ]
| substRelSConsFun : forall σ τ Θ d A f,
    [ Δ |- (↑ >> σ) -( Θ )- (↑ >> τ) ] ->
    [ Δ |- f : arr A[↑ >> σ] A[↑ >> τ] ] ->
    [ Δ |- tApp f (σ var_zero) -( d )- (τ var_zero) : A[↑ >> τ] ] ->
    [ Δ |- σ -( cons (d, A) Θ )- τ ]
| substRelSConsCofun : forall σ τ Θ d A f,
    [ Δ |- (↑ >> σ) -( Θ )- (↑ >> τ) ] ->
    [ Δ |- f : arr A[↑ >> τ] A[↑ >> σ] ] ->
    [ Δ |- (σ var_zero) -( d )- tApp f (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- σ -( cons (d, A) Θ )- τ ]
where "[ Δ |- σ -( Θ )- τ ]" := (SubstRel Δ σ τ Θ).

Lemma TermRel_WellSubst_l {Δ σ τ Θ} :
  [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s σ : erase_dir Θ ].
Proof.
Admitted.


Lemma TermRel_WellSubst_r {Δ σ τ Θ} :
  [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s τ : erase_dir Θ ].
Proof.
Admitted.

Lemma DirectedFundamental {Δ σ τ Θ}:
  DirectedDeclarativeTyping.WfContextDecl Θ ->
  [ Δ |-s σ : erase_dir Θ ] ->
  [ Δ |-s τ : erase_dir Θ ] ->
  [ Δ |- σ -( Θ )- τ ] ->
  ∑ (tyDiscr: (forall A, DirectedDeclarativeTyping.WfTypeDecl Θ Discr A -> [ Δ |- A[σ] ≅ A[τ] ]))
    (tyFun: (forall A, DirectedDeclarativeTyping.WfTypeDecl Θ Fun A -> ∑ f: term, [ Δ |- f: arr A[σ] A[τ] ]))
    (tyCofun: (forall A, DirectedDeclarativeTyping.WfTypeDecl Θ Cofun A -> ∑ f: term, [ Δ |- f: arr A[τ] A[σ] ])),
  (forall d A u (wfA: DirectedDeclarativeTyping.WfTypeDecl Θ Discr A),
      DirectedDeclarativeTyping.TypingDecl Θ d A u ->
      [ Δ |- u[σ] -( d )- u[τ] : A[σ] ])
    ×
  (forall d A u (wfA: DirectedDeclarativeTyping.WfTypeDecl Θ Fun A),
      DirectedDeclarativeTyping.TypingDecl Θ d A u ->
      [ Δ |- tApp (tyFun _ wfA).π1 u[σ] -( d )- u[τ] : A[τ] ])
  ×
  (forall d A u (wfA: DirectedDeclarativeTyping.WfTypeDecl Θ Cofun A),
      DirectedDeclarativeTyping.TypingDecl Θ d A u ->
      [ Δ |- u[σ] -( d )- tApp (tyCofun _ wfA).π1 u[τ] : A[σ] ]).
Proof.
Admitted.
