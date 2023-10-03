
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedErasure DirectedDeclarativeTyping DirectedContext.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping DeclarativeInstance DeclarativeSubst Weakening GenericTyping.


Reserved Notation "[ Δ |- t -( d )- u : A ]" (at level 0, Δ, d, t, u, A at level 50).
Reserved Notation "[ Δ |- σ -( Θ )- τ ]" (at level 0, Δ, Θ, σ, τ at level 50).

Import DeclarativeTypingData.
Import DeclarativeTypingProperties.
Import Notations.

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
  [ Δ |- A ] ->
  [ Δ ,, A |- tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Fun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
  [ Δ |- t -( Fun )- u : tProd A B ]
| termRelPiCofun { A B }:
  [ Δ |- A ] ->
  [ Δ ,, A |- tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Cofun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
  [ Δ |- t -( Cofun )- u : tProd A B ]

where "[ Δ |- t -( d )- u : A ]" := (TermRel Δ t u d A).



(* Definition TermRel_actionType {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : *)
(*   match d with Fun | Cofun => term | Discr => unit end. *)
(* Proof. *)
(*   induction rel. *)
(*   - exact (arr t u). *)
(*   - exact (arr u t). *)
(*   - exact tt. *)
(*   - exact (tProd A IHrel). *)
(*   - exact (tProd A IHrel). *)
(* Defined. *)

(* Definition TermRel_action_concl {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : Type. *)
(* Proof. *)
(*   destruct d. *)
(*   - exact (∑(w: term), [ Δ |- w : TermRel_actionType rel ]). *)
(*   - exact (∑(w: term), [ Δ |- w : TermRel_actionType rel ]). *)
(*   - exact [ Δ |- t ≅ u : A ]. *)
(* Defined. *)

(* Definition TermRel_action {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : TermRel_action_concl rel. *)
(* Proof. *)
(*   depind rel; simpl. *)
(*   - exists f. assumption. *)
(*   - exists f. assumption. *)
(*   - assumption. *)
(*   - destruct IHrel as [v H]. *)
(*     exists (tLambda A v). now constructor. *)
(*   - destruct IHrel as [v H]. *)
(*     exists (tLambda A v). now constructor. *)
(* Defined. *)

(* Lemma TermRel_Fun_is_kind {Δ t u A} : *)
(*   [ Δ |- t -( Fun )- u : A ] -> DirectedDeclarativeTyping.is_kind A. *)
(* Proof. *)
(*   intro h. *)
(*   depind h. *)
(*   all: try inversion H. *)
(*   all: by cbn. *)
(* Qed. *)

(* Lemma TermRel_Cofun_is_kind {Δ t u A} : *)
(*   [ Δ |- t -( Cofun )- u : A ] -> DirectedDeclarativeTyping.is_kind A. *)
(* Proof. *)
(*   intro h. *)
(*   depind h. *)
(*   all: try inversion H. *)
(*   all: by cbn. *)
(* Qed. *)

Lemma TermRel_WellTyped {Δ t u d A} :
  [ Δ |- t -( d )- u : A ] -> [ Δ |- t : A ] × [ Δ |- u : A ].
Proof.
  induction 1.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Inductive SubstRel (Δ: context) :
  (nat -> term) -> (nat -> term) -> DirectedContext.context -> Type :=
| substRelSEmpty : forall σ τ, [ Δ |- σ -( nil )- τ ]
| substRelSConsDiscr : forall σ τ Θ d A,
    [ Δ |- (↑ >> σ) -( Θ )- (↑ >> τ) ] ->
    [ Δ |- A[↑ >> σ] ≅ A[↑ >> τ] ] ->
    [ Δ |- (σ var_zero) -( d )- (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- σ -( cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Discr;
                      DirectedContext.dir := d |} Θ )- τ ]
| substRelSConsFun : forall σ τ Θ d A f,
    [ Δ |- (↑ >> σ) -( Θ )- (↑ >> τ) ] ->
    [ Δ |- f : arr A[↑ >> σ] A[↑ >> τ] ] ->
    [ Δ |- tApp f (σ var_zero) -( d )- (τ var_zero) : A[↑ >> τ] ] ->
    [ Δ |- σ -( cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Fun ;
                      DirectedContext.dir := d |} Θ )- τ ]
| substRelSConsCofun : forall σ τ Θ d A f,
    [ Δ |- (↑ >> σ) -( Θ )- (↑ >> τ) ] ->
    [ Δ |- f : arr A[↑ >> τ] A[↑ >> σ] ] ->
    [ Δ |- (σ var_zero) -( d )- tApp f (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- σ -( cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Cofun ;
                      DirectedContext.dir := d |} Θ )- τ ]
where "[ Δ |- σ -( Θ )- τ ]" := (SubstRel Δ σ τ Θ).

Lemma TermRel_WellSubst_l {Δ σ τ Θ} :
  [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s σ : erase_dir Θ ].
Proof.
  induction 1.
  - constructor.
  - constructor; tea.
    unshelve eapply (fst (TermRel_WellTyped _)).
    3: eassumption.
  - constructor; tea.
    admit.
  - admit.
Admitted.


Lemma TermRel_WellSubst_r {Δ σ τ Θ} :
  [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s τ : erase_dir Θ ].
Proof.
Admitted.

Section DirectedAction.

  Context {Δ} (wfΔ: [ |- Δ ]).

  Let Pctx θ := [ |-() θ ] -> unit.

  Let Pty Θ d A := [ Θ |-( d ) A ] ->
    forall (σ τ: nat -> term), [ Δ |- σ -( Θ )- τ ] ->
      match d with
      | Fun => ∑ (w: term), [ Δ |- w : arr A[σ] A[τ] ]
      | Cofun => ∑ (w: term), [ Δ |- w : arr A[τ] A[σ] ]
      | Discr => [ Δ |- A[σ] ≅ A[τ] ]
      end.

  Let Ptm Θ dt A dA t := [ Θ |-( dt ) t : A @ dA ] ->
    forall (σ τ: nat -> term), [ Δ |- σ -( Θ )- τ ] ->
      match dA with
      | Fun => ∑ (f: term), [Δ |- f : arr A[σ] A[τ] ] × [ Δ |- tApp f t[σ] -( dt )- t[τ] : A[τ] ]
      | Cofun => ∑ (f: term), [Δ |- f : arr A[τ] A[σ] ] × [ Δ |- t[σ] -( dt )- tApp f t[τ] : A[σ] ]
      | Discr => [ Δ |- t[σ] -( dt )- t[τ] : A[σ] ]
      end.

  Let Pconvty Θ d A B := [ Θ |-( d ) A ≅ B ] -> unit.

  Let Pconvtm Θ dt A dA t u := [ Θ |-( dt ) t ≅ u : A @ dA ] -> unit.

  Definition DirectedAction :
    DirectedDeclarativeTyping.WfDeclInductionConcl Pctx Pty Ptm Pconvty Pconvtm.
  Proof.
    eapply DirectedDeclarativeTyping.WfDeclInduction.
    all: revert Pctx Pty Ptm Pconvty Pconvtm; simpl.
    all: try (intros; exact tt).
    - (* wfTypeU *)
      intros Θ d wfΘ _ wfU σ τ rel.
      destruct d.
      (* 1-2: exists (idterm U); now apply ty_id'. *)
      1-2: admit.
      constructor. now constructor.
    - (* wfTypeProd *)
      intros Θ d A B wfA IHA wfB IHB wfProd σ τ rel.
      destruct d.
      + admit.
      + admit.
      + cbn in *.
        constructor.
        * eapply typing_subst; tea.
          now eapply typing_erased.
          now eapply TermRel_WellSubst_l.
        * now trivial.
        * admit.
    - (* wfTypeUniv *)
      intros Θ d A wtA IHA wfA σ τ rel.
      pose (X := IHA wtA _ _ rel).
      destruct d.
      + inversion X.
        eexists. eassumption.
      + inversion X.
        eexists. eassumption.
      + inversion X. eapply convUniv.
        exact H.
    - (* wfVar *)
      intros Θ d' n d A dA wfΘ _ inctx dleq σ τ rel.
      admit.
    - (* wfTermProd *)
      intros Θ d A B wfA IHA wfB IHB wfProd σ τ rel.
      destruct d.
      + admit.
      + admit.
      + admit.
    - (* wfTermLam *)
      intros Θ dt dT A B t wfA IHA wfB IHB wtLam σ τ rel.
      destruct dT; simpl in *.
      + admit.
      + admit.
      + destruct dt.
        * constructor.
          {
            eapply typing_subst; tea.
            now eapply typing_erased.
            now eapply TermRel_WellSubst_l.
          }
          { admit. }
        * admit.
        * constructor.
          admit.
    - (* wfTermApp *)
      intros Θ d dA f a A B wtf IHf wta IHa wtApp σ τ rel.
      destruct dA.
      + cbn in *. admit.
      + admit.
      + cbn in *. admit.
    - (* wfTermConv *)
      admit.
  Abort.

End DirectedAction.
