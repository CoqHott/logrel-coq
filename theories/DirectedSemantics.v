
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedContext DirectedDirectioning DirectedDeclarativeTyping.
From LogRel Require Import Utils BasicAst.

Reserved Notation "[ Δ |- w : t -( d )- u : A ]" (at level 0, Δ, d, t, u, A, w at level 50).
Reserved Notation "[ Δ |- ϕ : σ -( )- τ : Θ ]" (at level 0, Δ, Θ, σ, τ, ϕ at level 50).

Definition err_term : term := tApp U U.

Definition action
  (δ: list direction)
  (dt: direction) (t: term) :
  [δ |- t ▹ dt] ->
  forall (σ τ: nat -> term), list term -> term.
Proof.
  induction 1 eqn: eq; intros σ τ l.
  - exact (tLambda U (tRel 0)).
  - exact (List.nth n l err_term).
  - remember d'' as dt. destruct d''.
    + pose (tA := IHd1 _ eq_refl σ τ l).
      pose (tB := IHd2 _ eq_refl
                    (scons (tApp tA⟨↑⟩ (tRel 0)) σ)
                    (scons (tRel 0) τ)
                    (cons err_term l)).
      exact (tLambda (tProd A B)[σ] (tLambda A[τ] (
                                         tApp tB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp tA⟨↑⟩⟨↑⟩ (tRel 0)))
            ))).
    + pose (tA := IHd1 _ eq_refl σ τ l).
      pose (tB := IHd2 _ eq_refl
                    (scons (tRel 0) σ)
                    (scons (tApp tA⟨↑⟩ (tRel 0)) τ)
                    (cons err_term l)).
      exact (tLambda (tProd A B)[τ] (tLambda A[σ] (
                                         tApp tB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp tA⟨↑⟩⟨↑⟩ (tRel 0)))
            ))).
    + exact err_term.
  - pose (tA := IHd1 _ eq_refl σ τ l).
    remember dA as d''. destruct d''.
    + pose (tt := IHd2 _ eq_refl
                    (scons (tRel 0) σ)
                    (scons (tApp tA⟨↑⟩ (tRel 0)) τ)
                    (cons err_term l)).
      exact (tLambda A[σ] (tLambda A[τ] tt⟨↑⟩)).
    + pose (tt := IHd2 _ eq_refl
                    (scons (tApp tA⟨↑⟩ (tRel 0)) σ)
                    (scons (tRel 0) τ)
                    (cons err_term l)).
      exact (tLambda A[σ] (tLambda A[τ] tt)⟨↑⟩).
    + pose (tt := IHd2 _ eq_refl
                    (scons (tRel 0) σ)
                    (scons (tRel 0) τ)
                    (cons err_term l)).
      exact (tLambda A[σ] (tLambda A[τ] tt⟨↑⟩)).
  - (* TODO: I think the direction of A is (dir_op dT) *)
    pose (tf := IHd1 _ eq_refl σ τ l).
    exact (tApp (tApp tf a[σ]) a[τ]).
Defined.

Definition compute_action (δ: list direction) (t: term) (σ τ: nat -> term) (ϕ: list term) : term :=
  match compute_DirInfer δ t with
  | None => err_term
  | Some (d; der) => action δ d t der σ τ ϕ
  end.




From LogRel Require Import Notations Context DeclarativeTyping DeclarativeInstance Weakening GenericTyping DeclarativeInstance.


Section MorphismDefinition.
  Context `{GenericTypingProperties}.

  Fixpoint termRelArr Δ t u A : term :=
    match A with
    | U => arr t u
    | tProd A B => tProd A (termRelArr (Δ ,, A) (eta_expand t) (eta_expand u) B)
    | _ => err_term
    end.
  
  Definition termRel Δ t u d (A : term) : Type :=
    match d with
    | Fun => ∑ f, [ Δ |- f : termRelArr Δ t u A ]
    | Cofun => ∑ f, [ Δ |- f : termRelArr Δ u t A ] 
    | Discr => [Δ |- t ≅ u]
    end.
  

  Inductive TermRel (Δ: Context.context) (t u: term) : forall (d: direction), term -> term -> Type :=
  | termRelFun { f } :
    [ Δ |- f : arr t u ] ->
    [ Δ |- f : t -( Fun )- u : U ]
  | termRelCofun { f } :
    [ Δ |- f : arr u t ] ->
    [ Δ |- f : t -( Cofun )- u : U ]
  | termRelDiscr { A } :
    [ Δ |- t ≅ u : A ] ->
    [ Δ |- err_term : t -( Discr )- u : A ]
  | termRelPiFun { A B w }:
    (* KM: I'm a bit skeptical that this typing premise should be needed.
        This relation should assume that the type is well-formed and comes with all the inversion lemmas needed *)
    [ Δ |- A ] ->
    [ Δ ,, A |- w : tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Fun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
    [ Δ |- tLambda A w : t -( Fun )- u : tProd A B ]
  | termRelPiCofun { A B w }:
    [ Δ |- A ] ->
    [ Δ ,, A |- w : tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Cofun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
    [ Δ |- tLambda A w : t -( Cofun )- u : tProd A B ]

  where "[ Δ |- w : t -( d )- u : A ]" := (TermRel Δ t u d A w).

  Context (type_act : forall (γ : list direction) (dA : direction) (A : term) (wdA : [γ |- A ◃ dA]) (σ τ : nat -> term) (φ : list term), term).

  (* Given a context of directions γ coming from Θ,
    substitutions, Δ |- σ, τ : |Θ|,
    a morphism Δ |- φ : σ ⇒ τ : Θ,
    a type |Θ| |- A, terms Δ |- t : A[σ], Δ |- u : A[τ],
    returns the adequate triple (t',u', A') by acting
    on t/u and substituting A according to the direction dA of A *)
  Definition dispatch_dir γ σ τ φ A dA wdA t u :=
    match dA with
    (* Discrete case, A[σ] ≅ A[τ], no transport needed *)
    | Discr => (t, u, A[σ])
    (* Fun case, A @ φ : A[σ] → A[τ] *)
    | Fun => (tApp (type_act γ dA A wdA σ τ φ) t, u, A[τ])
    (* Cofun case, A @ φ : A[τ] → A[σ] *)
    | Cofun => (t, tApp (type_act γ dA A wdA σ τ φ) u, A[σ])
    end.

  Inductive SubstRel (Δ: Context.context) :
    (nat -> term) -> (nat -> term) -> DirectedContext.context -> list term -> Type :=
  | substRelSEmpty : forall σ τ, [ Δ |- nil : σ -( )- τ : nil ]
  | substRelSCons {Θ σ τ φ A dA t u w d} (wdA : [dirs Θ |- A ◃ dA])
    (tuA := dispatch_dir (dirs Θ) σ τ φ A dA wdA t u) (t':= fst tuA) (u' := fst (snd tuA)) (A' := snd (snd tuA)):
    [ Δ |- φ : σ -( )- τ : Θ] ->
    [ Δ |- w : t' -( d )- u' : A' ] ->
    [ Δ |- (w :: φ) : (t .: σ) -( )- (u .: τ) : (Θ ,,  d \ A @ dA)]
  where "[ Δ |- ϕ : σ -( )- τ : Θ ]" := (SubstRel Δ σ τ Θ ϕ).

End MorphismDefinition.

(* (* TODO: reorganize files! *) *)
(* Section DirectedAction. *)

(*   Context {Δ} (wfΔ: [ |- Δ ]). *)

(*   Let Pctx θ := [ |-( ) θ ] -> unit. *)

(*   Let Pty Θ d A := forall (wfA : [ Θ |-( d ) A ]), *)
(*     forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] -> *)
(*       match d with *)
(*       | Fun => [ Δ |- wfty_action ϕ wfA : arr A[σ] A[τ] ] *)
(*       | Cofun => [ Δ |- wfty_action ϕ wfA : arr A[τ] A[σ] ] *)
(*       | Discr => [ Δ |- A[σ] ≅ A[τ] ] *)
(*       end. *)

(*   Let Ptm Θ dt A dA t := forall (wtt: [ Θ |-( dt ) t : A @( dA ) ]), *)
(*     forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] -> *)
(*       match dA with *)
(*       | Fun => ∑ (w: witType dt), [ Δ |- w : tApp (wtterm_action ϕ wtt) t[σ] -( dt )- t[τ] : A[τ] ] *)
(*       | Cofun => ∑ (w: witType dt), [ Δ |- w : t[σ] -( dt )- tApp (wtterm_action ϕ wtt) t[τ] : A[σ] ] *)
(*       | Discr => ∑ (w: witType dt), [ Δ |- w : t[σ] -( dt )- t[τ] : A[σ] ] *)
(*       end. *)

(*   Let Pconvty Θ d A B := [ Θ |-( d ) A ≅ B ] -> unit. *)

(*   Let Pconvtm Θ dt A dA t u := [ Θ |-( dt ) t ≅ u : A @( dA ) ] -> unit. *)

(*   Definition DirectedAction : *)
(*     DirectedDeclarativeTyping.WfDeclInductionConcl Pctx Pty Ptm Pconvty Pconvtm. *)
(*   Proof. *)
(*     eapply DirectedDeclarativeTyping.WfDeclInduction. *)
(*     all: revert Pctx Pty Ptm Pconvty Pconvtm; simpl. *)
(*     all: try (intros; exact tt). *)
(*     - (* wfTypeU *) *)
(*       intros Θ d wfΘ _ wfU σ τ l rel. *)
(*       have wfU' : [ Δ |- U ] by constructor. *)
(*       destruct d. *)
(*       1-3: repeat (constructor; tea). *)
(*     - (* wfTypeProd *) *)
(*       intros Θ d A B wfA IHA wfB IHB wfProd σ τ l rel. *)
(*       destruct d. *)
(*       + admit. *)
(*       + admit. *)
(*       + cbn in *. *)
(*         constructor. *)
(*         * eapply typing_subst; tea. *)
(*           now eapply typing_erased. *)
(*           admit. *)
(*         * now trivial. *)
(*         * admit. *)
(*     - (* wfTypeUniv *) *)
(*       intros Θ d A wtA IHA wfA σ τ l rel. *)
(*       pose (X := IHA wtA _ _ l rel). *)
(*       admit. *)
(*       (* destruct d. *) *)
(*       (* + inversion X. *) *)
(*       (*   eexists. eassumption. *) *)
(*       (* + inversion X. *) *)
(*       (*   eexists. eassumption. *) *)
(*       (* + inversion X. eapply convUniv. *) *)
(*       (*   exact H. *) *)
(*     - (* wfVar *) *)
(*       intros Θ d' n d A dA wfΘ _ inctx dleq wtRel σ τ l rel. *)
(*       admit. *)
(*     - (* wfTermProd *) *)
(*       intros Θ d A B wfA IHA wfB IHB wfProd σ τ rel. *)
(*       destruct d. *)
(*       + admit. *)
(*       + admit. *)
(*       + admit. *)
(*     - (* wfTermLam *) *)
(*       intros Θ dt dT A B t wfA IHA wfB IHB wtLam σ τ rel. *)
(*       destruct dT; simpl in *. *)
(*       + admit. *)
(*       + admit. *)
(*       + destruct dt. *)
(*         * constructor. *)
(*           { *)
(*             eapply typing_subst; tea. *)
(*             now eapply typing_erased. *)
(*             now eapply TermRel_WellSubst_l. *)
(*           } *)
(*           { admit. } *)
(*         * admit. *)
(*         * constructor. *)
(*           admit. *)
(*     - (* wfTermApp *) *)
(*       intros Θ d dA f a A B wtf IHf wta IHa wtApp σ τ rel. *)
(*       destruct dA. *)
(*       + cbn in *. admit. *)
(*       + admit. *)
(*       + cbn in *. admit. *)
(*     - (* wfTermConv *) *)
(*       admit. *)
(*   Abort. *)

(* End DirectedAction. *)
