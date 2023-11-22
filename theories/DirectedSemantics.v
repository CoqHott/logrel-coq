
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedContext DirectedDirectioning DirectedMorphisms DirectedDeclarativeTyping.
From LogRel Require Import Utils BasicAst Notations GenericTyping.

(* TODO: reorganize files! *)
Section DirectedValid.

  Context `{GenericTypingProperties}.
  Context {Δ} (wfΔ: [ |- Δ ]).

  Let Pctx θ := [ |-( ) θ ] -> unit.

  Let Pty Θ d A := forall (wfA : [ Θ |-( d ) A ]),
    forall (σ τ: nat -> term) ϕ,
      [ Δ |- ϕ : σ -( )- τ : Θ ] ->
      match d with
      | Fun => [ Δ |- compute_action (dirs Θ) A σ τ ϕ : arr A[σ] A[τ] ]
      | Cofun => [ Δ |- compute_action (dirs Θ) A σ τ ϕ : arr A[τ] A[σ] ]
      | Discr => [ Δ |- A[σ] ≅ A[τ] ]
      end.

  Let Ptm Θ dt A dA t := forall (wtt: [ Θ |-( dt ) t : A @( dA ) ]),
    forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] ->
    (let '(u,v,A) :=
      dispatchDir (dirs Θ) σ τ ϕ A dA t[σ] t[τ]
    in termRelPred Δ u v dt A (compute_action (dirs Θ) t σ τ ϕ)).

  Let Pconvty Θ d A B := [ Θ |-( d ) A ≅ B ] ->
    forall (σ τ: nat -> term) ϕ,
      [ Δ |- ϕ : σ -( )- τ : Θ ] ->
      match d with
      | Fun => [ Δ |- compute_action (dirs Θ) A σ τ ϕ ≅ compute_action (dirs Θ) B σ τ ϕ : arr A[σ] A[τ] ]
      | Cofun => [ Δ |- compute_action (dirs Θ) A σ τ ϕ ≅ compute_action (dirs Θ) B σ τ ϕ : arr A[τ] A[σ] ]
      | Discr => unit
      end.

  Let Pconvtm Θ dt A dA t u := [ Θ |-( dt ) t ≅ u : A @( dA ) ] -> unit. (* TODO *)

  Definition DirectedAction :
    DirectedDeclarativeTyping.WfDeclInductionConcl Pctx Pty Ptm Pconvty Pconvtm.
  Proof.
    eapply DirectedDeclarativeTyping.WfDeclInduction.
    all: revert Pctx Pty Ptm Pconvty Pconvtm; simpl.
    all: try (intros; exact tt).
    - (* wfTypeU *)
      intros Θ d wfΘ _ wfU σ τ l rel.
      cbn.
      (* TODO: for reflexivity, look at generic consequences or something, there is a type class for this *)
      (* WAIT in this case its not needed, you have it for every constructors *)
      destruct d.
      1-3: admit.
    - (* wfTypeProd *)
      intros Θ A dA B dB d wfA IHA wfB IHB maxd wfProd σ τ ϕ rel.
      destruct d.
      + admit.
      + admit.
      + admit.
        (* constructor. *)
(*         * eapply typing_subst; tea. *)
(*           now eapply typing_erased. *)
(*           admit. *)
(*         * now trivial. *)
(*         * admit. *)
    - (* wfTypeUniv *)
      admit.
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
    - (* wfVar *)
      intros Θ d' n d A dA wfΘ IHΘ inctx dleq wtRel σ τ ϕ rel.
      (* maybe will need something on the context in the induction *)
      admit.
(*       admit. *)
    - (* wfTermProd *)
      admit.
(*       intros Θ d A B wfA IHA wfB IHB wfProd σ τ rel. *)
(*       destruct d. *)
(*       + admit. *)
(*       + admit. *)
(*       + admit. *)
    - (* wfTermLam *)
      admit.
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
    - (* wfTermApp *)
      admit.
(*       intros Θ d dA f a A B wtf IHf wta IHa wtApp σ τ rel. *)
(*       destruct dA. *)
(*       + cbn in *. admit. *)
(*       + admit. *)
(*       + cbn in *. admit. *)
    - (* wfTermConv *)
      admit.
  Abort.

End DirectedValid.
