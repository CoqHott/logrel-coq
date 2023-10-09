
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedErasure DirectedDeclarativeTyping DirectedContext DirectedSemantics.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping DeclarativeInstance DeclarativeSubst Weakening GenericTyping.

From PartialFun Require Import Monad PartialFun.


Import DeclarativeTypingData.
Import DeclarativeTypingProperties.
Import Notations.

Import MonadNotations.
Set Universe Polymorphism.
Import IndexedDefinitions.
Import StdInstance.

(* Variant action_s_state := *)
(*   | term_state *)
(*   | ctx_state. *)

(* Definition action_s_input (s: action_s_state) := *)
(*   match s with *)
(*   | term_state => DirectedContext.context × term *)
(*   | ctx_state => DirectedContext.context *)
(*   end. *)

(* Definition action_s_output (s: action_s_state) := *)
(*   match s with *)
(*   | term_state => term *)
(*   | ctx_state => list (option term) *)
(*   end. *)

(* Equations action_s : ∇ (arg: ∑ (s: action_s_state), action_s_input s), action_s_output (arg.π1) := *)
(*   action_s (term_state; (c, t)) := *)
(*     l ← rec (ctx_state; c) ;; *)
(*     undefined ; *)
(*   action_s (ctx_state; nil) := ret nil ; *)
(*   action_s (ctx_state; cons A ctx) := undefined. *)

(* NOTE: no need to handle lambda, because we only look at types in whnf *)
Equations type_action (γ : witList) : term ⇀ term :=
  type_action γ (tSort s) := ret (tLambda (tSort s) (tRel 0)) ;
  type_action γ (tProd A B) := tB ← rec B ;; ret (tLambda A tB) ;
  type_action γ (tRel n) := match List.nth n γ (Discr; tt) with
                        | (Fun; t) => ret t
                        | (Cofun; t) => ret t
                        | (Distr; tt) => undefined
                        end ;
  type_action γ (tApp f a) := tf ← rec f ;; ret (tApp tf a) ;
  type_action γ _ := undefined.

Definition type_action_domain {Θ d A γ} : [ Θ |-( d ) A ] -> domain (type_action γ) A.
  intro wfA.
  (* funelim (type_action γ A). *)
Admitted.

Definition wfty_action {Θ d A} (ϕ: witList) (wfA: [ Θ |-( d ) A ]) : term :=
  def (type_action ϕ) A (type_action_domain wfA).

Definition wtterm_action {Θ d A t dA} (ϕ: witList) (wft: [Θ |-( d ) t : A @( dA ) ]) : term.
Proof.
  assert (wfA : [ Θ |-( dA ) A ]) by admit.
  exact (wfty_action ϕ wfA).
Admitted.


Section DirectedAction.

  Context {Δ} (wfΔ: [ |- Δ ]).

  Let Pctx θ := [ |-( ) θ ] -> unit.

  Let Pty Θ d A := forall (wfA : [ Θ |-( d ) A ]),
    forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] ->
      match d with
      | Fun => [ Δ |- wfty_action ϕ wfA : arr A[σ] A[τ] ]
      | Cofun => [ Δ |- wfty_action ϕ wfA : arr A[τ] A[σ] ]
      | Discr => [ Δ |- A[σ] ≅ A[τ] ]
      end.

  Let Ptm Θ dt A dA t := forall (wtt: [ Θ |-( dt ) t : A @( dA ) ]),
    forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] ->
      match dA with
      | Fun => ∑ (w: witType dt), [ Δ |- w : tApp (wtterm_action ϕ wtt) t[σ] -( dt )- t[τ] : A[τ] ]
      | Cofun => ∑ (w: witType dt), [ Δ |- w : t[σ] -( dt )- tApp (wtterm_action ϕ wtt) t[τ] : A[σ] ]
      | Discr => ∑ (w: witType dt), [ Δ |- w : t[σ] -( dt )- t[τ] : A[σ] ]
      end.

  Let Pconvty Θ d A B := [ Θ |-( d ) A ≅ B ] -> unit.

  Let Pconvtm Θ dt A dA t u := [ Θ |-( dt ) t ≅ u : A @( dA ) ] -> unit.

  Definition DirectedAction :
    DirectedDeclarativeTyping.WfDeclInductionConcl Pctx Pty Ptm Pconvty Pconvtm.
  Proof.
    eapply DirectedDeclarativeTyping.WfDeclInduction.
    all: revert Pctx Pty Ptm Pconvty Pconvtm; simpl.
    all: try (intros; exact tt).
    - (* wfTypeU *)
      intros Θ d wfΘ _ wfU σ τ l rel.
      have wfU' : [ Δ |- U ] by constructor.
      destruct d.
      1-3: repeat (constructor; tea).
    - (* wfTypeProd *)
      intros Θ d A B wfA IHA wfB IHB wfProd σ τ l rel.
      destruct d.
      + admit.
      + admit.
      + cbn in *.
        constructor.
        * eapply typing_subst; tea.
          now eapply typing_erased.
          admit.
        * now trivial.
        * admit.
    - (* wfTypeUniv *)
      intros Θ d A wtA IHA wfA σ τ l rel.
      pose (X := IHA wtA _ _ l rel).
      admit.
      (* destruct d. *)
      (* + inversion X. *)
      (*   eexists. eassumption. *)
      (* + inversion X. *)
      (*   eexists. eassumption. *)
      (* + inversion X. eapply convUniv. *)
      (*   exact H. *)
    - (* wfVar *)
      intros Θ d' n d A dA wfΘ _ inctx dleq wtRel σ τ l rel.
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
