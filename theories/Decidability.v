(** * LogRel.Decidability: type-checking is decidable. *)
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms TypeConstructorsInj.
From LogRel Require Import AlgorithmicTyping BundledAlgorithmicTyping AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness Completeness Termination.
From PartialFun Require Import Monad PartialFun.

Import AlgorithmicTypingData DeclarativeTypingProperties.
Import IndexedDefinitions.

#[local]Existing Instance ty_errors.

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.
  
Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).

Obligation Tactic := try easy.

Equations check_ty (Γ : context) (T : term) (hΓ : [|- Γ]) :
  [Γ |- T] + ~[Γ |- T] :=

check_ty Γ T hΓ with (inspect (def typing (wf_ty_state;Γ;tt;T) _)) :=
  {
    | ok _ eq: e => inl _
    | error _ eq: e => inr _
  }.
Next Obligation.
  intros.
  apply typing_terminates ; tea.
  now cbn.
Qed.
Next Obligation.
  intros.
  apply bn_alg_typing_sound.
  set (Hter := check_ty_obligations_obligation_1 _ _ _) in *.
  clearbody Hter.
  pose proof (def_graph_sound _ _ Hter) as Hgraph.
  rewrite e in Hgraph.
  apply implem_typing_sound in Hgraph ; cbn in Hgraph.
  now constructor.
Qed.
Next Obligation.
  intros * e Hty ; cbn in *.
  set (Hter := check_ty_obligations_obligation_1 _ _ _) in *.
  clearbody Hter.
  pose proof (def_graph_sound _ _ Hter) as Hgraph.
  enough (graph typing (wf_ty_state;Γ;tt;T) (ok tt)).
  {
    eapply orec_graph_functional in Hgraph ; tea.
    assert (ok tt = error e0) by (etransitivity ; eassumption).
    now congruence.
  }
  eapply algo_wfty_complete in Hty as [].
  apply typing_complete.
  constructor ; tea.
Qed.

Equations check_ctx (Γ : context) : [|- Γ] + ~[|- Γ] :=
  check_ctx ε := inl _ ;
  check_ctx (Γ,,A) with (check_ctx Γ) := {
    | inr _ := inr _ ;
    | inl hΓ with (check_ty Γ A hΓ) := {
      | inr _ := inr _ ;
      | inl _ := inl _ ;
    }
  }.
Next Obligation.
  now constructor.
Qed.
Next Obligation.
  now constructor.
Qed.
Next Obligation.
  intros ? ** hΓ'.
  now inversion hΓ'.
Qed.
Next Obligation.
  intros ? ** hΓ'.
  now inversion hΓ'.
Qed.




Equations check (Γ : context) (T t : term) (hΓ : [|- Γ]) (hT : [Γ |- T]) :
  [Γ |- t : T] + ~[Γ |- t : T] :=

check Γ T t hΓ hT with (inspect (def typing (check_state;Γ;T;t) _)) :=
  {
    | ok _ eq: e => inl _
    | error _ eq: e => inr _
  }.
Next Obligation.
  intros.
  now apply typing_terminates.
Qed.
Next Obligation.
  intros.
  apply bn_alg_typing_sound.
  set (Hter := check_obligations_obligation_1 _ _ _ _ _) in *.
  clearbody Hter.
  pose proof (def_graph_sound _ _ Hter) as Hgraph.
  rewrite e in Hgraph.
  apply implem_typing_sound in Hgraph ; cbn in Hgraph.
  now constructor.
Qed.
Next Obligation.
  intros * e Hty ; cbn in *.
  set (Hter := check_obligations_obligation_1 _ _ _ _ _) in *.
  clearbody Hter.
  pose proof (def_graph_sound _ _ Hter) as Hgraph.
  enough (graph typing (check_state;Γ;T;t) (ok tt)).
  {
    eapply orec_graph_functional in Hgraph ; tea.
    assert (ok tt = error e0) by (etransitivity ; eassumption).
    now congruence.
  }
  eapply algo_typing_complete in Hty as [].
  apply typing_complete.
  constructor ; tea.
  econstructor ; tea.
  now eapply algo_conv_complete.
Qed.

Equations check_full (Γ : context) (T t : term) :
  [Γ |- t : T] + ~[Γ |- t : T] :=

  check_full Γ T t with (check_ctx Γ) :=
  {
    | inr _ := inr _ ;
    | inl hΓ with (check_ty Γ T hΓ) := {
      | inr _ := inr _ ;
      | inl hT with (check Γ T t hΓ hT) := {
        | inr _ := inr _ ;
        | inl _ := inl _ ;
      }
    }
  }.
Next Obligation.
  intros ** ?.
  eauto with boundary.
Qed.
Next Obligation.
  intros ** ?.
  eauto with boundary.
Qed.

Print Assumptions check_full.

Definition check_conv (Γ : context) (T t t' : term) (hΓ : [|- Γ]) (hT : [Γ |- T]) (ht : [Γ |- t : T]) (ht' : [Γ |- t' : T]) :
  [Γ |- t ≅ t' : T] + ~[Γ |- t ≅ t' : T].
Proof.
  assert (hdom : domain conv (tm_state; Γ; T; t; t')).
  1: now eapply conv_terminates.
  pose (x := (def conv (tm_state;Γ;T;t;t') hdom)).
  destruct x as [|] eqn:e; [left| right]; cbn in *.
  all: pose proof (def_graph_sound _ _ hdom) as Hgraph.
  - unfold x in e; rewrite e in Hgraph.
    apply implem_conv_sound in Hgraph ; cbn in Hgraph.
    now eapply algo_conv_sound in Hgraph.
  - intros Hty.
    enough (graph conv (tm_state;Γ;T;t;t') (ok tt)).
    {
      eapply orec_graph_functional in Hgraph ; tea.
      pose proof (eq_trans Hgraph e) as [=].
    }
    eapply algo_convtm_complete in Hty; inversion Hty; subst.
    apply implem_conv_complete.
    now constructor.
Qed.
