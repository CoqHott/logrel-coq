(** * LogRel.Decidability: type-checking is decidable. *)
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import AlgorithmicTyping BundledAlgorithmicTyping AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness Completeness Termination.
From PartialFun Require Import Monad PartialFun.

Import AlgorithmicTypingData DeclarativeTypingProperties.
Import IndexedDefinitions.

#[local]Existing Instance ty_errors.

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.
  
Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Obligation Tactic := idtac.

Equations check (Γ : context) (t T : term) (hΓ : [|- Γ]) (hT : [Γ |- T]) :
  [Γ |- t : T] + ~[Γ |- t : T] :=

check Γ t T hΓ hT with (inspect (def typing (check_state;Γ;T;t) _)) :=
  {
    | ok _ eqn: e => inl _
    | error _ eqn: e => inr _
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

Print Assumptions check.