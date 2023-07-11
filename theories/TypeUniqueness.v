(** * LogRel.TypeUniqueness: all types for a term are convertible. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping
  BundledAlgorithmicTyping AlgorithmicTypingProperties.

Import DeclarativeTypingProperties AlgorithmicTypingData BundledTypingData AlgorithmicTypingProperties.

Lemma type_uniqueness Γ A A' t :
  [Γ |-[de] t : A] ->
  [Γ |-[de] t : A'] ->
  [Γ |-[de] A ≅ A'].
Proof.
  intros [?? Hinf]%algo_typing_complete [?? Hinf']%algo_typing_complete.
  eapply algo_typing_det in Hinf.
  2: eassumption.
  subst.
  etransitivity ; tea.
  now symmetry.
Qed.