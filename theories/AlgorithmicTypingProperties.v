From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction
  GenericTyping DeclarativeTyping Generation DeclarativeInstance AlgorithmicTyping LogRelConsequences BundledAlgorithmicTyping AlgorithmicConvProperties.
From LogRel Require Import LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape.
From LogRel.Substitution Require Import Properties.

Import DeclarativeTypingProperties AlgorithmicTypingData BundledTypingData BundledIntermediateData IntermediateTypingProperties.

Lemma algo_conv_complete Γ A B :
  [Γ |-[de] A ≅ B] ->
  [Γ |-[al] A ≅ B].
Proof.
  intros Hconv.
  enough [Γ |-[bni] A ≅ B] as [] by easy.
  eapply Fundamental in Hconv as [HΓ [HA HAext] _ [Hconv]].
  cbn in *.
  clear HAext.
  pose proof (soundCtxId HΓ) as [? Hsubst].
  set (HA' := HA _ _ _ Hsubst).
  specialize (Hconv _ _ _ Hsubst).
  fold HA' in Hconv.
  destruct HA' as [[] HA'] ; cbn in *.
  repeat rewrite instId'_term in *.
  now eapply escapeEq.
Qed.

Module AlgorithmicTypingProperties.
  Export BundledTypingData AlgorithmicConvProperties.

  #[local] Ltac intros_bn :=
    intros ;
    repeat match goal with | H : context [bn] |- _ => destruct H end ;
    econstructor ; try assumption.

  #[export, refine] Instance WfCtxAlgProperties : WfContextProperties (ta := bn) := {}.
  Proof.
    1-8: intros_bn.
    - now do 2 constructor.
    - constructor ; tea.
      now apply typing_sound.
    - now intros ? []. 
  Qed.

  #[export, refine] Instance WfTypeAlgProperties : WfTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      now eapply algo_typing_wk.
    - now intros * [? ?%typing_sound]. 
    - intros_bn.
      now econstructor.
    - intros_bn.
      now econstructor.
    - intros_bn.
      do 2 econstructor ; tea.
      now apply algo_conv_complete.
  Qed.

  #[export, refine] Instance TypingAlgProperties : TypingProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      + now eapply algo_typing_wk.
      + gen_typing.
    - intros * [?? ?%typing_sound] ; tea.
      now econstructor.
    - intros_bn.
      + now econstructor.
      + constructor.
        now eapply in_ctx_wf.
    - intros_bn.
      + do 2 econstructor ; tea.
        all: now eapply (redty_red (ta := de)), red_ty_compl_univ_r.
      + now do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        2: econstructor.
        all: boundary.
    - intros * [? ? ? (?&?&?&[])%red_ty_compl_prod_r] [].
      esplit ; tea.
      + do 2 econstructor ; tea.
        1: now eapply (redty_red (ta := de)).
        eapply algo_conv_complete.
        now etransitivity.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      symmetry.
      now eapply RedConvTyC, subject_reduction_type.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      now eapply conv_sound in bun_conv_ty.
  Qed.

  #[export] Instance AlgorithmicTypingProperties : GenericTypingProperties bn _ _ _ _ _ _ _ _ _ := {}.

End AlgorithmicTypingProperties.