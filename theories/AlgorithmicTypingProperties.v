(** * LogRel.AlgorithmicTypingProperties: properties of algorithmic typing. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping DeclarativeSubst TypeConstructorsInj BundledAlgorithmicTyping AlgorithmicConvProperties.
From LogRel Require Import LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape.
From LogRel.Substitution Require Import Properties Escape.

Import DeclarativeTypingProperties AlgorithmicTypingData BundledTypingData.

(** ** Small types are large types *)

(** In the generic instance we allow to turn any small type into a type,
while in the definition of algorithmic typing we only allow it when A is a non-canonical
type (in which case it has to be small).
So we need to show admissibility of the more general rule. *)

Lemma algo_typing_small_large Γ A :
  [Γ |-[bn] A : U] ->
  [Γ |-[bn] A].
Proof.
  enough (BundledTypingInductionConcl
    (fun _ _ => True)
    (fun Γ A t => [Γ |-[de] A ≅ U] -> [Γ |-[al] t])
    (fun Γ A t => A = U -> [Γ |-[al] t])
    (fun _ _ _ => True)) as (?&?&H&?).
  {
    intros [].
    split ; tea.
    eapply H.
    2: reflexivity.
    do 2 (econstructor ; tea).
    now eapply redty_red, red_ty_compl_univ_r.
  }
  eapply BundledTypingInduction.
  all: try solve [econstructor].
  - intros.
    econstructor.
    + intros Hcan ; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - intros.
    prod_hyp_splitter.
    now econstructor.
  - intros * ????? Hconv.
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now econstructor.
    now cbn in Hconv.
  - intros.
    econstructor.
    + intros Hcan ; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - intros * ? Hconv.
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now econstructor.
    now cbn in Hconv.
  - intros * ??? Hconv.
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now econstructor.
    now cbn in Hconv.
  - intros.
    econstructor.
    + intros Hcan ; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - intros.
    econstructor.
    + intros Hcan ; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - intros * ? [IH] **; subst.
    eapply IH.
    eapply subject_reduction_type ; tea.
    boundary.
Qed.

Import BundledIntermediateData IntermediateTypingProperties.

(** ** Instance *)
(** Equipped with the equivalence of declarative and algorithmic conversion,
we easily derive our third instance. *)

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
      now apply algo_typing_sound.
    - now intros ? [].
  Qed.

  #[export, refine] Instance WfTypeAlgProperties : WfTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      now eapply algo_typing_wk.
    - now intros * [? ?%algo_typing_sound]. 
    - intros_bn.
      now econstructor.
    - intros_bn.
      now econstructor.
    - intros_bn.
      now econstructor.
    - intros_bn.
      now econstructor.
    - intros.
      now eapply algo_typing_small_large.
  Qed.

  #[export, refine] Instance TypingAlgProperties : TypingProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      + now eapply algo_typing_wk.
      + gen_typing.
    - intros * [?? ?%algo_typing_sound] ; tea.
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
    - intros * [? ? ? (?&?&[])%red_ty_compl_prod_r] [].
      esplit ; tea.
      + do 2 econstructor ; tea.
        1: now eapply (redty_red (ta := de)).
        eapply algo_conv_complete.
        now etransitivity.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros_bn.
      1: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      1: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      + do 2 econstructor ; tea.
        now eapply (redty_red (ta := de)), red_ty_compl_nat_r.
      + now do 2 econstructor.
    - intros_bn.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply (redty_red (ta := de)), red_ty_compl_nat_r.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor.
        eapply typing_subst1.
        1: eauto using inf_conv_decl.
        now eapply algo_typing_sound.
    - intros_bn.
      1: econstructor.
      gen_typing.
    - intros_bn.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply (redty_red (ta := de)), red_ty_compl_empty_r.
      + econstructor.
        eapply typing_subst1.
        1: eauto using inf_conv_decl.
        now eapply algo_typing_sound.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      symmetry.
      eapply RedConvTyC, subject_reduction_type ; tea.
      now eapply algo_typing_sound.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
  Qed.

  #[export, refine] Instance RedTermAlgProperties :
    RedTermProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      2: now apply credalg_wk.
      econstructor ; tea.
      1: now eapply algo_typing_wk.
      now eapply typing_wk.
    - intros * [? []]; assumption.
    - now intros * [].
    - intros_bn. 2: econstructor; [|reflexivity].
      all: econstructor ; tea.
      + econstructor.
        1: now do 2 econstructor.
        econstructor ; tea.
        now eapply algo_conv_complete.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros * HP Hz Hs.
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor ; tea.
        1: econstructor.
        now do 2 econstructor.
      + econstructor; [|reflexivity]; now constructor.
    - intros * HP Hz Hs [].
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor.
        * eassumption.
        * do 2 econstructor ; tea.
          now eapply (redty_red (ta := de)), red_ty_compl_nat_r.
        * now do 2 econstructor.
      + econstructor; [|reflexivity]; now constructor.
    - intros_bn.
      + eapply red_ty_compl_prod_r in bun_inf_conv_conv0 as (?&?&[]).
        econstructor ; tea.
        1: econstructor.
        * econstructor ; tea.
          now eapply (redty_red (ta := de)).
        * econstructor ; tea.
          eapply algo_conv_complete.
          now etransitivity.
        * eapply typing_subst1 ; tea.
          econstructor.
          now eapply inf_conv_decl.  
      + clear -bun_red_tm.
        induction bun_red_tm ; econstructor.
        2: eassumption.
        now econstructor.
    - intros * [] [] [] [] [] ?.
      assert [Γ |-[al] n ▹h tNat].
      {
        econstructor ; tea.
        now eapply (redty_red (ta := de)), red_ty_compl_nat_r.
      }
      split ; tea.
      1: econstructor ; tea.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor ; tea.
        now eapply algo_conv_complete.
      + econstructor.
        eapply typing_subst1.
        all: eapply algo_typing_sound ; tea.
        2: now econstructor.
        econstructor ; tea.
        now eapply algo_conv_complete.
      + clear -bun_red_tm.
        induction bun_red_tm.
        1: now constructor.
        econstructor ; tea.
        now econstructor. 
    - intros * [] [] [] ?.
      assert [Γ |-[al] n ▹h tEmpty].
      {
        econstructor ; tea.
        now eapply (redty_red (ta := de)), red_ty_compl_empty_r.
      }
      split ; tea.
      1: econstructor ; tea.
      1: econstructor ; tea.
      + econstructor.
        eapply typing_subst1.
        all: eapply algo_typing_sound ; tea.
        2: now econstructor.
        econstructor ; tea.
        now eapply algo_conv_complete.
      + clear -bun_red_tm.
        induction bun_red_tm.
        1: now constructor.
        econstructor ; tea.
        now econstructor. 
    - intros_bn.
      eapply algo_conv_sound in bun_conv_ty ; tea.
      econstructor ; tea.
      now etransitivity.
    - intros_bn.
      all: now econstructor.
    - red. intros_bn.
      2: now etransitivity.
      now econstructor.
  Qed.

  #[export, refine] Instance RedTypeAlgProperties :
    RedTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      1: now apply algo_typing_wk.
      now apply credalg_wk.
    - intros * []; assumption.
    - now intros_bn.
    - intros * [?[]%algo_typing_small_large].
      now econstructor.
    - intros_bn.
      now econstructor. 
    - red. intros_bn.
      now etransitivity.
  Qed.

  Export UntypedValues.WeakValuesProperties.

  #[export] Instance AlgorithmicTypingProperties : GenericTypingProperties bn _ _ _ _ _ _ _ _ _ _ _ _ _ _ := {}.

End AlgorithmicTypingProperties.

(** ** Consequences *)

Import AlgorithmicTypingProperties.

(** *** Completeness of algorithmic typing *)

Corollary algo_typing_complete Γ A t :
  [Γ |-[de] t : A] ->
  [Γ |-[bn] t : A].
Proof.
  now intros [_ _ ?%escapeTm]%(Fundamental (ta := bn)).
Qed.

(** *** Uniqueness of types *)

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