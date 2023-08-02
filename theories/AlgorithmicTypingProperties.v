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
  - intros * ? [] ? [] **.
    econstructor; eauto.
  - intros * ????? ???? hconv.
    unshelve eapply ty_conv_inj in hconv.
    1,2: constructor.
    cbn in hconv; destruct hconv.
  - intros * ??? hconv.
    econstructor.
    + intros Hcan; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - intros * ??? hconv.
    econstructor.
    + intros Hcan; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - intros * ? [ih] **.
    econstructor; eauto.
  - intros * ? [_ ] ? hconv.
    unshelve eapply ty_conv_inj in hconv.
    1,2: constructor.
    destruct hconv.
  - intros * ? [_ ] ????? hconv.
    unshelve eapply ty_conv_inj in hconv.
    1,2: constructor.
    destruct hconv.
  - econstructor.
    + intros Hcan; inversion Hcan.
    + econstructor.
      1: now econstructor.
      now eapply redty_red, red_ty_compl_univ_r.
  - econstructor.
    + intros Hcan; inversion Hcan.
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
  Qed.

  #[export, refine] Instance WfTypeAlgProperties : WfTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      now eapply algo_typing_wk.
    - intros_bn.
      now econstructor.
    - intros_bn.
      now econstructor.
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
      1: do 2 econstructor; tea.
      1,2: now eapply (redty_red (ta:=de)), red_ty_compl_univ_r.
      gen_typing.
    - intros_bn.
      1: do 2 (econstructor; tea); now eapply algo_conv_complete.
      econstructor.
      2,3: eapply TypeRefl; refold.
      1,2: boundary.
      now eapply algo_typing_sound.
    - intros * [].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_ty_compl_sig_r .
      econstructor; tea.
      do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
    - intros * [].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_ty_compl_sig_r .
      econstructor; tea.
      1: do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
      eapply typing_subst1; [|now symmetry].
      eapply TermConv; refold; [|now symmetry].
      econstructor. eapply TermRefl.
      now eapply inf_conv_decl.
    - intros * [??? hconv].
      pose proof hconv as h%red_ty_compl_univ_r.
      econstructor.
      2: econstructor; econstructor; tea; apply h.
      all: gen_typing.
    - intros * tyA.
      pose proof tyA as ?%bn_alg_typing_sound.
      destruct tyA; econstructor; tea.
      1: now econstructor.
      now do 2 econstructor.
    - intros * tyA [] [].
      pose proof tyA as ?%bn_alg_typing_sound.
      destruct tyA; econstructor.
      1: tea.
      1: econstructor; tea; econstructor; tea; now eapply algo_conv_complete.
      now do 2 econstructor.
    - intros * [] tyB [] [].
      pose proof tyB as ?%bn_alg_typing_sound.
      destruct tyB; econstructor.
      1: tea.
      1: econstructor; tea; econstructor; tea; now eapply algo_conv_complete.
      now do 2 econstructor.
    - intros_bn.
      + econstructor ; tea.
        * econstructor ; tea.
          now eapply algo_conv_complete.
        * econstructor ; tea.
          now eapply algo_conv_complete.
        * econstructor ; tea.
          now eapply algo_conv_complete.
      + econstructor.
        eapply typing_subst1.
        1: now eapply algo_typing_sound in bun_inf_conv_inf.
        eapply stability1 ; tea.
        1-2: boundary.
        now apply algo_typing_sound. 
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
    - intros_bn.
      2: apply redalg_one_step; now constructor.
      econstructor ; tea.
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
      + apply redalg_one_step ; now constructor.
    - intros * HP Hz Hs [].
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor.
        * eassumption.
        * do 2 econstructor ; tea.
          now eapply (redty_red (ta := de)), red_ty_compl_nat_r.
        * now do 2 econstructor.
      + apply redalg_one_step; now constructor.
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
      + now apply redalg_app.
    - intros * [] [] [] [? []].
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
      + now apply redalg_natElim.
    - intros * [] [?[]].
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
      + now apply redalg_natEmpty.
    - intros_bn.
      2: econstructor; [|reflexivity]; now constructor.
      econstructor.
      1: tea.
      2: eapply TypeRefl; refold; now boundary.
      do 2 econstructor.
      1: do 2 (econstructor; tea); now eapply algo_conv_complete.
      reflexivity.
    - intros * [? []].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_ty_compl_sig_r.
      econstructor; tea.
      2: now apply redalg_fst.
      econstructor; tea.
      do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
    - intros_bn.
      2: econstructor; [|reflexivity]; now constructor.
      econstructor.
      1: tea.
      (* 2: eapply TypeRefl; refold; now boundary. *)
      + do 2 econstructor.
        2: reflexivity.
        do 2 (econstructor; tea); now eapply algo_conv_complete.
      + eapply TypeRefl; eapply typing_subst1.
        2: now eapply algo_typing_sound.
        do 2 econstructor.
        * boundary.
        * now eapply algo_typing_sound.
        * now eapply inf_conv_decl.
        * now eapply inf_conv_decl.
    - intros * [? []].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_ty_compl_sig_r.
      econstructor; tea.
      2: now apply redalg_snd.
      econstructor; tea.
      do 2 econstructor; tea; now eapply (redty_red (ta:=de)).
      eapply typing_subst1.
      2: now symmetry.
      eapply TermRefl; eapply wfTermConv; refold; [|now symmetry].
      econstructor; now eapply inf_conv_decl.
    - intros * tyA tyB tyf []; econstructor; tea.
      2: now eapply redalg_map.
      now eapply ty_map.
    - intros * tyA ????; econstructor.
      1: now destruct tyA.
      2: eapply redalg_one_step; now econstructor.
      eapply ty_map; tea; eapply ty_conv.
      1: now eapply ty_nil.
      eapply convty_list; now symmetry.
    - intros * tyA ??????; econstructor.
      1: now destruct tyA.
      2: eapply redalg_one_step; econstructor.
      eapply ty_map; tea; eapply ty_conv.
      1: eapply ty_cons; tea; eapply ty_conv; tea.
      1,2: eapply convty_list; tea; now symmetry.
    - intros * tyA **.
      pose proof tyA as ?%bn_alg_typing_sound.
      econstructor.
      1: boundary.
      2: eapply redalg_one_step ; now econstructor.
      eapply ty_map ; tea.
      eapply ty_conv.
      1: eapply ty_map ; tea.
      eapply convty_list.
      now symmetry.
    - intros * tyA tyP tynil tycons **.
      split.
      1: now destruct tyA.
      2: eapply redalg_one_step; now econstructor.
      eapply ty_listElim ; tea.
      eapply ty_conv.
      1: now eapply ty_nil.
      symmetry.
      now eapply convty_list.
    - intros * tyA tyP tynil tycons **.
      split.
      1: now destruct tyA.
      2: eapply redalg_one_step; now econstructor.
      eapply ty_listElim ; tea.
      eapply ty_conv.
      1: now eapply ty_cons.
      symmetry.
      now eapply convty_list.
    - intros * tyA tyP tynil tycons [].
      split.
      1: now destruct tyA.
      2: now eapply redalg_listElim.
      now eapply ty_listElim.
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

  #[export] Instance AlgorithmicTypingProperties : GenericTypingProperties bn _ _ _ _ _ _ _ _ _ _ _ := {}.

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

Lemma conv_equiv_de_bn Γ A B :
  [Γ |-[de] A ≅ B] <~> [Γ |-[bn] A ≅ B].
Proof.
  split.
  + now intros [??? ?%escapeEq]%(Fundamental (ta:=bn)).
  + now intros [??? h%algo_conv_sound].
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