From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction
  GenericTyping DeclarativeTyping Generation Reduction AlgorithmicTyping LogRelConsequences BundledAlgorithmicTyping.

Import AlgorithmicTypingData BundledTypingData DeclarativeTypingProperties.

Section AlgoConvConv.

  Lemma in_ctx_conv Γ' Γ n decl :
  [|-[de] Γ' ≅ Γ] ->
  in_ctx Γ n decl ->
  ∑ decl', (in_ctx Γ' n decl') × ([Γ' |-[de] decl'.(decl_type) ≅ decl.(decl_type)]).
  Proof.
  intros Hconv Hin.
  induction Hin in Γ', Hconv |- *.
  all: inversion Hconv ; subst ; clear Hconv.
  1: eexists ; split.
  - now econstructor.
  - cbn.
    eapply typing_shift ; tea.
    all: eapply validity in H3 as [].
    all: gen_typing.
  - destruct d as [? d].
    edestruct IHHin as [[? d'] []].
    1: eassumption.
    cbn in *.
    econstructor ; split.
    1: now econstructor.
    cbn.
    eapply typing_shift ; tea.
    all: now eapply validity in H3 as [] ; gen_typing.
  Qed.

  Let PTyEq (Γ : context) (A B : term) := True.
  Let PTyRedEq (Γ : context) (A B : term) := True.
  Let PNeEq (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    (∑ T, [Γ |-[de] t : T]) ->
    (∑ T, [Γ |-[de] u : T]) ->
    ∑ A', [Γ' |-[al] t ~ u ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    (∑ T, [Γ |-[de] t : T]) ->
    (∑ T, [Γ |-[de] u : T]) ->
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], [Γ' |-[de] A' ≅ A] & isType A'].
  Let PTmEq (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ |-[de] t : A] -> [Γ |-[de] u : A ] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] -> isType A' ->
    [Γ |-[de] t : A] -> [Γ |-[de] u : A ] ->
    [Γ' |-[al] t ≅h u : A'].

  Let PTyEq' (Γ : context) (A B : term) := True.
  Let PTyRedEq' (Γ : context) (A B : term) := True.
  Let PNeEq' (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [Γ' |-[al] t ~ u ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq' (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], [Γ' |-[de] A' ≅ A] & isType A'].
  Let PTmEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] -> isType A' ->
    [Γ' |-[al] t ≅h u : A'].

  Theorem algo_conv_conv :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    enough (BundledConvInductionConcl PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq') as Hind.
    all: subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
    {
      unfold BundledConvInductionConcl, AlgoConvInductionConcl in *.
      unshelve (repeat (split ; [destruct Hind as [Hind _] ; shelve | destruct Hind as [_ Hind]])).
      1-2: now constructor.
      all: intros * Hconv ; intros ; eapply Hind ; tea.
      all: match goal with H : ConvCtx _ _ |- _ => symmetry in H ; apply wf_conv_ctx in H end.
      all: split ; tea.
      all: try solve [now apply algo_conv_wh in Hconv as []].
      all: now eapply validity in H2.
    }
    apply BundledConvInduction ; cbn in *.
    all: try solve [now constructor].
    - intros * HΓ ? _ _ ? ?.
      eapply in_ctx_conv in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      eassumption.
    - intros * ? IHm Ht IHt ? ? ? ? HΓ.
      edestruct IHm as [[? [? HconvP]] ?]; tea.
      eapply red_ty_compl_prod_r in HconvP as (?&?&?&[HconvP HconvA]).
      eapply redty_red, red_whnf in HconvP as ->.
      2: gen_typing.
      destruct IHt as [IHt IHt'].
      specialize (IHt _ _ HΓ HconvA).
      eexists ; split.
      1: now econstructor.
      eapply typing_subst1 ; tea.
      econstructor.
      eapply stability ; tea.
      now eapply validity in IHt' as [].
    - intros * ? IHm ; intros.
      edestruct IHm as [[A'' [IHm' ?]] [Hconvm]]; tea.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'.
      {
        symmetry.
        etransitivity ; tea.
        eapply RedConvTyC, subject_reduction_type ; tea.
        eapply validity in Hconvm as [].
        now eapply stability. 
      }
      pose proof (HconvA'' := HconvA').
      eapply red_ty_complete in HconvA'' as [? []]; tea.
      eexists ; split.
      + econstructor ; tea.
        now eapply redty_red.
      + symmetry ; etransitivity ; tea.
        now eapply RedConvTyC.
      + gen_typing. 
    - intros * ? ? ? Ht IH ? ? ? ? A'' ? HconvA; intros.
      pose proof Ht as Ht'.
      eapply algo_conv_wh in Ht' as [? ? HwhA].
      assert [Γ' |-[de] A' ≅ A''] as HconvA'.
      {
        etransitivity ; tea.
        symmetry.
        eapply RedConvTyC, subject_reduction_type ; tea.
        now apply validity in HconvA.
      }
      pose proof (HconvA'' := HconvA').
      eapply red_ty_complete in HconvA'' as [? []]; tea.
      econstructor ; tea.
      1: now eapply redty_red.
      eapply IH ; tea.
      etransitivity ; tea.
      now eapply RedConvTyC.
    - intros * ? IHA ? IHB ? ? ? * ? HconvU ?.
      symmetry in HconvU.
      eapply red_ty_compl_univ_r, redty_red, red_whnf in HconvU as ->.
      2: gen_typing.
      destruct IHA as [IHA HconvA].
      econstructor ; fold_algo.
      + eapply IHA ; tea.
        do 2 econstructor.
        now eapply wf_conv_ctx.
      + eapply IHB ; tea.
        all: econstructor ; tea.
        1: econstructor ; fold_decl.
        2: do 2 econstructor ; fold_decl.
        2: now eapply wf_conv_ctx.
        all: eapply stability ; tea.
        all: econstructor.
        all: now eapply validity in HconvA as [].
    - intros * ? ? ? IHf ? ? ? * ? HconvP ?.
      symmetry in HconvP ; eapply red_ty_compl_prod_r in HconvP as (?&?&?&[HconvP]).
      eapply redty_red, red_whnf in HconvP as ->.
      2:gen_typing.
      econstructor ; fold_algo ; tea.
      eapply IHf.
      + econstructor ; tea.
        now symmetry.
      + symmetry.
        eapply stability ; tea.
        econstructor.
        2: now symmetry.
        now eapply ctx_conv_refl, wf_conv_ctx.
    - intros * ? IHm ? ? ? ? * ? HconvN HtyA'.
      edestruct IHm as [[? []] ?] ; tea.
      econstructor ; fold_algo ; tea.
      unshelve eapply ty_conv_inj in HconvN.
      1: now constructor.
      1: assumption.
      cbn in HconvN.
      destruct HtyA'.
      1-2: easy.
      assumption.
  Qed.

End AlgoConvConv.

Section TermTypeConv.

  Let PTyEq (Γ : context) (A B : term) := True.
  Let PNeEq (Γ : context) (A t u : term) := True.
  Let PTmEq (Γ : context) (A t u : term) :=
      [A ⇒* U] ->
      [Γ |-[al] t ≅ u].
  Let PTmRedEq (Γ : context) (A t u : term) := 
    A = U ->
    [Γ |-[al] t ≅h u].

  Theorem algo_conv_tm_ty :
  AlgoConvInductionConcl PTyEq PTyEq PNeEq PNeEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PNeEq PTmEq PTmRedEq.
    apply AlgoConvInduction.
    all: try solve [now constructor].
    - intros * ? ? ? Hconv IH ?.
      econstructor ; tea.
      eapply IH, whred_det ; tea.
      2: gen_typing.
      eapply algo_conv_wh in Hconv as [].
      now gen_typing.
    - intros * ? IHA ? IHB _.
      now econstructor ; fold_algo.
    - intros.
      congruence.
    - intros * ? ? Hne ->.
      inversion Hne.
  Qed.
  
End TermTypeConv.

Section Symmetry.

  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅ A].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅h A].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    ∑ A', [Δ |-[al] u ~ t ▹ A'] × [Δ |-[de] A ≅ A'].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    ∑ A', [Δ |-[al] u ~h t ▹ A'] × [Δ |-[de] A ≅ A'].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ≅ t : A].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ≅h t : A].

  Theorem algo_conv_sym :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction.
    - intros.
      econstructor ; fold_algo.
      all: intuition eauto.
    - intros * ? IHA ? IHB ; intros.
      econstructor ; fold_algo.
      1: now intuition eauto.
      eapply IHB.
      econstructor ; tea.
      eapply IHA.
    - now econstructor.
    - intros * ? IHM ; intros.
      edestruct IHM as [[U' [IHM' HconvM]] []] ; tea.
      assert (U' = U) as ->.
      {
        symmetry in HconvM.
        eapply red_ty_compl_univ_r, redty_red in HconvM.
        eapply whred_det ; tea.
        + apply algo_conv_wh in IHM' as []. gen_typing.
        + gen_typing.
        + reflexivity.
      }
      now econstructor.
    - intros * HΓ ; intros.
      eapply in_ctx_conv in HΓ as [? []].
      2: now symmetry.
      eexists ; split.
      1: now econstructor.
      now symmetry.
    - intros * ? IHm ? [IHt Hwft] ; intros.
      edestruct IHm as [[? [IHm' Hconv]] []] ; tea ; clear IHm.
      eapply red_ty_compl_prod_l in Hconv as (?&?&?&[Hred]).
      eapply redty_red, whred_det in Hred.
      4: reflexivity.
      3: gen_typing.
      2: now eapply algo_conv_wh in IHm' as [] ; gen_typing.
      subst.
      eexists ; split.
      + econstructor ; fold_algo.
        1: eassumption.
        eapply algo_conv_conv.
        * now eapply IHt.
        * now eapply ctx_conv_refl, wf_conv_ctx ; symmetry.
        * now symmetry.
        * eapply stability.
          2: now symmetry.
          now eapply validity in Hwft as [].
        * eapply stability.
        2: now symmetry.
        now eapply validity in Hwft as [].
      + eapply typing_subst1 ; tea.
        eapply TermConv ; fold_decl.
        2: now symmetry.
        eapply stability ; tea.
        now symmetry.
    - intros * ? IHm ; intros.
      edestruct IHm as [[A'' [IHm' Hconv]] [Hwf]] ; tea ; clear IHm.
      assert [Δ |-[de] A' ≅ A''] as Hconv'.
      {
        etransitivity ; tea.
        symmetry.
        eapply RedConvTyC, subject_reduction_type ; tea.
        eapply stability.
        2: now symmetry.
        now eapply validity in Hwf as [].
      }
      pose proof Hconv' as Hconv''.
      eapply red_ty_complete in Hconv'' as [? []]; tea.
      eexists ; split.
      + econstructor ; tea.
        now eapply redty_red.
      + etransitivity ; tea.
        now eapply RedConvTyC.
    - intros.
      econstructor ; fold_algo.
      all: intuition eauto.
    - intros * ? IHA ? IHB ; intros.
      econstructor ; fold_algo.
      1: now eapply IHA.
      eapply IHB.
      econstructor ; tea.
      now econstructor ; intuition eauto.
    - intros * ? ? ? IH ? Hf ; intros.
      econstructor ; fold_algo.
      1-2: assumption.
      eapply IH.
      econstructor ; tea.
      eapply validity, prod_ty_inv in Hf as [].
      now econstructor.
    - intros * ? IH ; intros.
      edestruct IH as [[? []] []] ; tea.
      now econstructor.
  Qed.
  
End Symmetry.
  
Section Transitivity.

  Let PTyEq (Γ : context) (A B : term) := forall Δ C,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅ C] ->
    [Γ |-[al] A ≅ C].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ C,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅h C] ->
    [Γ |-[al] A ≅h C].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ v A',
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ~ v ▹ A'] ->
    [Γ |-[al] t ~ v ▹ A] × [Γ |-[de] A ≅ A'].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ~h v ▹ A'] ->
    [Γ |-[al] t ~h v ▹ A] × [Γ |-[de] A ≅ A'].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Γ |-[de] A' ≅ A] ->
    [Δ |-[al] u ≅ v : A'] ->
    [Γ |-[al] t ≅ v : A].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Γ |-[de] A' ≅ A] ->
    [Δ |-[al] u ≅h v : A'] ->
    [Γ |-[al] t ≅h v : A].

  Theorem algo_conv_trans :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction.
    - intros ? ? ? ? B' ? ? Hconv IH ? ? ? * ? Hconv'.
      inversion Hconv' ; subst ; clear Hconv'.
      assert (A'0 = B') as ->.
      {
        eapply whred_det ; tea.
        - eapply algo_conv_wh in H7 as [] ; gen_typing.
        - eapply algo_conv_wh in Hconv as [] ; gen_typing. 
      }
      econstructor ; tea.
      eapply IH ; tea.
    - intros * ? IHA ? IHB ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{
        apply algo_conv_wh in H5 as [e _].
        now inversion e.
        }
        econstructor ; fold_algo.
        + eapply IHA ; tea.
        + eapply IHB ; tea.
          econstructor ; tea.
          eapply conv_sound in H ; tea.
          all: now eapply prod_ty_inv.
    - intros * ? ? _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{ apply algo_conv_wh in H2 as [e _]. now inversion e. }
      now constructor.
    - intros * ? IH ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      1-2: apply algo_conv_wh in H as [_ e] ; now inversion e.
      econstructor ; fold_algo.
      now eapply IH.
    - intros * ? ? _ _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      split.
      + now econstructor.
      + eapply in_ctx_conv in H5 as [? [Hin ]]; tea.
        now eapply in_ctx_inj in Hin as ->.
    - intros * ? IHm Ht IHt ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      eapply IHm in H8 as [? HconvP] ; tea.
      eapply prod_ty_inj in HconvP as [].
      split.
      + econstructor ; fold_algo ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        eapply TermConv ; fold_decl.
        1: now eapply IHt.
        now symmetry.
    - intros * ? IH ? ? ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      edestruct IH as [[? HconvA] ?] ; tea.
      split.
      1: now econstructor.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; now eapply validity in HconvA. 
      eassumption.
    - intros * ? ? ? Ht IHt ? ? ? * ? HconvA Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      assert (t'0 = u') as ->.
      {
        eapply whred_det ; tea.
        1: now eapply algo_conv_wh in H9 as [].
        now eapply algo_conv_wh in Ht as [].
      }
      econstructor ; tea ; fold_algo.
      eapply IHt ; tea. 
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; now eapply validity in HconvA.
      eassumption.
    - intros * ? [IHA HpostA] ? IHB ? ? ? * HΓ ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      2: now inversion H5 ; inversion H8.
      2: now inversion H5.
      econstructor ; fold_algo.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor ; fold_decl.
        * now symmetry in HΓ ; eapply wf_conv_ctx in HΓ.
        * econstructor ; fold_decl.
          now eapply validity in HpostA as [].
    - intros * ? ? ? IH ? ? ? * ? ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      1:{ unshelve eapply ty_conv_inj in H6. 1-2: econstructor. now cbn in *. }
      2:{ unshelve eapply ty_conv_inj in H6. 1-2: now econstructor. now cbn in H6. }
      eapply prod_ty_inj in H6 as [].
      econstructor ; tea.
      eapply IH ; tea.
      now econstructor.
    - intros * ? IH ? ? ? ? * ? ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; fold_algo.
      1-2: now unshelve eapply ty_conv_inj in H5 ; [now econstructor | now econstructor | cbn in *].
      econstructor ; fold_algo ; tea.
      now eapply IH.
  Qed.

End Transitivity.

Module AlgorithmicTypingProperties.
  Include AlgorithmicTypingData.

  #[local] Ltac intros_bn :=
    intros ;
    repeat match goal with | H : context [bn] |- _ => destruct H end ;
    econstructor ; try assumption.

  #[export, refine] Instance WfCtxAlgProperties : WfContextProperties (ta := bn) := {}.
  Proof.
    all: intros_bn.
    - now do 2 constructor.
    - constructor ; tea.
      now apply typing_sound.
  Qed.

  #[export, refine] Instance WfTypeAlgProperties : WfTypeProperties (ta := bn) := {}.
  Proof.
    all: intros_bn.
    2-4: now econstructor.
    - now eapply algo_typing_wk.
  Qed.

  #[export, refine] Instance InferringAlgProperties : InferringProperties (ta := bn) := {}.
  Proof.
    all: intros_bn.
    2-5: now econstructor.
    - now eapply algo_typing_wk.
  Qed.

  #[export, refine] Instance InferringRedProperties :
  InferringRedProperties (ta := bn) := {}.
  Proof.
    all: intros_bn.
    - now eapply algo_typing_wk.
    - now econstructor.
  Qed. 

  #[export, refine] Instance TypingAlgProperties : TypingProperties (ta := bn) := {}.
  Proof.
    1-2: intros_bn.
    - gen_typing.
    - now eapply algo_typing_wk.
    - now econstructor.
    - intros * [? ? [? ? ? ? ? Hc]] [].
      destruct Hc.
      econstructor ; tea.
      econstructor ; fold_algo ; tea.
      econstructor ; fold_algo.
      2: etransitivity.
      all: eassumption.
    - intros * [? ? Hc] HA.
      destruct Hc as [? ? ? ? Ht Hc] ; fold_algo.
      econstructor ; tea.
      1: now destruct HA.
      econstructor ; fold_algo ; tea.
      eapply algo_conv_trans.
      + split ; tea.
        now eapply typing_sound, validity in Ht.
      + now eapply ctx_conv_refl.
      + eapply HA.
  Qed.

  #[export, refine] Instance ConvTypeAlgProperties : ConvTypeProperties (ta := bn) := {}.
  Proof.
    2: split.
    - intros_bn.
      1-2: now constructor.
      now eapply algo_conv_tm_ty.
    - red ; intros_bn.
      eapply algo_conv_sym.
      + now econstructor.
      + now eapply ctx_conv_refl. 
    - red ; intros * Hconv [? ? ? Hconv'].
      econstructor ; tea.
      1: now apply Hconv.
      eapply algo_conv_trans ; tea.
      now eapply ctx_conv_refl.
    - intros_bn.
      1-2: now apply typing_wk.
      now apply algo_conv_wk.
    - intros_bn.
      inversion bun_conv_ty ; subst ; clear bun_conv_ty.
      econstructor ; fold_algo.
      1-2: now etransitivity.
      eassumption.
    - intros_bn.
      1-2: now econstructor.
      do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea ; fold_decl.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_conv_refl.
        * symmetry.
          now eapply conv_sound in bun_conv_ty0.
      + now do 2 econstructor.
  Qed.

  #[export, refine] Instance ConvTermAlgProperties : ConvTermProperties (ta := bn) := {}.
  Proof.
    1: split.
    - red ; intros_bn.
      eapply algo_conv_sym.
      + now econstructor.
      + now eapply ctx_conv_refl. 
    - red. intros * Hconv [? ? ? Hconv'].
      split ; tea.
      1: apply Hconv.
      eapply algo_conv_trans ; tea.
      + now apply ctx_conv_refl.
      + now constructor.
    - intros_bn.
      all: eapply conv_sound in bun_conv_ty ; tea.
      1-2: now econstructor.
      eapply algo_conv_conv ; tea.
      now apply ctx_conv_refl.
    - intros_bn.
      1-3: now apply typing_wk.
      now apply algo_conv_wk.
    - intros_bn.
      + eapply subject_reduction_type, RedConvTyC in bun_red_ty ; tea.
        symmetry in bun_red_ty.
        now gen_typing.
      + eapply subject_reduction_type, RedConvTyC in bun_red_ty ; tea.
        symmetry in bun_red_ty.
        now gen_typing.
      + inversion bun_conv_tm ; subst ; clear bun_conv_tm.
        econstructor.
        1-3: now etransitivity.
        eassumption.
    - intros Γ n n' A [? ? ? ? ? A' Hconvn HconvA].
      assert [Γ |-[de] A]
        by now eapply validity in HconvA as [].
      assert [Γ |-[de] n : A'] by
        (eapply conv_sound in Hconvn as [[]%validity] ; tea ; now gen_typing).
      assert [Γ |-[de] n' : A'] by
        (eapply conv_sound in Hconvn as [[]%validity] ; tea ; now gen_typing).
      split ; tea.
      1-2: now gen_typing.
      eapply algo_conv_conv ; tea.
      2: now eapply ctx_conv_refl.
      apply ne_conv_conv.
      2: eassumption.
      now eapply validity in HconvA as [].
    - intros_bn.
      + now constructor.
      + constructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now apply ctx_conv_refl.
        eapply conv_sound in bun_conv_tm0 ; tea.
        symmetry.
        now constructor.
      + now do 2 econstructor.
    - intros_bn.
      + now eapply typing_sound in bun_chk0.
      + now eapply typing_sound in bun_chk.
      + econstructor.
        1-3: reflexivity.
        now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuAlgProperties : ConvNeuProperties (ta := bn) := {}.
  Proof.
    1: split.
    - intros ? ? [].
      assert ([Γ |-[bn] x ~ y ▹ bun_conv_ne_conv_ty]) as Hconv.
      {
        now econstructor.
      }
      eapply algo_conv_sym in Hconv as [? []].
      2: now eapply ctx_conv_refl.
      econstructor ; tea.
      etransitivity ; tea.
      now symmetry.
    - red. intros_bn.
      + eapply algo_conv_trans ; tea.
        * now constructor.
        * now apply ctx_conv_refl.
      + eassumption.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      now eapply conv_sound in bun_conv_ty.
    - intros_bn.
      + destruct bun_conv_ne_conv_l.
        eexists.
        gen_typing.
      + now apply whne_ren.
      + destruct bun_conv_ne_conv_r.
        eexists.
        gen_typing.
      + now apply whne_ren.
      + now apply algo_conv_wk.
      + now apply typing_wk.
    - intros * [? ? Hty].
      inversion Hty ; subst ; clear Hty.
      inversion H ; subst ; clear H  ; fold_algo.
      econstructor.
      + assumption.
      + eexists. now econstructor.
      + gen_typing.
      + eexists. now econstructor.
      + gen_typing.
      + now econstructor ; fold_algo.
      + eapply conv_sound in H0 ; tea.
        enough [Γ |-[de] tRel n : decl_type decl] as Hty by
          now apply validity in Hty.
        now econstructor.
  - intros *
    [? ? ? ? ? ? Hf (?&?&?&[])%red_ty_compl_prod_r]
    [? ? ? ? Ht].
    econstructor ; tea.
    + eapply conv_sound in Hf as [Hf] ; tea.
      eapply validity in Hf as [_ Hf _].
      eexists ; econstructor ; fold_decl.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + gen_typing.
    + eapply conv_sound in Hf as [Hg] ; tea.
      eapply validity in Hg as [_ _ Hg].
      eexists ; econstructor ; fold_decl.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + gen_typing.
    + econstructor ; fold_algo.
      * econstructor ; tea.
        2: econstructor.
        now eapply redty_red.
      * eapply algo_conv_conv ; tea.
        now eapply ctx_conv_refl.
    + eapply typing_subst1 ; tea.
      econstructor.
      eapply conv_sound, validity in Ht as [] ; tea.
  Qed.

  #[export, refine] Instance RedTermAlgProperties :
    RedTermProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      1: now apply typing_wk.
      now apply credalg_wk.
    - now intros * [].
    - intros_bn.
      2: now do 2 econstructor.
      econstructor ; [econstructor|..] ; fold_decl.
      all: now eapply typing_sound.
    - intros_bn.
      + econstructor ; tea.
        now eapply typing_sound.
      + clear -bun_red_tm.
        induction bun_red_tm ; econstructor.
        2: eassumption.
        now econstructor.
    - intros_bn.
      eapply conv_sound in bun_conv_ty ; tea.
      now gen_typing.
    - intros_bn.
      1: now eapply typing_sound.
      econstructor.
    - red. intros_bn.
      now etransitivity.
  Qed.

  #[export, refine] Instance RedTypeAlgProperties :
    RedTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      1: now apply typing_wk.
      now apply credalg_wk.
    - now intros * [].
    - intros_bn.
      now econstructor.
    - intros_bn.
      1: now eapply typing_sound.
      econstructor.
    - red. intros_bn.
      now etransitivity.
  Qed.

  #[export] Instance AlgorithmicTypingProperties : GenericTypingProperties bn _ _ _ _ _ _ _ _ _ _ := {}.

End AlgorithmicTypingProperties.