From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction
  GenericTyping DeclarativeTyping Generation Reduction AlgorithmicTyping LogRelConsequences McBrideDiscipline.

Import AlgorithmicTypingData DeclarativeTypingProperties.

Section AlgoStability.
  
  Let PTy (Γ : context) (A : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[al] A].
  Let PInf (Γ : context) (A t : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [Γ' |-[al] t ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PInfRed (Γ : context) (A t : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [Γ' |-[al] t ▹h A'] × [Γ' |-[de] A' ≅ A].
  Let PCheck (Γ : context) (A t : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t : A'].
  Let PTyEq (Γ : context) (A B : term) := forall Γ' A' B',
    [|-[de] Γ' ≅ Γ] ->
    [Γ' |-[de] A' ≅ A] ->
    [Γ' |-[de] B ≅ B'] ->
    [Γ' |-[al] A' ≅ B'].
  Let PTyRedEq (Γ : context) (A B : term) := forall Γ' A' B',
    [|-[de] Γ' ≅ Γ] ->
    whnf A' -> whnf B' ->
    [Γ' |-[de] A' ≅ A] -> [Γ' |-[de] B ≅ B'] ->
    [Γ' |- A' ≅h B'].
  Let PNeEq (Γ : context) (A t u : term) := forall Γ' t' u',
    [|-[de] Γ' ≅ Γ] ->
    whne t' -> whne u' ->
    [Γ' |-[de] t' ≅ t : A] -> [Γ' |-[de] u ≅ u' : A] ->
    ∑ A', [Γ' |-[al] t' ~ u' ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Γ' t' u',
    [|-[de] Γ' ≅ Γ] ->
    whne t' -> whne u' ->
    [Γ' |-[de] t' ≅ t : A] -> [Γ' |-[de] u ≅ u' : A] ->
    ∑ A', [Γ' |- t' ~h u' ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PTmEq (Γ : context) (A t u : term) := forall Γ' A' t' u',
  [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
  [Γ' |-[de] t' ≅ t : A'] -> [Γ' |-[de] u ≅ u' : A'] ->
  [Γ' |-[al] t' ≅ u' : A'].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Γ' A' t' u',
  [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
  [Γ' |-[de] t' ≅ t : A'] -> [Γ' |-[de] u ≅ u' : A'] ->
  [Γ' |- t' ≅h u' : A'] × [Γ' |-[de] A' ≅ A].

  Theorem conv_stability : AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTy PInf PInfRed PCheck PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvInduction.
    - intros * HA HB H IH * ? HconvA HconvB.
      eapply algo_conv_wh in H as [nfA' nfB'].
      eapply subject_reduction_type in HA, HB.
      2: now eapply validity in HconvB.
      2: now eapply validity in HconvA.
      eapply red_ty_complete in nfA' as [A'' [? nfA'']].
      2:{
        etransitivity.
        1: symmetry ; now eapply RedConvTyC.
        now symmetry.
      }
      eapply red_ty_complete in nfB' as [B'' [? nfB'']].
      2:{
        etransitivity.
        1: now symmetry ; eapply RedConvTyC.
        eassumption.
      }
      econstructor.
      1-2: now eapply redty_red.
      eapply IH ; tea.
      1-2: gen_typing.
      + etransitivity ; [..|etransitivity].
        1: symmetry.
        1,3: eapply RedConvTyC ; tea.
        eassumption.
      + etransitivity ; [..|etransitivity].
        1: symmetry.
        1,3: eapply RedConvTyC ; tea.
        eassumption.
  - intros * ? IHA ? IHB * ? ? ? Hconv Hconv'.
    eapply red_ty_compl_prod_r in Hconv as (?&A1&?&[Hred HconvA1]).
    eapply red_ty_compl_prod_l in Hconv' as (?&A2&?&[Hred' HconvA2]).
    eapply redty_red, red_whnf in Hred as ->, Hred' as -> ; tea.
    assert [Γ' |-[al] A1 ≅ A2] as HconvA.
    {
     apply IHA ; tea.
     all: now symmetry. 
    }
    econstructor ; fold_algo ; tea.
    eapply IHB.
    * econstructor ; tea.
      now symmetry.
    * eapply stability ; tea.
      econstructor.
      1: now eapply ctx_conv_refl, wf_conv_ctx.
      now symmetry.
    * eapply stability ; tea.
      econstructor.
      1: now eapply ctx_conv_refl, wf_conv_ctx.
      eapply conv_sound in HconvA ; tea.
      all: now eapply validity in HconvA1, HconvA2.
  - intros * ? ? ? HA HB.
    eapply red_ty_compl_univ_r in HA.
    eapply red_ty_compl_univ_l in HB.
    eapply redty_red, red_whnf in HA as ->, HB as -> ; tea.
    now constructor.
  - intros * Hconv IHM * ? ? ? HM HN.
    pose proof (Hconv' := Hconv).
    eapply algo_conv_wh in Hconv' as [? ? _].
    pose proof (HN' := HN).
    eapply red_ty_complete in HN' as [N' [HN' wN']].
    2: now econstructor.
    eapply redty_red, red_whnf in HN' as -> ; tea.
    pose proof (HM' := HM).
    symmetry in HM'.
    eapply red_ty_complete in HM' as [M' [HM' wM']].
    2: now econstructor.
    eapply redty_red, red_whnf in HM' as -> ; tea.
    pose proof (HM' := HM).
    pose proof (HN' := HN).
    unshelve eapply ty_conv_inj in HM', HN' ; tea.
    1-2: now econstructor.
    destruct wM', wN' ; cbn in * ; try easy.
    edestruct IHM as [? [HconvM HU]].
    4-5: eassumption.
    1-3: eassumption.
    eapply red_ty_compl_univ_r, redty_red, red_whnf in HU as ->.
    2: now eapply algo_conv_wh in HconvM as [].
    now econstructor.
  - intros * ? * ? ? ? Ht Hu.
    symmetry in H
    

  Theorem typing_stability : AlgoTypingInductionConcl PTy PInf PInfRed PCheck.
  Proof.
    subst PTy PInf PInfRed PCheck PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoTypingInduction.
    - econstructor.
    - intros * ? IHA ? IHB.
      econstructor ; fold_algo.
      1: easy.
      eapply IHB.
      econstructor ; tea.
      now econstructor ; eapply typing_sound, wf_conv_ctx.
    - intros * ? IH ? ?.
      econstructor ; fold_algo.
      eapply IH ; tea.
      econstructor.
      econstructor.
      now eapply wf_conv_ctx.
    - intros * Hin ? ?.
      eapply in_ctx_conv in Hin as [? []] ; tea. 
      eexists ; split.
      1: now econstructor.
      eassumption.
    - intros * ? IHA ? IHB ? ?.
      edestruct IHA as [? [HA ?]] ; tea.
      edestruct (IHB (Γ',, vass na A)) as [? [HB ?]] ; tea.
      1:{
        econstructor ; tea.
        do 3 econstructor ; tea.
        eapply infer_red_equiv, typing_sound in HA.
        2: now eapply wf_conv_ctx.
        eassumption.
      }
      eexists ; split.
      2: now do 2 econstructor ; eapply wf_conv_ctx.
      econstructor.
      + inversion HA.
        econstructor ; tea.
        etransitivity ; tea.
        eapply redty_red, univ_red_compl ; tea.
      + inversion HB.
        econstructor ; tea.
        etransitivity ; tea.
        eapply redty_red, univ_red_compl ; tea.
    - intros * ? IHA ? IHt ? ?.
      assert [Γ' |-[de] A].
      {
        eapply typing_sound.
        1: eauto.
        now eapply wf_conv_ctx. 
      }
      assert [Γ' |-[de] A ≅ A] by
        now econstructor.
      edestruct (IHt (Γ',, vass na A)) as [? [Ht ?]] ; tea.
      1: now econstructor ; tea ; econstructor.
      eexists ; split.
      all: now econstructor ; fold_decl ; fold_algo.
    - intros * ? IHf ? IHa ? ?.
      edestruct IHf as [? [Hf Hfconv]] ; tea.
      inversion Hf ; subst ; clear Hf.
      eapply prod_ty_red_compl_inj in Hfconv as (?&?&?&[? HA ]).
      eexists ; split.
      1: econstructor ; fold_algo.
      + econstructor ; tea.
        etransitivity ; tea.
        now eapply redty_red.
      + eauto.
      + eapply validity in HA as [].
        eapply typing_subst1 ; tea.
        econstructor ; fold_decl.
        eapply typing_sound ; tea.
        eapply IHa ; tea.
        now econstructor.
    - intros * ? IHt ? ? ?.
      edestruct IHt as [? [? HA]] ; tea.
      eexists ; split.
      + econstructor ; tea.
        reflexivity.
      + etransitivity ; tea.
        eapply RedConvTyC, subject_reduction_type ; tea.
        now eapply validity in HA.
    - intros * ? IHt ? ? * ? ?.
      edestruct IHt as [? [IHt' Htconv]] ; tea.
      now econstructor ; fold_algo.
  Admitted.

End AlgoStability.