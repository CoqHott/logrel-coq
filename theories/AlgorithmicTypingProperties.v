From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction
  GenericTyping DeclarativeTyping Generation Reduction AlgorithmicTyping LogRelConsequences BundledAlgorithmicTyping.

Import AlgorithmicTypingData BundledTypingData DeclarativeTypingProperties.

Lemma conv_red_l Γ A A' A'' : [Γ |-[de] A' ≅ A''] -> [A' ⇒* A] -> [Γ |-[de] A ≅ A''].
Proof.
  intros Hconv **.
  etransitivity ; tea.
  symmetry.
  eapply RedConvTyC, subject_reduction_type ; tea.
  boundary.
Qed.

Section AlgoConvConv.

  Lemma in_ctx_conv_r Γ' Γ n decl :
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
    eapply typing_shift ; boundary.
  - destruct d as [? d].
    edestruct IHHin as [[? d'] []].
    1: eassumption.
    cbn in *.
    econstructor ; split.
    1: now econstructor.
    cbn.
    eapply typing_shift ; boundary.
  Qed.

  Lemma in_ctx_conv_l Γ' Γ n decl' :
  [|-[de] Γ' ≅ Γ] ->
  in_ctx Γ' n decl' ->
  ∑ decl, (in_ctx Γ n decl) × ([Γ' |-[de] decl'.(decl_type) ≅ decl.(decl_type)]).
  Proof.
    intros ? Hin.
    eapply in_ctx_conv_r in Hin as [? []].
    2: now symmetry.
    eexists ; split ; tea.
    symmetry.
    now eapply stability.
  Qed.

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

  Theorem bundled_conv_conv :
    BundledConvInductionConcl PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
  Proof.
    all: subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
    apply BundledConvInduction ; cbn in *.
    1-4: now constructor.
    - intros * HΓ **.
      eapply in_ctx_conv_r in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      eassumption.
    - intros * ? IHm Ht [IHt []%boundary] **.
      edestruct IHm as [[? [? (?&?&?&[HconvP HconvA])%red_ty_compl_prod_r]] ?] ; tea.
      eapply redty_red, red_whnf in HconvP as ->.
      2: gen_typing.
      eexists ; split.
      + econstructor ; refold ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply stability.
    - intros * ? IHm **.
      edestruct IHm as [[A'' []] []]; tea.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'.
      {
        eapply conv_red_l ; tea.
        now symmetry.
      }
      pose proof HconvA' as [? []]%red_ty_complete ; tea.
      eexists ; split.
      + econstructor ; refold.
        all: eauto using redty_red.
      + symmetry ; etransitivity ; tea.
        now eapply RedConvTyC.
      + eassumption.
    - intros * ? ? ? []%algo_conv_wh IH ? ? ? ? A'' **.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'
        by now eapply conv_red_l.
      pose proof HconvA' as [? []]%red_ty_complete ; tea.
      econstructor ; refold ; tea.
      1: now eapply redty_red.
      eapply IH ; tea.
      etransitivity ; tea.
      now eapply RedConvTyC.
    - intros * ? [IHA HconvA] ? IHB ? ? ? * ? HconvU ?.
      eapply red_ty_compl_univ_l, redty_red, red_whnf in HconvU as ->.
      2: gen_typing.
      econstructor ; refold.
      + eapply IHA ; tea.
        do 2 econstructor ; refold.
        boundary.
      + assert [Γ' |-[de] A].
        {
          eapply stability ; tea.
          econstructor ; refold.
          now boundary.
        }
        eapply IHB ; tea.
        all: econstructor ; tea.
        all: econstructor ; tea.
        econstructor ; refold.
        all: gen_typing.
    - intros * ? ? ? IHf ? ? ? * ? (?&?&?&[HconvP])%red_ty_compl_prod_l ?.
      eapply redty_red, red_whnf in HconvP as ->.
      2: gen_typing.
      econstructor ; refold ; tea.
      eapply IHf ; tea.
      now econstructor. 
    - intros * ? IHm ? ? ? ? * ? HconvN HtyA'.
      edestruct IHm as [[? []] ?] ; tea.
      unshelve eapply ty_conv_inj in HconvN.
      1: now constructor.
      1: assumption.
      cbn in HconvN.
      econstructor ; refold ; tea.
      destruct HtyA'.
      1-2: easy.
      assumption.
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

  Corollary algo_conv_conv : AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    pose proof bundled_conv_conv as Hind.
    subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
    unfold BundledConvInductionConcl, AlgoConvInductionConcl in *.
    unshelve (repeat (split ; [destruct Hind as [Hind _] ; shelve | destruct Hind as [_ Hind]])).
    1-2: now constructor.
    all: intros * Hconv ; intros ; eapply Hind ; tea.
    all: match goal with H : ConvCtx _ _ |- _ => symmetry in H ; apply boundary_ctx_conv_l in H end.
    all: split ; tea.
    all: try solve [now apply algo_conv_wh in Hconv as []].
    all: now boundary.
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
    destruct (AlgoConvInduction PTyEq PTyEq PNeEq PNeEq PTmEq PTmRedEq) as [?[?[?[?[?]]]]].
    12: repeat (split; [assumption|]); assumption. 
    subst PTyEq PNeEq PTmEq PTmRedEq.
    all: try solve [now constructor].
    - intros * ? ? ? Hconv IH ?.
      econstructor ; tea.
      eapply IH, whred_det ; tea.
      2: gen_typing.
      eapply algo_conv_wh in Hconv as [].
      now gen_typing.
    - intros * ? IHA ? IHB _.
      now econstructor ; refold.
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
      econstructor ; refold.
      all: intuition eauto.
    - intros * ? IHA ? IHB  **.
      econstructor ; refold.
      1: now intuition eauto.
      eapply IHB.
      econstructor ; tea.
      eapply IHA.
    - now econstructor.
    - intros * ? IHM  **.
      edestruct IHM as [[U' [IHM' HconvM]] []] ; tea.
      now econstructor.
    - intros * HΓ **.
      eapply in_ctx_conv_l in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      now eapply stability.
    - intros * ? IHm ? [IHt Hwft]  **.
      edestruct IHm as [[? [IHm' Hconv]] []] ; tea ; clear IHm.
      eapply red_ty_compl_prod_l in Hconv as (?&?&?&[Hred]).
      eapply redty_red, red_whnf in Hred as ->.
      2: now eapply algo_conv_wh in IHm' as [] ; gen_typing.
      eexists ; split.
      + econstructor ; refold.
        1: eassumption.
        eapply algo_conv_conv.
        * now eapply IHt.
        * now eapply conv_ctx_refl_r.
        * now symmetry.
        * eapply stability.
          2: now symmetry.
          boundary.
        * eapply stability.
          2: now symmetry.
          boundary.
      + eapply typing_subst1 ; tea.
        econstructor ; refold.
        2: now symmetry.
        eapply stability ; tea.
        now symmetry.
    - intros * ? IHm  **.
      edestruct IHm as [[A'' [IHm' Hconv]] [Hwf]] ; tea ; clear IHm.
      assert [Δ |-[de] A' ≅ A''] as Hconv'.
      {
        etransitivity ; tea.
        symmetry.
        eapply RedConvTyC, subject_reduction_type ; tea.
        eapply stability.
        2: now symmetry.
        boundary.
      }
      pose proof Hconv' as [? []]%red_ty_complete; tea.
      eexists ; split.
      + econstructor ; tea.
        now eapply redty_red.
      + etransitivity ; tea.
        now eapply RedConvTyC.
    - intros.
      econstructor ; refold.
      all: intuition eauto.
    - intros * ? IHA ? IHB **.
      econstructor ; refold.
      1: now eapply IHA.
      eapply IHB.
      econstructor ; tea.
      now econstructor ; intuition eauto.
    - intros * ? ? ? IH ? Hf  **.
      econstructor ; refold.
      1-2: assumption.
      eapply IH.
      econstructor ; tea.
      eapply boundary, prod_ty_inv in Hf as [].
      now econstructor.
    - intros * ? IH  **.
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
    - intros * ? [IHA ] ? IHB ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{
        apply algo_conv_wh in H5 as [e _].
        now inversion e.
        }
        econstructor ; refold.
        + eapply IHA ; tea.
        + eapply IHB ; tea.
          now econstructor.
    - intros * ? ? _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{ apply algo_conv_wh in H2 as [e _]. now inversion e. }
      now constructor.
    - intros * ? IH ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      1-2: apply algo_conv_wh in H as [_ e] ; now inversion e.
      econstructor ; refold.
      now eapply IH.
    - intros * Hin ? _ _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      split.
      + now econstructor.
      + eapply in_ctx_conv_l in Hin as [? [Hin ]]; tea.
        eapply in_ctx_inj in Hin.
        2: clear Hin ; tea.
        now subst.
    - intros * ? IHm ? IHt ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      eapply IHm in H9 as [? []%prod_ty_inj] ; tea.
      split.
      + econstructor ; refold ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor ; refold.
        1: now eapply IHt.
        now symmetry.
    - intros * ? IH ? ? ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      edestruct IH as [[? HconvA] ?] ; tea.
      split.
      1: now econstructor.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; boundary.
      eassumption.
    - intros * ? ? Hu Ht' IHt ? ? ? * ? HconvA Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      eapply whred_det in Hu ; tea.
      2,3: now eapply algo_conv_wh in H8 as [], Ht' as [].
      subst.
      econstructor ; tea ; refold.
      eapply IHt ; tea.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; boundary.
      eassumption.
    - intros * ? [IHA HpostA] ? IHB ? ? ? * HΓ ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: now inversion H5 ; inversion H8.
      2: now inversion H5.
      econstructor ; refold.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor ; refold.
        * now symmetry in HΓ ; boundary.
        * econstructor ; refold.
          boundary.
    - intros * ? ? ? IH ? ? ? * ? ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      1,3: now unshelve eapply ty_conv_inj in H6 ; [econstructor | econstructor | cbn in *].
      eapply prod_ty_inj in H6 as [].
      econstructor ; tea.
      eapply IH ; tea.
      now econstructor.
    - intros * ? IH ? ? ? ? * ? ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      1-2: now unshelve eapply ty_conv_inj in H5 ; [now econstructor | now econstructor | cbn in *].
      econstructor ; refold ; tea.
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
      econstructor ; refold ; tea.
      econstructor ; refold.
      2: etransitivity.
      all: eassumption.
    - intros * [? ? Hc] HA.
      destruct Hc as [? ? ? ? Ht Hc] ; refold.
      econstructor ; tea.
      1: now destruct HA.
      econstructor ; refold ; tea.
      eapply algo_conv_trans.
      + split ; tea.
        now eapply typing_sound, boundary in Ht.
      + now eapply ctx_refl.
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
      + now eapply ctx_refl. 
    - red ; intros * Hconv [? ? ? Hconv'].
      econstructor ; tea.
      1: now apply Hconv.
      eapply algo_conv_trans ; tea.
      now eapply ctx_refl.
    - intros_bn.
      1-2: now apply typing_wk.
      now apply algo_conv_wk.
    - intros_bn.
      inversion bun_conv_ty ; subst ; clear bun_conv_ty.
      econstructor ; refold.
      1-2: now etransitivity.
      eassumption.
    - intros_bn.
      1-2: now econstructor.
      do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea ; refold.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_refl.
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
      + now eapply ctx_refl. 
    - red. intros * Hconv [? ? ? Hconv'].
      split ; tea.
      1: apply Hconv.
      eapply algo_conv_trans ; tea.
      + now apply ctx_refl.
      + now constructor.
    - intros_bn.
      all: eapply conv_sound in bun_conv_ty ; tea.
      1-2: now econstructor.
      eapply algo_conv_conv ; tea.
      now apply ctx_refl.
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
      assert [Γ |-[de] A] by boundary.
      assert [Γ |-[de] n : A'] by
        (eapply conv_sound in Hconvn as [[]%boundary] ; tea ; now gen_typing).
      assert [Γ |-[de] n' : A'] by
        (eapply conv_sound in Hconvn as [[]%boundary] ; tea ; now gen_typing).
      split ; tea.
      1-2: now gen_typing.
      eapply algo_conv_conv ; tea.
      2: now eapply ctx_refl.
      apply ne_conv_conv.
      2: eassumption.
      boundary.
    - intros_bn.
      + now constructor.
      + constructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now apply ctx_refl.
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
      2: now eapply ctx_refl.
      econstructor ; tea.
      etransitivity ; tea.
      now symmetry.
    - red. intros_bn.
      + eapply algo_conv_trans ; tea.
        * now constructor.
        * now apply ctx_refl.
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
      inversion H ; subst ; clear H  ; refold.
      econstructor.
      + assumption.
      + eexists. now econstructor.
      + gen_typing.
      + eexists. now econstructor.
      + gen_typing.
      + now econstructor ; refold.
      + eapply conv_sound in H0 ; tea.
        enough [Γ |-[de] tRel n : decl_type decl] by boundary.
        now econstructor.
  - intros *
    [? ? ? ? ? ? Hf (?&?&?&[])%red_ty_compl_prod_r]
    [? ? ? ? Ht].
    econstructor ; tea.
    + eapply conv_sound in Hf as [Hf] ; tea.
      eapply boundary in Hf as [_ Hf _].
      eexists ; econstructor ; refold.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + gen_typing.
    + eapply conv_sound in Hf as [Hg] ; tea.
      eapply boundary in Hg as [_ _ Hg].
      eexists ; econstructor ; refold.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + gen_typing.
    + econstructor ; refold.
      * econstructor ; tea.
        2: econstructor.
        now eapply redty_red.
      * eapply algo_conv_conv ; tea.
        now eapply ctx_refl.
    + eapply typing_subst1 ; tea.
      econstructor.
      eassumption.
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
      econstructor ; [econstructor|..] ; refold.
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