From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction
  GenericTyping DeclarativeTyping Generation Reduction AlgorithmicTyping.

Import AlgorithmicTypingData DeclarativeTypingProperties.

Lemma infer_red_equiv Γ t A :
  InferRedAlg Γ A t <~> [Γ |-[al] t ▹h A].
Proof.
  split ; intros [] ; now econstructor.
Qed.

Section AlgTypingWh.

  Let PTy (Γ : context) (A : term) := True.
  Let PInf (Γ : context) (A t : term) := True.
  Let PInfRed (Γ : context) (A t : term) := True.
  Let PCheck (Γ : context) (A t : term) := True.
  Let PTyEq (Γ : context) (A B : term) := True.
  Let PTyRedEq (Γ : context) (A B : term) := 
    isType A × isType B.
  Let PNeEq (Γ : context) (A t u : term) := 
    whne t × whne u.
  Let PNeRedEq (Γ : context) (A t u : term) :=
    whne t × whne u.
  Let PTmEq (Γ : context) (A t u : term) := True.
  Let PTmRedEq (Γ : context) (A t u : term) := 
    [× whnf t, whnf u & isType A].

  Theorem typing_alg_wh :
    WfAlgoInductionConcl PTy PInf PInfRed PCheck PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTy PInf PInfRed PCheck PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
    apply WfAlgoInduction.
    all: try solve [now constructor].
    all: intros ;
      repeat match goal with
      | H : [× _, _ & _] |- _ => destruct H
      | H : _ × _ |- _ => destruct H
      end.
    all: try solve [now do 2 constructor].
    constructor.
    1-2: gen_typing.
    now constructor.
  Qed.
End AlgTypingWh.

Conjecture typing_subst : WfDeclInductionConcl
  (fun _ => True)
  (fun Γ A => forall Δ σ, [|-[de] Δ] -> [Δ |-[de]s σ : Γ] -> [Δ |-[de] A[σ]])
  (fun Γ A t => forall Δ σ, [|-[de] Δ] -> [Δ |-[de]s σ : Γ] -> [Δ |-[de] t[σ] : A[σ]])
  (fun Γ A B => forall Δ σ σ', [|-[de] Δ] -> [Δ |-[de]s σ ≅ σ' : Γ] -> [Δ |-[de] A[σ] ≅ B[σ']])
  (fun Γ A t u => forall Δ σ σ', [|-[de] Δ] -> [Δ |-[de]s σ ≅ σ' : Γ] -> [Δ |-[de] t[σ] ≅ u[σ'] : A[σ]]).

Conjecture validity : WfDeclInductionConcl
  (fun _ => True)
  (fun _ _ => True)
  (fun Γ A t => [Γ |-[de] A])
  (fun Γ A B => [Γ |-[de] A] × [Γ |-[de] B])
  (fun Γ A t u => [× [Γ |-[de] A], [Γ |-[de] t : A] & [Γ |- u : A]]).

Conjecture prod_ty_inj : forall Γ na A B na' A' B',
  [Γ |-[de] tProd na A B ≅ tProd na' A' B'] ->
  [Γ |-[de] A' ≅ A] × [Γ,, vass na A |-[de] B ≅ B'].

Conjecture prod_tm_inj : forall Γ na A B na' A' B',
  [Γ |-[de] tProd na A B ≅ tProd na' A' B' : U ] ->
  [Γ |-[de] A' ≅ A : U ] × [Γ,, vass na A |-[de] B ≅ B' : U].

Conjecture app_neu_inj : forall Γ m t n u T,
  whne m ->
  whne n ->
  [Γ |-[de] tApp m t ≅ tApp n u : T] ->
  ∑ na A B, [×
    [Γ |-[de] m ≅ n : tProd na A B],
    [Γ |-[de] t ≅ u : A] &
    [Γ |-[de] B[t..] ≅ T]].

Conjecture prod_ty_red_compl : forall Γ na A B T,
  [Γ |-[de] tProd na A B ≅ T] ->
  ∑ na' A' B', [Γ |-[de] T ⇒* tProd na' A' B'].

Conjecture prod_tm_red_compl : forall Γ na A B T,
  [Γ |-[de] tProd na A B ≅ T : U] ->
  ∑ na' A' B', [Γ |-[de] T ⇒* tProd na' A' B' : U].

Conjecture univ_red_compl : forall Γ T,
  [Γ |-[de] U ≅ T] ->
  [Γ |-[de] T ⇒* U].

Section Stability.

  Lemma ctx_conv_refl Γ :
    [|-[de] Γ] ->
    [|-[de] Γ ≅ Γ].
  Proof.
    induction 1.
    all: constructor ; tea.
    now eapply TypeRefl.
  Qed.

  Lemma wk_subst_compose (Γ Δ Δ' : context) (ρ : Δ' ≤ Δ) σ :
    [|- Δ'] ->
    [Δ |-s σ : Γ] ->
    [Δ' |-s σ >> ⟨ρ⟩ : Γ].
  Proof.
    intros ?.
    induction 1 as [|σ Γ na A].
    1: now econstructor.
    econstructor.
    - asimpl ; cbn in * ; asimpl.
      eassumption.
    - asimpl ; cbn in * ; asimpl.
      unfold funcomp.
      eapply typing_meta_conv.
      1: eapply typing_wk ; eassumption.
      asimpl.
      reflexivity.
  Qed.

  Lemma well_subst_up (Γ Δ : context) na A σ :
    [Δ |- A] ->
    [Δ |-s σ : Γ] ->
    [Δ ,, vass na A |-s σ >> ⟨↑⟩ : Γ].
  Proof.
    intros HA Hσ.
    unshelve eapply (wk_subst_compose _ _ (Δ,, vass na A)) in Hσ.
    - now eapply wk_step, wk_id.
    - eapply well_subst_ext ; [|eassumption].
      asimpl ; cbn in * ; asimpl.
      rewrite wk_to_ren_id.
      now reflexivity.
    - econstructor ; fold_decl.
      all: gen_typing.
  Qed.

  Lemma id_subst (Γ : context) :
    [|- Γ] ->
    [Γ |-s tRel : Γ].
  Proof.
    induction 1.
    all: econstructor.
    - eapply well_subst_ext.
      2: now eapply well_subst_up.
      now asimpl.
    - eapply typing_meta_conv.
      1: now do 2 econstructor.
      cbn ; now renamify.
  Qed.

  Lemma wf_subst (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [|- Γ].
  Proof.
    destruct 1 as [| ? ? ? ? ? ? ? HA].
    all: econstructor ; fold_decl.
    - gen_typing.
    - now eapply validity in HA.
  Qed.

  Lemma subst_refl (Γ Δ : context) σ :
    [Γ |-[de]s σ : Δ] ->
    [Γ |-[de]s σ ≅ σ : Δ].
  Proof.
    induction 1.
    all: econstructor ; tea.
    now eapply TermRefl.
  Qed.

  Lemma conv_well_subst (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [Γ |-[de]s tRel : Δ].
  Proof.
    induction 1 as [| * ? HA].
    - now econstructor.
    - assert [Γ |-[de] A] by
        now eapply validity in HA as [].
      assert [|-[de] Γ,, vass na A] by
        (econstructor ; fold_decl ;
        eauto using wf_subst).
      econstructor ; fold_decl ; tea.
      + eapply well_subst_ext, well_subst_up ; tea.
        reflexivity.
      + econstructor.
        1: now econstructor ; [..|econstructor].
        cbn ; renamify.
        unshelve eapply typing_wk in HA.
        2: eapply wk_step, wk_id.
        2: eassumption.
        unshelve erewrite (extRen_term _ _ _ B), (extRen_term _ _ _ A).
        5: eassumption.
        all: now intros ; cbn ; rewrite wk_to_ren_id.
  Qed.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ,
    [|-[de] Δ ≅ Γ] -> [Δ |- A].
  Let PTm (Γ : context) (A t : term) := forall Δ,
    [|-[de] Δ ≅ Γ] -> [Δ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|-[de] Δ ≅ Γ] -> [Δ |- A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Δ ≅ Γ] -> [Δ |- t ≅ u : A].

  Theorem stability : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    1: now unfold PCon.
    all: intros * Hty Δ HΔ.
    all: pose proof (wf_subst _ _ HΔ).
    all: eapply conv_well_subst in HΔ.
    all: pose proof (subst_refl _ _ _ HΔ).
    all: eapply typing_subst in Hty ; tea.
    all: repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: try eassumption.
  Qed.

End Stability.

Section Soundness.

  Lemma termGen' Γ t A :
    [Γ |- t : A] ->
    ∑ A', (termGenData Γ t A') × [Γ |- A' ≅ A].
  Proof.
    intros * H.
    destruct (termGen _ _ _ H) as [? [? [->|]]].
    2: now eexists.
    eexists ; split ; tea.
    eapply TypeRefl.
    now eapply validity in H.
  Qed.

  Theorem subject_reduction_one Γ t t' A :
    [Γ |-[de] t : A] ->
    [t ⇒ t'] ->
    [Γ |- t ⇒ t' : A].
  Proof.
    intros Hty Hred.
    induction Hred in Hty, A |- *.
    - apply termGen' in Hty as [? [Hty Heq]].
      inversion Hty; subst ; clear Hty.
      apply termGen' in H1 as [? [Hty Heq']].
      inversion Hty ; subst ; clear Hty.
      eapply prod_ty_inj in Heq' as [? HeqB].
      econstructor ; fold_decl.
      1: econstructor ; fold_decl ; gen_typing.
      etransitivity ; tea.
      eapply typing_subst ; tea.
      1: now gen_typing.
      econstructor ; cbn.
      all: asimpl.
      2: eapply TermRefl ; fold_decl ; gen_typing.
      now eapply subst_refl, id_subst ; gen_typing.
    - apply termGen' in Hty as [? [Hty Heq]].
      inversion Hty ; subst ; clear Hty.
      econstructor ; tea.
      econstructor.
      1: easy.
      fold_decl ; gen_typing.
    Qed.

  Theorem subject_reduction Γ t t' A :
    [Γ |-[de] t : A] ->
    [t ⇒* t'] ->
    [Γ |- t ⇒* t' : A].
  Proof.
    intros Hty.
    induction 1 as [| ? ? ? o red] in A, Hty |- *.
    1: now econstructor.
    eapply subject_reduction_one in o ; tea.
    etransitivity.
    2: eapply IHred.
    1: now constructor.
    now eapply RedConvTe, validity in o as [].
  Qed.

  Lemma subject_reduction_one_type Γ A A' :
    [Γ |- A] ->
    [A ⇒ A'] ->
    [Γ |- A ⇒ A'].
  Proof.
    intros Hty.
    inversion 1 ; subst.
    all: inversion Hty ; subst ; clear Hty.
    all: econstructor.
    all: now eapply subject_reduction_one.
  Qed.

  Theorem subject_reduction_type Γ A A' :
  [Γ |- A] ->
  [A ⇒* A'] ->
  [Γ |- A ⇒* A'].
  Proof.
    intros Hty.
    induction 1 as [| ? ? ? o red] in Hty |- *.
    1: now econstructor.
    eapply subject_reduction_one_type in o ; tea.
    etransitivity.
    2: eapply IHred.
    1: now constructor.
    now eapply RedConvTy, validity in o as [].
  Qed.

  Lemma typing_eta' (Γ : context) na A B f :
    [Γ |- f : tProd na A B] ->
    [Γ,, vass na A |- eta_expand f : B].
  Proof.
    intros Hf.
    eapply typing_eta ; tea.
    - gen_typing.
    - eapply validity in Hf.
      inversion Hf ; subst ; tea.
      eapply termGen' in H as [? [H ?]]; inversion H ; subst ; clear H.
      now econstructor.
    - eapply validity in Hf.
      inversion Hf ; subst ; tea.
      eapply termGen' in H as [? [H ?]]; inversion H ; subst ; clear H.
      now econstructor.
  Qed.

  Let PTy (Γ : context) (A : term) :=
    [|-[de] Γ] -> [Γ |-[de] A].
  Let PInf (Γ : context) (A t : term) :=
    [|-[de] Γ] ->
    [Γ |-[de] t : A].
  Let PCheck (Γ : context) (A t : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] t : A].
  Let PTyEq (Γ : context) (A B : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] B] ->
    [Γ |-[de] A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) :=
    [Γ |-[de] t : A] -> [Γ |-[de] u : A] ->
    [Γ |-[de] t ≅ u : A].
  Let PNeEq (Γ : context) (A : term) (m n : term) :=
    (∑ T, [Γ |-[de] m : T]) ->
    (∑ T, [Γ |-[de] n : T]) ->
    [× [Γ |-[de] m ≅ n : A],
      (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
      (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])].

  Theorem typing_sound :
    WfAlgoInductionConcl PTy PInf PInf PCheck PTyEq PTyEq
      PNeEq PNeEq PTmEq PTmEq.
  Proof.
    subst PTy PInf PCheck PTyEq PNeEq PTmEq.
    apply WfAlgoInduction.
    - now econstructor.
    - econstructor ; fold_decl ; gen_typing.
    - econstructor ; fold_decl ; gen_typing.
    - econstructor ; fold_decl ; gen_typing.
    - econstructor ; fold_decl ; gen_typing.
    - econstructor ; fold_decl ; gen_typing.
    - intros * ? IHf ? IHA.
      econstructor ; fold_decl.
      1: gen_typing.
      eapply validity, prod_ty_inv in IHf as [] ; tea.
      now gen_typing.
    - intros * ? IHt HA ?.
      eapply subject_reduction_type, RedConvTyC in HA.
      2: now eapply validity in IHt.
      gen_typing.
    - intros * ? IHt ? IHA ?.
      unshelve epose proof (IHA _ _) ; tea.
      1: eapply validity in IHt.
      all: gen_typing.
    - intros * HA HB ? IHA' ? ?.
      eapply subject_reduction_type, RedConvTyC in HA, HB ; tea.
      unshelve epose proof (IHA' _ _).
      1-2: now eapply validity in HA, HB.
      symmetry in HB.
      do 2 etransitivity ; tea.
      now eapply TypeRefl.
    - intros * ? IHA ? IHB ? ?.
      eapply prod_ty_inv in H1 as [], H2 as [].
      econstructor ; fold_decl ; tea.
      1: now eauto.
      eapply IHB.
      1: eauto.
      eapply stability ; tea.
      econstructor.
      2: now eauto.
      eapply ctx_conv_refl.
      now gen_typing.
    - now gen_typing.
    - intros * Hconv IH HM HN.
      eapply typing_alg_wh in Hconv as [neM neN].
      eapply convUniv ; fold_decl.
      inversion HM ; subst ; clear HM.
      1-2: now inversion neM.
      inversion HN ; subst ; clear HN.
      1-2: now inversion neN.
      now eapply IH.
    - intros * Hin []  _.
      split.
      + do 2 constructor ; fold_decl ; gen_typing.
      + intros T Hty.
        eapply termGen' in Hty as [? [Hty ?]].
        inversion Hty ; subst ; clear Hty.
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
      + intros T Hty.
        eapply termGen' in Hty as [? [Hty ?]].
        inversion Hty ; subst ; clear Hty.
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
    - intros * ? IHm ? IHt [? Htym] [? Htyn].
      eapply termGen' in Htym as [? [Htym ?]].
      inversion Htym ; subst ; clear Htym.
      eapply termGen' in Htyn as [? [Htyn ?]].
      inversion Htyn ; subst ; clear Htyn.
      edestruct IHm as [IHmc IHm' IHn'].
      1-2: now econstructor.
      eapply IHm', prod_ty_inj in H3 as [].
      eapply IHn', prod_ty_inj in H4 as [].
      split.
      + econstructor ; fold_decl ; gen_typing.
      + intros ? Happ.
        eapply termGen' in Happ as [? [Happ ?]].
        inversion Happ ; subst ; clear Happ.
        eapply IHm', prod_ty_inj in H3 as [].
        etransitivity ; [..|eassumption].
        eapply typing_subst.
        1-2: gen_typing.
        econstructor ; asimpl.
        1: eapply subst_refl, id_subst.
        2: eapply TermRefl ; fold_decl.
        all: now gen_typing.
      + intros ? Happ.
        eapply termGen' in Happ as [? [Happ ?]].
        inversion Happ ; subst ; clear Happ.
        eapply IHn', prod_ty_inj in H3 as [].
        etransitivity ; [..|eassumption].
        eapply typing_subst.
        1-2: gen_typing.
        econstructor ; asimpl.
        1: eapply subst_refl, id_subst.
        all: now gen_typing.
    - intros * ? IHm HA [? Htym] [? Htyn].
      edestruct IHm as [IHmc IHm' IHn'].
      1-2: now eexists.
      eapply subject_reduction_type, RedConvTyC in HA.
      2: now eapply validity in IHmc as [].
      split.
      + gen_typing.
      + intros.
        symmetry in HA.
        etransitivity ; gen_typing.
      + intros.
        symmetry in HA.
        etransitivity ; gen_typing.
    - intros * HA Ht Hu ? IH Htyt Htyu.
      eapply subject_reduction_type, RedConvTyC in HA.
      2: now eapply validity in Htyt.
      eapply subject_reduction, RedConvTeC in Ht ; tea.
      eapply subject_reduction, RedConvTeC in Hu ; tea.
      etransitivity ; [..|etransitivity].
      1: eassumption.
      2: now symmetry.
      eapply TermConv ; fold_decl.
      2: now symmetry.
      eapply IH.
      all: econstructor ; fold_decl ; tea.
      all: now eapply validity in Ht as [], Hu as [].
    - intros * ? IHA ? IHB Hty Hty'.
      eapply termGen' in Hty as [? [Hty _]].
      inversion Hty ; subst ; clear Hty.
      eapply termGen' in Hty' as [? [Hty' _]].
      inversion Hty' ; subst ; clear Hty'.
      econstructor ; fold_decl.
      + now econstructor.
      + now eapply IHA.
      + eapply IHB ; tea.
        eapply stability ; tea.
        econstructor.
        1: eapply ctx_conv_refl ; gen_typing.
        now econstructor.
    - intros * ? ? ? IH Hf Hg.
      assert [Γ |-[de] A].
      {
        eapply validity in Hf.
        inversion Hf ; subst ; clear Hf.
        1: eassumption.
        eapply termGen' in H2 as [? [Hty ]].
        inversion Hty ; subst ; clear Hty.
        now econstructor.
      }
      econstructor ; tea ; fold_decl.
      eapply IH.
      all: now eapply typing_eta'.
    - intros * ? IHm ? Htym Htyn.
      edestruct IHm as [? Hm'].
      1-2: now eexists.
      eapply TermConv ; tea ; fold_decl.
      now eapply Hm'.
  Qed.

End Soundness.

Section Transitivity.

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

  Theorem typing_trans :
    WfAlgoInductionConcl PTy PInf PInfRed PCheck PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    apply WfAlgoInduction.
    - econstructor.
    - intros * ? IHA ? IHB.
      econstructor ; unfold PTy in * ; fold_algo.
      1: easy.
      eapply IHB.
      econstructor ; tea.
      eapply TypeRefl ; fold_decl.
  Admitted.

End Transitivity.

Module AlgorithmicTypingProperties.
  Include AlgorithmicTypingData.

  #[export, refine] Instance WfCtxAlgProperties : WfContextProperties (ta := al) := {}.
  Proof.
    all: now constructor.
  Qed.

  #[export, refine] Instance WfTypeAlgProperties : WfTypeProperties (ta := al) := {}.
  Proof.
    2-4: now econstructor.
    intros.
    now eapply typing_alg_wk.
  Qed.

  #[export, refine] Instance InferringAlgProperties : InferringProperties (ta := al) := {}.
  Proof.
    - intros.
      now eapply typing_alg_wk.
    - now econstructor.
    - econstructor.
      all: now eapply infer_red_equiv.
    - now econstructor.
    - econstructor.
      1: now eapply infer_red_equiv.
      eassumption. 
  Qed.  

  #[export, refine] Instance TypingAlgProperties : TypingProperties (ta := al) := {}.
  Proof.
    - intros.
      now eapply typing_alg_wk.
    - intros.
      now econstructor.
    - intros * Hc ?.
      destruct Hc as [? ? ? ? ? Hc].
      destruct Hc.
      econstructor ; fold_algo ; tea.
      econstructor ; fold_algo.
      2: etransitivity.
      all: eassumption.
    - intros * Hc ?.
      destruct Hc.
      econstructor ; fold_algo ; tea.
      red.
      admit.
  Admitted.

  #[export, refine] Instance ConvTypeAlgProperties : ConvTypeProperties (ta := al) := {}.
  Proof.
  Admitted.

  #[export, refine] Instance ConvTermAlgProperties : ConvTermProperties (ta := al) := {}.
  Proof.
  Admitted.

  #[export, refine] Instance ConvNeuAlgProperties : ConvNeuProperties (ta := al) := {}.
  Proof.
  Admitted.

  Lemma RedTermAlgProperties :
    RedTermProperties (ta := al).
  Proof.
  Admitted.

  #[export]Existing Instance RedTermAlgProperties.

  Lemma RedTypeAlgProperties :
    RedTypeProperties (ta := al).
  Proof.
  Admitted.

  #[export] Existing Instance RedTypeAlgProperties.

  #[export] Instance AlgorithmicTypingProperties : GenericTypingProperties al _ _ _ _ _ _ _ _ _ := {}.

End AlgorithmicTypingProperties.