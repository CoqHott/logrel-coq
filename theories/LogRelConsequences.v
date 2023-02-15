From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction
  GenericTyping DeclarativeTyping Generation Reduction AlgorithmicTyping.

Import DeclarativeTypingProperties.

Conjecture typing_subst : WfDeclInductionConcl
  (fun _ => True)
  (fun Γ A => forall Δ σ, [|- Δ] -> [Δ |-s σ : Γ] -> [Δ |- A[σ]])
  (fun Γ A t => forall Δ σ, [|- Δ] -> [Δ |-s σ : Γ] -> [Δ |- t[σ] : A[σ]])
  (fun Γ A B => forall Δ σ σ', [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] -> [Δ |- A[σ] ≅ B[σ']])
  (fun Γ A t u => forall Δ σ σ', [|- Δ] -> [Δ |-s σ ≅ σ' : Γ] -> [Δ |- t[σ] ≅ u[σ'] : A[σ]]).

Conjecture boundary : WfDeclInductionConcl
  (fun _ => True)
  (fun _ _ => True)
  (fun Γ A t => [Γ |- A])
  (fun Γ A B => [Γ |- A] × [Γ |- B])
  (fun Γ A t u => [× [Γ |- A], [Γ |- t : A] & [Γ |- u : A]]).

Corollary boundary_tm Γ A t : [Γ |- t : A] -> [Γ |- A].
Proof.
  now intros ?%boundary.
Qed.

Corollary boundary_ty_conv_l Γ A B : [Γ |- A ≅ B] -> [Γ |- A].
Proof.
  now intros ?%boundary.
Qed.

Corollary boundary_ty_conv_r Γ A B : [Γ |- A ≅ B] -> [Γ |- B].
Proof.
  now intros ?%boundary.
Qed.

Corollary boundary_ored_ty_r Γ A B : [Γ |- A ⇒ B] -> [Γ |- B].
Proof.
  now intros ?%RedConvTy%boundary.
Qed.

Corollary boundary_red_ty_r Γ A B : [Γ |- A ⇒* B] -> [Γ |- B].
Proof.
  now intros ?%RedConvTyC%boundary.
Qed.

Corollary boundary_tm_conv_l Γ A t u : [Γ |- t ≅ u : A] -> [Γ |- t : A].
Proof.
  now intros []%boundary.
Qed.

Corollary boundary_tm_conv_r Γ A t u : [Γ |- t ≅ u : A] -> [Γ |- u : A].
Proof.
  now intros []%boundary.
Qed.

Corollary boundary_tm_conv_ty Γ A t u : [Γ |- t ≅ u : A] -> [Γ |- A].
Proof.
  now intros []%boundary.
Qed.

Corollary boundary_ored_tm_l Γ A t u : [Γ |- t ⇒ u : A] -> [Γ |- t : A].
Proof.
  now intros []%RedConvTe%boundary.
Qed.

Corollary boundary_ored_tm_r Γ A t u : [Γ |- t ⇒ u : A] -> [Γ |- u : A].
Proof.
  now intros []%RedConvTe%boundary.
Qed.

Corollary boundary_ored_tm_ty Γ A t u : [Γ |- t ⇒ u : A] -> [Γ |- A].
Proof.
  now intros []%RedConvTe%boundary.
Qed.

Corollary boundary_red_tm_l Γ A t u : [Γ |- t ⇒* u : A] -> [Γ |- t : A].
Proof.
  now intros []%RedConvTeC%boundary.
Qed.

Corollary boundary_red_tm_r Γ A t u : [Γ |- t ⇒* u : A] -> [Γ |- u : A].
Proof.
  now intros []%RedConvTeC%boundary.
Qed.

Corollary boundary_red_tm_ty Γ A t u : [Γ |- t ⇒* u : A] -> [Γ |- A].
Proof.
  now intros []%RedConvTeC%boundary.
Qed.

#[export] Hint Resolve
  boundary_tm boundary_ty_conv_l boundary_ty_conv_r
  boundary_tm_conv_l boundary_tm_conv_r boundary_tm_conv_ty
  boundary_ored_tm_l boundary_ored_tm_r boundary_ored_tm_ty
  boundary_red_tm_l boundary_red_tm_r boundary_red_tm_ty
  boundary_ored_ty_r boundary_red_ty_r : boundary.


Lemma boundary_ctx_conv_l (Γ Δ : context) :
  [ |- Γ ≅ Δ] ->
  [|- Γ].
Proof.
  destruct 1 as [| ? ? ? ? ? ? ? HA].
  all: econstructor ; refold ; boundary.
Qed.

#[export] Hint Resolve boundary_ctx_conv_l : boundary.

Section NeutralConjecture.
  Import AlgorithmicTypingData.

  Conjecture ne_conv_conv : forall (Γ : context) (A m n : term),
    [Γ |-[de] A] ->
    [Γ |-[al] m ~ n ▹ A] ->
    [Γ |-[al] m ≅ n : A].

End NeutralConjecture.

Definition type_hd_view (Γ : context) {T T' : term} (nfT : isType T) (nfT' : isType T') : Type :=
  match nfT, nfT' with
    | @UnivType s, @UnivType s' => s = s'
    | @ProdType na A B, @ProdType na' A' B' => [Γ |- A' ≅ A] × [Γ,, vass na' A' |- B ≅ B']
    | NeType _, NeType _ => [Γ |- T ≅ T' : U]
    | _, _ => False
  end.

Conjecture red_ty_complete : forall (Γ : context) (T T' : term),
  isType T ->
  [Γ |- T ≅ T'] ->
  ∑ T'', [Γ |- T' ⇒* T''] × isType T''.

Conjecture ty_conv_inj : forall (Γ : context) (T T' : term) (nfT : isType T) (nfT' : isType T'),
  [Γ |- T ≅ T'] ->
  type_hd_view Γ nfT nfT'.

(* Conjecture app_neu_inj : forall Γ m t n u T,
  whne m ->
  whne n ->
  [Γ |- tApp m t ≅ tApp n u : T] ->
  ∑ na A B, [×
    [Γ |- m ≅ n : tProd na A B],
    [Γ |- t ≅ u : A] &
    [Γ |- B[t..] ≅ T]]. *)

Corollary red_ty_compl_univ_l Γ T :
  [Γ |- U ≅ T] ->
  [Γ |- T ⇒* U].
Proof.
  intros HT.
  pose proof HT as HT'.
  unshelve eapply red_ty_complete in HT' as (T''&[? nfT]).
  2: econstructor.
  enough (T'' = U) as -> by easy.
  assert [Γ |- U ≅ T''] as Hconv by
    (etransitivity ; [eassumption|now eapply RedConvTyC]).
  unshelve eapply ty_conv_inj in Hconv.
  1: econstructor.
  1: eassumption.
  now destruct nfT, Hconv.
Qed.

Corollary red_ty_compl_univ_r Γ T :
  [Γ |- T ≅ U] ->
  [Γ |- T ⇒* U].
Proof.
  intros.
  eapply red_ty_compl_univ_l.
  now symmetry.
Qed.

Corollary red_ty_compl_prod_l Γ na A B T :
  [Γ |- tProd na A B ≅ T] ->
  ∑ na' A' B', [× [Γ |- T ⇒* tProd na' A' B'], [Γ |- A' ≅ A] & [Γ,, vass na' A' |- B ≅ B']].
Proof.
  intros HT.
  pose proof HT as HT'.
  unshelve eapply red_ty_complete in HT as (T''&[? nfT]).
  2: econstructor.
  assert [Γ |- tProd na A B ≅ T''] as Hconv by 
    (etransitivity ; [eassumption|now eapply RedConvTyC]).
  unshelve eapply ty_conv_inj in Hconv.
  1: constructor.
  1: assumption.
  destruct nfT, Hconv.
  do 3 eexists ; split.
  all: eassumption.
Qed.

Corollary prod_ty_inj Γ na A B na' A' B' :
  [Γ |- tProd na A B ≅ tProd na' A' B'] ->
  [Γ |- A' ≅ A] × [Γ,, vass na' A' |- B ≅ B'].
Proof.
  intros Hty.
  unshelve eapply ty_conv_inj in Hty.
  1-2: constructor.
  now eassumption.
Qed.

Section Stability.

  Lemma ctx_refl Γ :
    [|- Γ] ->
    [|- Γ ≅ Γ].
  Proof.
    induction 1.
    all: constructor ; tea.
    now econstructor.
  Qed.

  Lemma subst_wk (Γ Δ Δ' : context) (ρ : Δ' ≤ Δ) σ :
    [|- Δ'] ->
    [Δ |-s σ : Γ] ->
    [Δ' |-s σ⟨ρ⟩ : Γ].
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

  Corollary well_subst_up (Γ Δ : context) na A σ :
    [Δ |- A] ->
    [Δ |-s σ : Γ] ->
    [Δ ,, vass na A |-s σ⟨↑⟩ : Γ].
  Proof.
    intros HA Hσ.
    eapply subst_wk with (ρ := wk_step na A wk_id) in Hσ.
    - eapply well_subst_ext ; [|eassumption].
      bsimpl.
      now reflexivity.
    - econstructor ; refold.
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

  Corollary conv_ctx_refl_l (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [|- Γ ≅ Γ].
  Proof.
    intros.
    eapply ctx_refl ; boundary.
  Qed.

  Lemma subst_refl (Γ Δ : context) σ :
    [Γ |-s σ : Δ] ->
    [Γ |-s σ ≅ σ : Δ].
  Proof.
    induction 1.
    all: econstructor ; tea.
    now eapply TermRefl.
  Qed.

  Lemma conv_well_subst (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [Γ |-s tRel : Δ].
  Proof.
    induction 1 as [| * ? HA].
    - now econstructor.
    - assert [Γ |- A] by boundary.
      assert [|- Γ,, vass na A] by
        (econstructor ; refold ; boundary).
      econstructor ; refold ; tea.
      + eapply well_subst_ext, well_subst_up ; tea.
        reflexivity.
      + econstructor ; refold.
        1: now econstructor ; [..|econstructor].
        cbn ; renamify ; refold.
        (* TODO: the following should work!
          eapply typing_wk with (ρ := wk_step na A wk_id). *)
        unshelve eapply typing_wk in HA.
        2: apply wk1.
        2: eassumption.
        now setoid_rewrite (extRen_term _ _ wk1_ren) in HA.
  Qed.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- A].
  Let PTm (Γ : context) (A t : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|- Δ ≅ Γ] -> [Δ |- t ≅ u : A].

  Theorem stability : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    1: now unfold PCon.
    all: intros * Hty Δ HΔ.
    all: pose proof (boundary_ctx_conv_l _ _ HΔ).
    all: eapply conv_well_subst in HΔ.
    all: pose proof (subst_refl _ _ _ HΔ).
    all: eapply typing_subst in Hty ; tea.
    all: asimpl ; repeat (rewrite idSubst_term in Hty ; [..|reflexivity]).
    all: try eassumption.
  Qed.

  Corollary red_ty_compl_prod_r Γ na A B T :
    [Γ |- T ≅ tProd na A B] ->
    ∑ na' A' B', [× [Γ |- T ⇒* tProd na' A' B'], [Γ |- A ≅ A'] & [Γ,, vass na A |- B' ≅ B]].
  Proof.
    intros HT.
    symmetry in HT.
    eapply red_ty_compl_prod_l in HT as (?&?&?&[? HA HB]).
    do 3 eexists ; split ; tea.
    1: now symmetry.
    symmetry.
    eapply stability in HB.
    eapply HB.
    econstructor.
    - eapply ctx_refl ; boundary.
    - now symmetry.
  Qed.

  Theorem typing_subst1 Γ nt T :
    (forall (t : term), [Γ |- t : T] ->
      forall (A : term), [Γ,, vass nt T |- A] -> [Γ |- A[t..]]) ×
    (forall (t : term), [Γ |- t : T] ->
      forall (A u : term), [Γ,, vass nt T |- u : A] -> [Γ |- u[t..] : A[t..]]) ×
    (forall (t t' : term), [Γ |- t ≅ t' : T] ->
      forall (A B : term), [Γ,, vass nt T |- A ≅ B] -> [Γ |- A[t..] ≅ B[t'..]]) ×
  (forall (t t' : term), [Γ |- t ≅ t' : T] ->
    forall (A u v : term), [Γ,, vass nt T |- u ≅ v : A] -> [Γ |- u[t..] ≅ v[t'..] : A[t..]]).
  Proof.
    repeat match goal with |- _ × _ => split end.
    all: intros * Ht * Hty.
    all: assert ([|- Γ]) by gen_typing.
    all: assert ([Γ |-s tRel : Γ]) as Hsubst by now eapply id_subst.
    3-4: apply subst_refl in Hsubst.
    all: eapply typing_subst ; tea.
    all: econstructor ; cbn ; refold ; now asimpl.
  Qed.

  #[global] Instance ConvCtxSym : Symmetric ConvCtx.
  Proof.
    intros Γ Δ.
    induction 1.
    all: constructor ; tea.
    eapply stability ; tea.
    now symmetry.
  Qed.

  Corollary conv_ctx_refl_r (Γ Δ : context) :
    [ |- Γ ≅ Δ] ->
    [|- Δ ≅ Δ].
  Proof.
    intros H.
    symmetry in H.
    now eapply ctx_refl ; boundary.
  Qed.

  #[global] Instance ConvCtxTrans : Transitive ConvCtx.
  Proof.
    intros Γ1 Γ2 Γ3 H1 H2.
    induction H1 in Γ3, H2 |- *.
    all: inversion H2 ; subst ; clear H2.
    all: constructor.
    1: eauto.
    etransitivity ; tea.
    now eapply stability.
  Qed.

End Stability.

Lemma termGen' Γ t A :
[Γ |- t : A] ->
∑ A', (termGenData Γ t A') × [Γ |- A' ≅ A].
Proof.
intros * H.
destruct (termGen _ _ _ H) as [? [? [->|]]].
2: now eexists.
eexists ; split ; tea.
econstructor ; refold.
boundary.
Qed.

Theorem subject_reduction_one Γ t t' A :
    [Γ |- t : A] ->
    [t ⇒ t'] ->
    [Γ |- t ⇒ t' : A].
Proof.
  intros Hty Hred.
  induction Hred in Hty, A |- *.
  - apply termGen' in Hty as (?&((?&?&?&[-> Hty])&Heq)).
    apply termGen' in Hty as (?&((?&[->])&Heq')).
    eapply prod_ty_inj in Heq' as [? HeqB].
    econstructor ; refold.
    1: econstructor ; refold ; gen_typing.
    etransitivity ; tea.
    eapply typing_subst1 ; tea.
    now econstructor.
  - apply termGen' in Hty as (?&((?&?&?&[->])&Heq)).
    econstructor ; tea.
    econstructor.
    1: easy.
    refold ; gen_typing.
  Qed.

  Theorem subject_reduction Γ t t' A :
    [Γ |- t : A] ->
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
    boundary.
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
    boundary.
  Qed.

  Lemma typing_eta' (Γ : context) na A B f :
    [Γ |- f : tProd na A B] ->
    [Γ,, vass na A |- eta_expand f : B].
  Proof.
    intros Hf.
    eapply typing_eta ; tea.
    - gen_typing.
    - eapply prod_ty_inv.
      boundary.
    - eapply prod_ty_inv.
      boundary.
  Qed.