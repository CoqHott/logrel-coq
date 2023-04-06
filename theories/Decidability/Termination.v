(** * LogRel.Decidability.Termination: the implementation always terminates on well-typed inputs. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness Completeness.
From PartialFun Require Import Monad PartialFun.

Set Universe Polymorphism.

Import DeclarativeTypingProperties.

Section ConversionComplete.

Let PTyEq (Γ : context) (A B : term) :=
  forall v B',
  [Γ |- B'] ->
  domain conv (ty_state;Γ;v;A;B').
Let PTyRedEq (Γ : context) (A B : term) :=
  forall v B',
  isType B' ->
  [Γ |- B'] ->
  domain conv (ty_red_state;Γ;v;A;B').
Let PNeEq (Γ : context) (A t u : term) :=
  forall v u',
  whne u' ->
  well_typed Γ u' ->
  domain conv (ne_state;Γ;v;t;u').
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall v u',
  whne u' ->
  well_typed Γ u' ->
  domain conv (ne_red_state;Γ;v;t;u').
Let PTmEq (Γ : context) (A t u : term) :=
  forall u',
  [Γ |- u' : A] ->
  domain conv (tm_state;Γ;A;t;u').
Let PTmRedEq (Γ : context) (A t u : term) :=
  forall u',
  whnf u' ->
  [Γ |- u' : A] ->
  domain conv (tm_red_state;Γ;A;t;u').

Theorem _conv_terminates :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  apply BundledConvInduction.
  - intros * ?? HA' [IH] **.
    apply compute_domain.
    simp conv.
    cbn.
    split.
    1: eapply wh_red_complete ; now exists istype.
    intros A''; split.
    1: eapply wh_red_complete ; now exists istype.
    intros B'' ; split.
    2: easy.
    assert [Γ |- B''].
    {
      eapply boundary_red_ty_r, subject_reduction_type.
      2: now eapply red_sound.
      eassumption.
    }
    replace A'' with A'.
    1: apply (IH tt B'').
    + eapply type_isType ; tea.
      now eapply red_sound.
    + eassumption. 
    + eapply whred_det ; tea.
      1: now eapply algo_conv_wh in HA' as [] ; gen_typing.
      all: now eapply red_sound.
  - intros * ? [IHA] ? [IHB] ? []%prod_ty_inv []%prod_ty_inv ? B' wB' HtyB'.
    apply compute_domain.
    simp conv.
    destruct wB' as [|A'' B''| | |? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now rewrite (whne_ty_view1 wB') ; cbn.
    apply prod_ty_inv in HtyB' as [].
    split.
    2: intros [] ; cbn ; [|easy].
    2: intros Hconv%implem_conv_sound%algo_conv_sound ; tea ; split ; [|easy].
    + now apply (IHA tt A'').
    + apply (IHB tt B'').
      now eapply stability1.
  - intros * ??? ? ? wB' ?.
    apply compute_domain.
    simp conv.
    destruct wB' as [| | | |? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    now rewrite (whne_ty_view1 wB') ; cbn.
  - intros * ??? ? ? wB' ?.
    apply compute_domain.
    simp conv.
    destruct wB' as [| | | |? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    now rewrite (whne_ty_view1 wB') ; cbn.
  - intros * ??? ? ? wB' ?.
    apply compute_domain.
    simp conv.
    destruct wB' as [| | | |? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    now rewrite (whne_ty_view1 wB') ; cbn.
  - intros * HM [IHM []] ??? ? ? wB' Hty.
    apply compute_domain.
    simp conv.
    eapply algo_conv_wh in HM as [].
    destruct wB' as [| | | |? wB'].
    1-4: simp build_nf_ty_view2 ; cbn.
    1-4: now unshelve erewrite whne_ty_view1 ; cbn.
    erewrite whne_ty_view2 ; tea.
    split.
    2: intros [|] ; cbn ; easy.
    eapply (IHM tt A) ; tea.
    inversion Hty ; subst ; tea.
    1-4: now inversion wB'.
    now exists U.
  - intros * ???? ? ? wu' ?.
    apply compute_domain.
    destruct wu' as [n'| | |].
    all: simp conv ; cbn ; try easy.
    destruct (Nat.eqb_spec n n') ; cbn.
    2: easy.
    split ; [|easy].
    eexists.
    now apply ctx_access_correct.
  - intros ? ???? A B Hm [IHm []] ? [IHt] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [|m' t'| | ].
    all: simp conv ; cbn ; try easy.
    split.
    + apply (IHm tt m') ; tea.
      destruct Hty as [? (?&(?&?&[])&?)%termGen'].
      now eexists.
    + destruct Hty as [? (?&(?&?&[??Htym'])&?)%termGen'] ; subst.
      intros [T|] ; cbn ; [|easy] ; intros [Hconvm?]%implem_conv_sound.
      assert (T = tProd A B) by now eapply algo_conv_det.
      subst.
      apply algo_conv_sound in Hconvm as [?? Hgenm'].
      2-3: now eexists ; boundary.
      apply Hgenm' in Htym' as []%prod_ty_inj.
      cbn.
      split.
      2: intros [|] ? ; cbn ; easy.
      eapply (IHt t').
      gen_typing.
  - intros * Hn [IHn] ? [IHP] ? [IHz] ? [IHs] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [| |P'' hz'' hs'' n''| ].
    all: simp conv ; cbn ; try easy.
    destruct Hty as [? (?&[]&?)%termGen'].
    split.
    1: apply (IHn tt n'') ; tea ; now eexists.
    intros [T|] ; cbn ; [|easy] ; intros [HconvT ?]%implem_conv_sound.
    eapply algo_conv_det in HconvT as ->.
    2: now apply Hn.
    cbn.
    split.
    1: now apply (IHP tt P'').
    intros [|] ; cbn ; [|easy] ; intros HconvP%implem_conv_sound%algo_conv_sound.
    2-3: boundary.
    split.
    1:{
      specialize (IHz hz'') ; apply IHz.
      econstructor ; tea.
      eapply typing_subst1.
      2: now symmetry.
      now do 2 econstructor.
    }
    assert (domain conv (tm_state; Γ; elimSuccHypTy P; hs; hs'')).
    {
      specialize (IHs hs'') ; apply IHs.
      econstructor ; tea.
      eapply elimSuccHypTy_conv ; tea.
      now symmetry. 
    }
    intros [|] ; cbn.
    2: now split.
    intros ? ; split.
    1: assumption.
    now intros [|] ; cbn.
  - intros * He [IHe] ? [IHP] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [| | | P'' e'' ].
    all: simp conv ; cbn ; try easy.
    destruct Hty as [? (?&[]&?)%termGen'].
    split.
    1: apply (IHe tt e'') ; tea ; now eexists.
    intros [T|] ; cbn ; [|easy] ; intros [HconvT ?]%implem_conv_sound.
    eapply algo_conv_det in HconvT as ->.
    2: now apply He.
    cbn.
    split.
    1: now apply (IHP tt P'').
    intros [|] ; cbn ; easy.
  - intros * ? [IHm] ?? ??? ? u' wu' Hty.
    apply compute_domain.
    simp conv ; cbn.
    split.
    2: intros [T|] ; cbn ; [|easy] ; intros []%implem_conv_sound%algo_conv_sound ; tea.
    2: split ; [|easy].
    + now apply (IHm tt u').
    + eapply wh_red_complete.
      exists istype.
      boundary.
  - intros * ??? Hconv [IHt'] ??? u' Hty.
    apply compute_domain.
    simp conv ; cbn.
    split.
    2: intros A'' [redA]%red_sound ; split.
    3: intros t'' []%red_sound ; split.
    4: intros u'' [redu]%red_sound ; split.
    + eapply wh_red_complete.
      exists istype.
      boundary.
    + eapply wh_red_complete.
      now eexists (isterm _).
    + eapply wh_red_complete.
      now eexists (isterm _).
    + assert (A'' = A').
      {
        eapply whred_det ; tea.
        apply algo_conv_wh in Hconv as [].
        gen_typing.
      }
      assert (t'' = t').
      {
        eapply whred_det ; tea.
        now apply algo_conv_wh in Hconv as [].
      }
      subst.
      eapply (IHt' u'') ; tea.
      eapply subject_reduction in redu ; tea.
      econstructor.
      1: boundary.
      eapply subject_reduction_type in redA as [] ; refold ; tea.
      now boundary.
    + easy.
  - intros * ? [IHA] ? [IHB] ??? u' wu' Hty.
    apply compute_domain.
    simp conv build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ | A'' B'' | | | ? wu'] ; cycle -1.
    1: rewrite (whne_ty_view1 wu').
    all: cbn ; try easy.
    eapply termGen' in Hty as (?&[]&?) ; subst.
    split.
    2: intros [|] ; cbn ; [|easy] ; intros ?%implem_conv_sound%algo_conv_sound.
    3-4: boundary.
    2: split.
    + now apply (IHA A'').
    + apply (IHB B'').
      eapply stability1 ; tea.
      1-2: boundary.
      now constructor.
    + now intros []. 
  - intros * ??? u' wu' Hty.
    apply compute_domain.
    simp conv build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ | | | | ? wu'] ; cycle -1.
    1: rewrite (whne_ty_view1 wu').
    all: now cbn.
  - intros * ??? u' wu' Hty.
    apply compute_domain.
    simp conv build_nf_view3 build_nf_ty_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' as [ | | ? wu'] ; cycle -1.
    1: rewrite (whne_nf_view1 wu').
    all: now cbn.
  - intros * ? [IHt] ??? u' wu' Hty.
    apply compute_domain.
    simp conv build_nf_view3 build_nf_ty_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' as [ | u' | ? wu'] ; cycle -1.
    1: rewrite (whne_nf_view1 wu').
    all: cbn ; try easy.
    split.
    2: now intros [|] ; cbn.
    eapply (IHt u').
    now apply termGen' in Hty as (?&[]&?).
  - intros * ??? u' wu' Hty.
    apply compute_domain.
    simp conv build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ | | | | ? wu'] ; cycle -1.
    1: rewrite (whne_ty_view1 wu').
    all: now cbn.
  - intros * ?? ? [IHf] ??? u' wu' Hty.
    apply compute_domain.
    simp conv build_nf_view3 ; cbn.
    split.
    2: easy.
    specialize (IHf (eta_expand u')).
    apply IHf.
    now eapply typing_eta'.
  - intros * Hm [IHm []] Hpos ??? u' wu' Hu'.
    apply compute_domain.
    simp conv build_nf_view3.
    eapply algo_conv_wh in Hm as [].
    destruct Hpos as [[]| | | ].
    + cbn.
      simp build_nf_ty_view2.
      unshelve erewrite whne_ty_view1 ; tea.
      cbn.
      eapply Uterm_isType in wu' ; tea.
      destruct wu' as [ | | | | u' wu'] ; cbn ; try easy.
      rewrite (whne_ty_view1 wu').
      cbn.
      split.
      2: now intros [] ; cbn.
      eapply (IHm tt u') ; tea.
      now eexists.
    + cbn.
      unshelve erewrite whne_nf_view1 ; tea.
      cbn.
      eapply nat_isNat in wu' ; tea.
      inversion wu'  as [| | u'' wu''] ; subst ; clear wu'.
      all: cbn ; try easy.
      rewrite (whne_nf_view1 wu'').
      cbn.
      split.
      2: now intros [] ; cbn.
      eapply (IHm tt u') ; tea.
      now eexists.
    + cbn.
      unshelve erewrite whne_nf_view1 ; tea.
      cbn.
      eapply empty_isEmpty in wu' ; tea.
      rewrite (whne_nf_view1 wu').
      cbn.
      split.
      2: now intros [] ; cbn.
      apply (IHm tt u') ; tea.
      now eexists.
    + unshelve erewrite whne_ty_view1 ; tea.
      cbn.
      eapply neutral_isNeutral in wu' ; tea.
      split.
      2: now intros [] ; cbn.
      apply (IHm tt u') ; tea.
      now eexists.
  Qed.
  
  Corollary conv_terminates Γ A A' :
    [Γ |-[de] A] ->
    [Γ |-[de] A'] ->
    forall v,
    domain conv (ty_state;Γ;v;A;A').
  Proof.
    intros.
    eapply _conv_terminates ; tea.
    split.
    4: eapply algo_conv_complete.
    4: econstructor.
    all: boundary.
  Qed.

End ConversionComplete.


    

