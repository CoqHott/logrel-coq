(** * LogRel.Decidability.Termination: the implementation always terminates on well-typed inputs. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations Weakening UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicConvProperties AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness Completeness.
From PartialFun Require Import Monad PartialFun.

Set Universe Polymorphism.

Import DeclarativeTypingProperties.
Import IndexedDefinitions.

Section ConversionTerminates.

  Import AlgorithmicTypingData.
  Import BundledTypingData.

Let PTyEq (Γ : context) (A B : term) :=
  forall v B',
  [Γ |-[de] B'] ->
  domain conv (ty_state;Γ;v;A;B').
Let PTyRedEq (Γ : context) (A B : term) :=
  forall v B',
  isType B' ->
  [Γ |-[de] B'] ->
  domain conv (ty_red_state;Γ;v;A;B').
Let PNeEq (Γ : context) (A t u : term) :=
  forall v u',
  whne u' ->
  well_typed (ta := de) Γ u' ->
  domain conv (ne_state;Γ;v;t;u').
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall v u',
  whne u' ->
  well_typed (ta := de) Γ u' ->
  domain conv (ne_red_state;Γ;v;t;u').
Let PNeListEq (Γ : context) (A t u : term) :=
  forall u',
  whne_list u' ->
  [Γ |-[de] u' : tList A] ->
  domain conv (ne_list_state;Γ;A;t;u').
Let PTmEq (Γ : context) (A t u : term) :=
  forall u',
  [Γ |-[de] u' : A] ->
  domain conv (tm_state;Γ;A;t;u').
Let PTmRedEq (Γ : context) (A t u : term) :=
  forall u',
  whnf u' ->
  [Γ |-[de] u' : A] ->
  domain conv (tm_red_state;Γ;A;t;u').

Theorem _conv_terminates :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq.
  apply BundledConvInduction.
  - intros * ?? HA' [IH] **.
    apply compute_domain.
    simp conv conv_ty.
    cbn.
    split.
    1: eapply wh_red_complete ; now exists istype.
    intros A''; split.
    1: eapply wh_red_complete ; now exists istype.
    intros B'' ; split.
    2: intros x; destruct x; cbn; easy.
    assert [Γ |-[de] B''].
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
    simp conv conv_ty_red.
    destruct wB' as [|A'' B''| | | | | ? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now rewrite (whne_ty_view1 wB') ; cbn.
    apply prod_ty_inv in HtyB' as [].
    split.
    2: intros [] ; cbn ; [|easy].
    2: intros Hconv%implem_conv_sound%algo_conv_sound ; tea ; split .
    + now apply (IHA tt A'').
    + apply (IHB tt B'').
      now eapply stability1.
    + intros x; destruct x; cbn; easy.
  - intros * ??? ? ? wB' ?.
    apply compute_domain.
    simp conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    match goal with H : whne _ |- _ => now rewrite (whne_ty_view1 H) ; cbn end.
  - intros * ??? ? ? wB' ?.
    apply compute_domain.
    simp conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    match goal with H : whne _ |- _ => now rewrite (whne_ty_view1 H) ; cbn end.
  - intros * ??? ? ? wB' ?.
    apply compute_domain.
    simp conv conv_ty_red.
    destruct wB'.
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    match goal with H : whne _ |- _ => now rewrite (whne_ty_view1 H) ; cbn end.
  - intros * ? [IHA] ? [IHB] ? []%sig_ty_inv []%sig_ty_inv ? B' wB' HtyB'.
    apply compute_domain.
    simp conv conv_ty_red.
    destruct wB' as [| | | | A'' B'' | | ? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now rewrite (whne_ty_view1 wB') ; cbn.
    apply sig_ty_inv in HtyB' as [].
    split.
    2: intros x; destruct x ; cbn ; [|easy].
    2: intros Hconv%implem_conv_sound%algo_conv_sound ; tea ; split.
    + now apply (IHA tt A'').
    + apply (IHB tt B'').
      now eapply stability1.
    + intros x; destruct x; cbn; easy.
  - intros * ? [IHA] ? ?%list_ty_inv ?%list_ty_inv ? B' wB' HtyB'.
    apply compute_domain.
    simp conv conv_ty_red.
    destruct wB' as [| | | | | A'' | ? wB'].
    all: simp build_nf_ty_view2 ; cbn ; try easy.
    2: now rewrite (whne_ty_view1 wB') ; cbn.
    apply list_ty_inv in HtyB'.
    split.
    2: intros x; destruct x ; cbn ; [|easy].
    2: intros Hconv%implem_conv_sound%algo_conv_sound ; tea ; split.
    now apply (IHA tt A'').
  - intros * HM [IHM []] ??? ? ? wB' Hty.
    apply compute_domain.
    simp conv conv_ty_red.
    eapply algo_conv_wh in HM as [].
    destruct wB'.
    1-6: simp build_nf_ty_view2 ; cbn.
    1-6: now unshelve erewrite whne_ty_view1 ; cbn.
    erewrite whne_ty_view2 ; tea.
    split.
    2: intros [|] ; cbn ; easy.
    eapply (IHM tt A) ; tea.
    inversion Hty ; subst ; tea.
    1-6:  inv_whne.
    now exists U. 
  - intros * ???? ? ? wu' ?.
    apply compute_domain.
    destruct wu' as [n'| | | | | |].
    all: simp conv conv_ne to_neutral_diag ; cbn ; try easy.
    destruct (Nat.eqb_spec n n') ; cbn.
    2: easy.
    erewrite ctx_access_complete ; tea.
    now econstructor.
  - intros ? ???? A B Hm [IHm []] ? [IHt] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [|m' t'| | | | |].
    all: simp conv conv_ne to_neutral_diag ; cbn; try exact I.
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
    destruct wu' as [| |P'' hz'' hs'' n''| | | |].
    all: simp conv conv_ne to_neutral_diag ; cbn ; try easy.
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
    destruct wu' as [| | | P'' e'' | | | ].
    all: simp conv conv_ne to_neutral_diag ; cbn ; try easy.
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
  - intros * h [ih []] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [| | | | t | |].
    all: simp conv conv_ne to_neutral_diag ; cbn ; try easy.
    destruct Hty as [? hu'%termGen']; cbn in hu'; prod_hyp_splitter; subst.
    split.
    1: apply (ih tt t); tea; now eexists.
    intros [T|]; cbn ; [|easy].
    intros [Hconv ?]%implem_conv_sound.
    eapply algo_conv_det in Hconv as ->.
    2: now eapply h.
    now cbn.
  - intros * h [ih []] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [| | | | | t |].
    all: simp conv conv_ne to_neutral_diag ; cbn ; try easy.
    destruct Hty as [? hu'%termGen']; cbn in hu'; prod_hyp_splitter; subst.
    split.
    1: apply (ih tt t); tea; now eexists.
    intros [T|]; cbn ; [|easy].
    intros [Hconv ?]%implem_conv_sound.
    eapply algo_conv_det in Hconv as ->.
    2: now eapply h.
    now cbn.
  - intros * HA [IHA] Hl [IHl] ? [IHP] ? [IHnil] ? [IHcons] ??? ? u' wu' Hty.
    apply compute_domain.
    destruct wu' as [| | | | | | A'' P'' hnil'' hcons'' l''].
    1-6: simp conv conv_ne to_neutral_diag ; cbn ; easy.
    simp conv conv_ne to_neutral_diag ; cbn.
    destruct Hty as [? (?&[]&?)%termGen'] ; subst.
    split.
    1: apply (IHA tt A'') ; tea ; now eexists.
    intros [?|] ; cbn ; [|easy] ; intros ?%implem_conv_sound%algo_conv_sound ; cbn in *.
    2-3: boundary.
    assert [Γ |-[de] tList A ≅ tList A''] by now econstructor.
    assert [Γ,, tList A |-[de] P''].
    {
     eapply stability1 ; last first ; tea.
     all: econstructor.
     all: now boundary. 
    } 
    split.
    1: eapply (IHl l'') ; tea ; econstructor ; tea ; now symmetry.
    intros [|] ; cbn ; [|easy] ; intros ?%implem_conv_sound ; cbn in *.
    split.
    1: now eapply (IHP tt P'').
    intros [|] ; cbn ; [|easy] ; intros ?%implem_conv_sound%algo_conv_sound ; cbn in *.
    2-3: boundary.
    split.
    1:{
      specialize (IHnil hnil'') ; apply IHnil.
      econstructor ; tea.
      symmetry.
      eapply typing_subst1 ; tea.
      now econstructor.
    }
    intros [|] ; cbn ; [|easy] ; intros _ ; cbn in *.
    split.
    2: intros [|] ; cbn ; easy.
    specialize (IHcons hcons'') ; apply IHcons.
    econstructor ; tea.
    symmetry.
    eapply elimConsHypTy_conv ; tea.
    all: boundary.
  - intros * ? [IHm] ?? ??? ? u' wu' Hty.
    apply compute_domain.
    simp conv conv_ne_red ; cbn.
    split.
    2: intros [T|] ; cbn ; [|easy] ; intros []%implem_conv_sound%algo_conv_sound ; tea.
    2: split ; [|easy].
    + now apply (IHm tt u').
    + eapply wh_red_complete.
      exists istype.
      boundary.
  - intros * Hlst [IHlst] Hfn [IHfn] ? []%map_eta_well_typed []%map_eta_well_typed u' wu' []%map_eta_well_typed.
    apply compute_domain.
    simp conv conv_ne_list ; cbn.
    split.
    + apply (IHlst tt (Map.lst (Map.eta B u'))).
      * now apply eta_map_lst_whne.
      * now eexists.
    + intros [A''|] ; cbn ; [|easy] ; intros [Hconvlst']%implem_conv_sound ; cbn in *.
      assert (A'' = tList A) as ->
        by now eapply algo_conv_det.
      eapply algo_conv_sound in Hconvlst' as [].
      2-3: now eexists.
      split ; cbn ; [|easy].
      apply (IHfn (Map.fn (Map.eta B u'))).
      eapply stability1.
      4: econstructor ; tea.
      * eapply list_ty_inv ; boundary.
      * eapply list_ty_inv ; boundary.
      * now eapply list_ty_inj.
      * rewrite wk1_ren_on.
        renToWk.
        eapply typing_wk ; tea.
        econstructor.
        all: boundary.
  - intros * ??? Hconv [IHt'] ??? u' Hty.
    apply compute_domain.
    simp conv conv_tm ; cbn.
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
    + intros x; destruct x; cbn; easy.
  - intros * ? [IHA] ? [IHB] ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ | A'' B'' | | | | | ? wu'] ; cycle -1.
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
    + intros x; destruct x; now cbn.
  - intros * ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ | | | | | | ? wu'] ; cycle -1.
    1: rewrite (whne_ty_view1 wu').
    all: now cbn.
  - intros * ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply nat_isNat in wu' ; tea.
    destruct wu' as [ | | ? wu'] ; cycle -1.
    1: rewrite (whne_nf_view1 wu').
    all: now cbn.
  - intros * ? [IHt] ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
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
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ | | | | | | ? wu'] ; cycle -1.
    1: rewrite (whne_ty_view1 wu').
    all: now cbn.
  - intros * ?? ? [IHf] ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 ; cbn.
    split.
    2: intros x; destruct x; now cbn.
    specialize (IHf (eta_expand u')).
    apply IHf.
    now eapply typing_eta'.
  - intros * ? [IHA] ? [IHB] ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ |  | | | A'' B'' | | ? wu'] ; cycle -1.
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
    + intros x; destruct x; now cbn.
  - intros * ?? ? [ihFst] ? [ihSnd] ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    econstructor.
    1: apply (ihFst (tFst u')); now econstructor.
    intros [T|]; cbn; [|easy].
    intros ?%implem_conv_sound%algo_conv_sound.
    2,3: now econstructor.
    split; [|intros x; destruct x; now cbn].
    apply (ihSnd (tSnd u')).
    eapply wfTermConv; refold; [now econstructor|].
    symmetry. eapply typing_subst1; tea.
    apply boundary in Hty as []%sig_ty_inv.
    now apply TypeRefl.
  - intros * HA [IHA] ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply Uterm_isType in wu' ; tea.
    destruct wu' as [ |  | | | | A'' | ? wu'] ; cycle -1.
    1: rewrite (whne_ty_view1 wu').
    all: cbn ; try easy.
    eapply termGen' in Hty as (?&[]&_) ; subst.
    split ; cbn ; [|easy].
    now apply (IHA A'').
  - intros * ??? u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply list_isList in wu' ; tea.
    destruct wu' as [ | | ? wu'] ; cycle -1.
    2-3: now cbn.
    destruct (Map.into_view n) ; cbn ; try easy.
    eapply whne_list_not_map in wu' ; tea.
    rewrite (whne_nf_view1 wu').
    now cbn.
  - intros * ? [IHhd] ? [IHtl] ? (?&[->]&?)%termGen' (?&[->]&?)%termGen' u' wu' Hty.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3 build_nf_ty_view2.
    eapply list_isList in wu' ; tea.
    destruct wu' as [ | ? hd'' tl'' | ? wu'] ; cycle -1.
    + destruct (Map.into_view n) ; cbn ; try easy.
      eapply whne_list_not_map in wu' ; tea.
      rewrite (whne_nf_view1 wu').
      now cbn.
    + now cbn.
    + eapply termGen' in Hty as (?&[->]&?).
      split.
      2: intros [|] ; cbn ; [|easy] ; intros ; split.
      3: intros [|] ; easy.
      * apply (IHhd hd'').
        econstructor ; tea.
        now eapply list_ty_inj.
      * apply (IHtl tl'').
        now econstructor.
  - intros * Hm [IHm] ??? u' wu' Hu'.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3.
    eapply list_isList in wu' ; tea.
    eapply algo_conv_wh in Hm as [wm].
    destruct wu' as [ | | ? wu'] ; cycle -1 ; cbn.
    + destruct wu' as [A'' B'' f'' l''| u' wu'], wm as [|? wm] ; cbn.
      * split.
        2: intros [|] ; now cbn.
        eapply (IHm (tMap A'' B'' f'' l'')) ; tea.
        now econstructor.
      * unshelve erewrite (whne_nf_view1 _) ; tea ; cbn.
        split.
        2: intros [|] ; now cbn.
        eapply (IHm (tMap A'' B'' f'' l'')) ; tea.
        now econstructor.
      * unshelve erewrite (whne_nf_view1 _) ; tea ; cbn.
        split.
        2: intros [|] ; now cbn.
        eapply (IHm u') ; tea.
        now econstructor.
      * unshelve erewrite !(whne_nf_view1 _) ; tea ; cbn.
        split.
        2: intros [|] ; now cbn.
        eapply (IHm u') ; tea.
        now econstructor.
    + destruct wm as [|? wm] ; cbn ; [easy|].
      now unshelve erewrite (whne_nf_view1 _) ; cbn.
    + destruct wm as [|? wm] ; cbn ; [easy|].
      now unshelve erewrite (whne_nf_view1 _) ; cbn.
  - intros * Hm [IHm []] Hpos ??? u' wu' Hu'.
    apply compute_domain.
    simp conv conv_tm_red build_nf_view3.
    eapply algo_conv_wh in Hm as [].
    destruct Hpos as [[]| | | ].
    + cbn.
      eapply Uterm_isType in wu' ; tea.
      unshelve epose proof (@whne_ty_view2_l m u' _ _) as [[? e]|e] ; tea.
      all: rewrite e ; cbn.
      2: easy.
      split.
      2: now intros [] ; cbn.
      eapply (IHm tt u') ; tea.
      now eexists.
    + cbn.
      unshelve erewrite whne_nf_view1 ; tea.
      cbn.
      eapply nat_isNat in wu' ; tea.
      inversion wu'  as [| | u'' wu'' ] ; subst ; clear wu'.
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

End ConversionTerminates.

Section TypingTerminates.

  Definition lt_state (s s' : typing_state) :=
    match s, s' with
    | inf_state, inf_state => False
    | inf_state, _ => True
    | inf_red_state, wf_ty_state => True
    | _, _ => False
    end.

  Lemma well_founded_lt_state : well_founded lt_state.
  Proof.
    intros [].
    all: repeat (constructor ; intros [] ; cbn ; try easy).
  Qed.

  #[local]Definition R_aux := lexprod term typing_state term_subterm lt_state.

  #[local]Definition R (x y : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term) :=
    R_aux
      (Datatypes.pair (x.π2.π2.π2) x.π1)
      (Datatypes.pair (y.π2.π2.π2) y.π1).
  
  #[local]Lemma R_acc : well_founded R.
  Proof.
    intros x.
    unfold R, R_aux.
    constructor.
    intros y h.
    eapply acc_A_B_lexprod in h.
  - remember (Datatypes.pair ((y.π2).π2).π2 y.π1) as y' eqn:e.
    induction h as [y'' h ih] in y, e |- *. subst.
    constructor. intros [v ρ] hr.
    eapply ih. 2: reflexivity.
    assumption.
  - eapply well_founded_term_subterm.
  - apply well_founded_lt_state.
  - apply well_founded_lt_state. 
  Qed.

Definition wf_input (s : typing_state) Γ : tstate_input s -> Type :=
  match s with
  | check_state => fun A => [Γ |-[de] A]
  | _ => fun _ => True
  end.

Theorem typing_terminates (s : typing_state) (Γ : context) (v : tstate_input s) (t : term) :
  [|-[de] Γ] ->
  wf_input s Γ v ->
  domain typing (s;Γ;v;t).
Proof.
  intros HΓ Hv.
  set (x := (s;Γ;v;t)).
  change s with (x.π1) in Hv.
  change Γ with (x.π2.π1) in HΓ, Hv.
  change v with (x.π2.π2.π1) in Hv.
  pose proof (Hacc := R_acc x).
  clearbody x.
  clear s Γ v t.
  induction Hacc as [x H IH] in HΓ, Hv |- * ; cbn in *.
  apply compute_domain. funelim_typing ; cbn in *; try easy.
  all: match goal with 
      | H : (_;_;_) = (_;_;_) |- _ => injection H; clear H; intros; subst
  end.

  - split.
    + apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    + intros [[]|] ; cbn ; try easy.
      intros ?%implem_typing_sound%algo_typing_sound ; tea.
      split ; cbn.
      2: now intros [[]|] ; cbn.
      apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      econstructor ; tea.
      econstructor.
      now destruct s.
  - split.
    + apply IH ; cbn ; try easy.
     left ; cbn ; now do 2 econstructor.
    + intros [|] ; cbn ; try easy.
      intros ?%implem_typing_sound%algo_typing_sound ; tea.
      split.
      2: intros [] ; now cbn.
      apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      now econstructor.
  - split.
    + apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    + intros [[]|] ; cbn ; try easy.
      intros Hf%implem_typing_sound%algo_typing_sound ; tea.
      split.
      2: intros [] ; now cbn.
      apply IH ; cbn ; tea.
      1: left ; cbn ; now do 2 econstructor.
      eapply prod_ty_inv.
      boundary.
  - split.
    + apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    + intros [[]|] ; now cbn.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [[]|] ; cbn ; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, tNat).
    assert ([|-[de] Γ']) by (now econstructor ; [|econstructor]). 
    split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; cbn ; [|easy].
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    2: intros [|] ; cbn ; intros _ ; split; [|intros []] ; try (cbn ; easy).
    + apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      eapply typing_subst1 ; tea.
      now econstructor.
    + apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      now eapply elimSuccHypTy_ty.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [[]|] ; cbn ; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, tEmpty).
    assert ([|-[de] Γ']) by (now econstructor ; [|econstructor]). 
    split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; now cbn.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea; split.
    set (Γ' := _ ,, _); assert [|-[de] Γ'] by (econstructor; tea; destruct s; now econstructor).
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros HA%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, _); assert [|-[de] Γ'] by (econstructor; tea; destruct s; now econstructor).
    split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros HB%implem_typing_sound%algo_typing_sound ; tea; split.
    1: apply IH ; cbn ; tea; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; try easy.
    intros Ha%implem_typing_sound%algo_typing_sound ; tea; split.
    match goal with
    | _ : [ ?Γ |-[de] _ : _] |- _ => assert [Γ|-[de] B[a..]] by now eapply typing_subst1
    end.
    1: apply IH ; cbn ; tea; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|]; cbn; easy.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|] HtyA; cbn; [|easy].
    eapply implem_typing_sound, algo_typing_sound in HtyA ; tea.
    split.
    + apply IH ; cbn.
      2-3: boundary.
      left ; cbn.
      now do 2 econstructor.
    + intros [[]|] _; cbn; [|easy].
      split.
      2: intros [|] ; cbn ; easy.
      eapply IH ; cbn.
      * left ; cbn.
        now do 2 econstructor.
      * easy.
      * now econstructor.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|] HtyA ; cbn ; [|easy].
    split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [[]|] HtyB ; cbn ; [|easy].
    eapply implem_typing_sound, algo_typing_sound in HtyA ; tea.
    eapply implem_typing_sound, algo_typing_sound in HtyB ; tea.
    split.
    2: intros [[]|] _ ; cbn ; [|easy].
    2: split.
    3: intros [|] ; cbn ; easy.
    + eapply IH ; cbn ; tea.
      1: left ; now do 2 econstructor.
      now eapply wft_simple_arr.
    + eapply IH ; cbn ; tea.
      1: left ; now do 2 econstructor.
      now econstructor.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [[]|] ; cbn ; try easy.
    intros Hn%implem_typing_sound%algo_typing_sound ; tea.
    set (Γ' := _ ,, tList A).
    assert ([|-[de] Γ']) by (now econstructor ; [|econstructor]). 
    split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; cbn ; [|easy].
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
      now econstructor.
    }
    intros [|] ; cbn ; [|easy].
    split.
    2: intros [|] ; cbn ; intros _ ; split; [|intros []] ; try (cbn ; easy).
    + apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      eapply typing_subst1 ; tea.
      now econstructor.
    + apply IH ; cbn ; try easy.
      1: left ; cbn ; now do 2 econstructor.
      now eapply elimConsHypTy_ty.
  - split.
    + apply IH ; cbn ; try easy.
      1: now right ; cbn.
    + intros [|] ; cbn ; [|easy].
      intros ?%implem_typing_sound%algo_typing_sound ; cbn in * ; tea.
      split.
      2: easy.
      eapply conv_terminates ; tea.
      boundary.
  - split.
    + apply IH ; cbn ; try easy.
      right; now cbn.
    + intros [|] ; cbn ; [|easy].
      intros ?%implem_typing_sound%algo_typing_sound ; cbn in * ; tea.
      split.
      2: easy.
      eapply wh_red_complete.
      exists istype.
      now boundary.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      left ; cbn ; now do 2 econstructor.
    }
    intros [|] ; cbn ; try easy.
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    2: intros []; now cbn.
    apply IH ; cbn ; try easy.
    1: left ; cbn ; now do 2 econstructor.
    now econstructor.
  - split.
    1: apply IH; cbn; try easy; left; cbn; now do 2 econstructor.
    intros [|] ; cbn ; try easy.
    intros ?%implem_typing_sound%algo_typing_sound ; tea.
    split.
    2: intros []; now cbn.
    apply IH ; cbn ; try easy.
    1: left ; cbn ; now do 2 econstructor.
    now econstructor.
  - split.
    2: easy.
    apply IH ; cbn ; try easy.
    left ; now do 2 econstructor.
  - split.
    1:{
      apply IH ; cbn ; try easy.
      right. now cbn.
    }
    intros [[]|] ; now cbn.
Qed.

End TypingTerminates.