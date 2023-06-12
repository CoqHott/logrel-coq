(** * LogRel.AlgorithmicConvProperties: properties of algorithmic conversion. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping DeclarativeSubst TypeConstructorsInj Normalisation BundledAlgorithmicTyping Fundamental.
From LogRel.LogicalRelation Require Import Escape.
From LogRel.Substitution Require Import Properties Escape.


Import AlgorithmicTypingData BundledTypingData DeclarativeTypingProperties.


(** ** Stability of algorithmic conversion by context and type change *)

(** If the input context and input type (when there is one) are changed to convertible
ones, algorithmic conversion still holds, possibly with a different output type
(when there is one). *)
Section AlgoConvConv.

  Lemma in_ctx_conv_r Γ' Γ n decl :
  [|-[de] Γ' ≅ Γ] ->
  in_ctx Γ n decl ->
  ∑ decl', (in_ctx Γ' n decl') × ([Γ' |-[de] decl' ≅ decl]).
  Proof.
  intros Hconv Hin.
  induction Hin in Γ', Hconv |- *.
  all: inversion Hconv ; subst ; clear Hconv.
  1: eexists ; split.
  - now econstructor.
  - cbn.
    renToWk.
    eapply typing_wk ; tea.
    econstructor.
    all: now boundary.
  - edestruct IHHin as [d'' [??]].
    1: eassumption.
    cbn in *.
    econstructor ; split.
    1: now econstructor.
    cbn.
    renToWk.
    eapply typing_wk ; tea.
    econstructor.
    all: now boundary.
  Qed.

  Lemma in_ctx_conv_l Γ' Γ n decl' :
  [|-[de] Γ' ≅ Γ] ->
  in_ctx Γ' n decl' ->
  ∑ decl, (in_ctx Γ n decl) × ([Γ' |-[de] decl' ≅ decl]).
  Proof.
    intros ? Hin.
    eapply in_ctx_conv_r in Hin as [? []].
    2: now symmetry.
    eexists ; split ; tea.
    symmetry.
    now eapply stability.
  Qed.

  Let PTyEq' (Γ : context) (A B : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    [Γ' |-[al] A ≅ B].
  Let PTyRedEq' (Γ : context) (A B : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    [Γ' |-[al] A ≅h B].
  Let PNeEq' (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [Γ' |-[al] t ~ u ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq' (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], [Γ' |-[de] A' ≅ A] & isType A'].
  Let PNeListEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t ~ u :List A'].
  Let PTmEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] -> isType A' ->
    [Γ' |-[al] t ≅h u : A'].

  Theorem bundled_conv_conv :
    BundledConvInductionConcl PTyEq' PTyRedEq' PNeEq' PNeRedEq' PNeListEq' PTmEq' PTmRedEq'.
  Proof.
    all: subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PNeListEq' PTmEq' PTmRedEq'.
    apply BundledConvInduction ; cbn in *.
    - intros * ??? IH **.
      econstructor ; tea.
      now eapply IH.
    - intros * ? IHA ? IHB ? H **.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      econstructor ; tea.
      econstructor.
      eapply stability ; tea.
      destruct IHA.
      now boundary.
    - now econstructor.
    - now econstructor.
    - now econstructor. 
    - intros * ? ihA ? ihB ? h **.
      econstructor.
      1: now eapply ihA.
      eapply ihB.
      econstructor ; tea.
      econstructor.
      eapply stability ; tea.
      destruct ihA.
      now boundary.
    - now econstructor.
    - intros * ? IHM **.
      edestruct IHM as [[? []]] ; tea.
      now econstructor.
    - intros * HΓ **.
      eapply in_ctx_conv_r in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      eassumption.
    - intros * ? IHm Ht [IHt []%boundary] **.
      edestruct IHm as [[? [? (?&?&[HconvP HconvA])%red_ty_compl_prod_r]] ?] ; tea.
      eapply redty_red, red_whnf in HconvP as ->.
      2: gen_typing.
      eexists ; split.
      + econstructor ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply stability.
    - intros * ? IHn ? IHP ? IHz ? IHs **.
      edestruct IHn as [[A []][]] ; tea.
      replace A with tNat in *.
      2:{
        symmetry.
        apply red_whnf.
        2: gen_typing.
        now eapply redty_red, red_ty_compl_nat_r.
      }
      eexists ; split.
      1: econstructor.
      + eauto.
      + eapply IHP.
        now econstructor.
      + eapply IHz ; tea.
        econstructor.
        eapply stability ; tea.
        destruct IHz.
        boundary.
      + eapply IHs ; tea.
        eapply TypeRefl ; refold.
        eapply stability ; tea.
        destruct IHs.
        boundary.
      + econstructor.
        destruct IHP.
        eapply stability ; tea.
        eapply typing_subst1.
        all: now boundary.
    - intros * ? IHe ? IHP **.
      edestruct IHe as [[A []][]] ; tea.
      replace A with tEmpty in *.
      2:{
        symmetry.
        apply red_whnf.
        2: gen_typing.
        now eapply redty_red, red_ty_compl_empty_r.
      }
      eexists ; split.
      1: econstructor.
      + eauto.
      + eapply IHP.
        now econstructor.
      + econstructor.
        destruct IHP.
        eapply stability ; tea.
        eapply typing_subst1.
        all: now boundary.
    - intros * ? [ih [? ihm ihn]] ? hm hn ??.
      edestruct ih as [?[? [?[?[r] ]]%red_ty_compl_sig_r isTy]]; tea.
      pose proof (redty_whnf r (isType_whnf _ isTy)); subst.
      eexists; split; tea; now econstructor.
    - intros * ? [ih [? ihm ihn]] **.
      edestruct ih as [?[? [?[?[r] ]]%red_ty_compl_sig_r isTy]]; tea.
      pose proof (redty_whnf r (isType_whnf _ isTy)); subst.
      eexists; split.
      1: now econstructor.
      eapply typing_subst1. 2: now symmetry.
      eapply TermConv; refold; [|now symmetry].
      econstructor; eapply lrefl.
      now eapply stability.
    - intros * ? IHm **.
      edestruct IHm as [[A'' []] []]; tea.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'.
      {
        eapply conv_red_l ; tea.
        now symmetry.
      }
      pose proof HconvA' as [? []]%red_ty_complete.
      2:{
        eapply type_isType ; tea.
        now boundary.
      }
      eexists ; split.
      + econstructor.
        1-2: eauto using redty_red.
        gen_typing.
      + symmetry ; etransitivity ; tea.
        now eapply RedConvTyC.
      + eassumption.
    - intros * ? [ih [? ihl ihr]] ? [] **.
      set (rl := Map.compact _ _) in *.
      set (rl' := Map.compact _ l') in *.
      edestruct ih as [T [ihlst hconv]] ; tea.
      eapply red_ty_compl_list_r in hconv as [A'' []].
      assert (T = tList A'') as ->.
      {
        eapply red_whnf.
        1: now eapply redty_sound.
        gen_typing.
      }
      econstructor.
      + repeat rewrite (Map.compact_lst_eq A' B).
        eapply ihlst.
      + 

      exists (tList (Map.tgtTy (fst rx))); split.
      + pose proof (redty_whnf r wh); subst.
        econstructor; fold rx; tea.
        1: now eapply c0.
        eapply c2; tea.
        eapply stability; tea.
        eapply TypeRefl; refold; boundary.
      + eapply stability; tea.
        eapply TypeRefl; refold.
        econstructor; boundary.
    - intros * ? ? ? []%algo_conv_wh IH ? ? ? ? A'' **.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'
        by now eapply conv_red_l.
      pose proof HconvA' as [? []]%red_ty_complete ; tea.
      econstructor ; tea.
      1: now eapply redty_red.
      eapply IH ; tea.
      etransitivity ; tea.
      now eapply RedConvTyC.
    - intros * ? [IHA HconvA] ? IHB ? ? ? * ? HconvU ?.
      eapply red_ty_compl_univ_l, redty_red, red_whnf in HconvU as ->.
      2: gen_typing.
      econstructor.
      + eapply IHA ; tea.
        do 2 econstructor.
        boundary.
      + assert [Γ' |-[de] A].
        {
          eapply stability ; tea.
          econstructor.
          now boundary.
        }
        eapply IHB ; tea.
        all: econstructor ; tea.
        all: econstructor ; tea.
        econstructor.
        all: gen_typing.
    - intros.
      replace A' with U.
      2:{
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply redty_red, red_ty_compl_univ_l.
      }
      now econstructor.
    - intros.
      replace A' with tNat.
      2:{
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply redty_red, red_ty_compl_nat_l.
      }
      now econstructor.
    - intros * ? IH **.
      replace A' with tNat.
      2:{
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply redty_red, red_ty_compl_nat_l.
      }
      econstructor.
      eapply IH ; tea.
      now do 2 econstructor.
    - intros * ? IH **.
      replace A' with U.
      2:{
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply redty_red, red_ty_compl_univ_l.
      }
      now econstructor.
    - intros * ? ? ? IHf ? ? ? * ? (?&?&[HconvP])%red_ty_compl_prod_l ?.
      eapply redty_red, red_whnf in HconvP as ->.
      2: gen_typing.
      econstructor ; tea.
      eapply IHf ; tea.
      now econstructor. 
    - intros * ? [ihA] ? [ihB] ?????? r%red_ty_compl_univ_l wh%isType_whnf.
      pose proof (redty_whnf r wh); subst.
      econstructor.
      1: eapply ihA; tea; gen_typing.
      assert [ |-[ de ] Γ',, A ≅ Γ,, A].  1:{
        econstructor; tea; eapply stability; tea. 
        eapply lrefl; now econstructor. 
      }
      eapply ihB; tea.
      do 2 constructor; boundary.
    - intros * ??? [ihA] ? [ihB] ?????? [?[?[r]]]%red_ty_compl_sig_l wh%isType_whnf.
      pose proof (redty_whnf r wh); subst.
      econstructor; tea.
      1: eapply ihA; tea; now symmetry.
      eapply ihB; tea. 
      eapply typing_subst1; tea.
      eapply TermConv; refold; [|now symmetry].
      eapply TermRefl, stability; tea.
      now econstructor.
    - intros * ? [ihA] ??? ??? r%red_ty_compl_univ_l wh%isType_whnf.
      pose proof (redty_whnf r wh); subst.
      econstructor; eapply ihA; tea; econstructor.
      econstructor; boundary.
    - intros *  ??? ??? [? [r]]%red_ty_compl_list_l wh%isType_whnf.
      pose proof (redty_whnf r wh); subst.
      econstructor.
    - intros * ? [ihhd] ? [ihtl] ?????? [? [r]]%red_ty_compl_list_l wh%isType_whnf.
      pose proof (redty_whnf r wh); subst.
      assert [Γ' |-[de] A ≅ A] by (eapply stability; tea; econstructor; now boundary).
      econstructor; [eapply ihhd|eapply ihtl]; tea; now econstructor.
    - admit.
    - intros * ? IHm HtyP ? ? ? * ? HconvN HtyA'.
      edestruct IHm as [[? []] ?] ; tea.
      unshelve eapply ty_conv_inj in HconvN.
      1: now gen_typing.
      1: assumption.
      econstructor ; tea.
      destruct HtyP, HtyA'.
      all: cbn in HconvN ; try now exfalso.
      all: now constructor.
  Qed.


  


  Let PTyEq (Γ : context) (A B : term) := True.
  Let PTyRedEq (Γ : context) (A B : term) := True.
  Let PNeEq (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    (well_typed Γ t) ->
    (well_typed Γ u) ->
    ∑ A', [Γ' |-[al] t ~ u ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    (well_typed Γ t) ->
    (well_typed Γ u) ->
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

Lemma bn_conv_conv :
  BundledConvInductionConcl
    (fun Γ A B => True)
    (fun Γ A B => True)
    (fun Γ A t u => True)
    (fun Γ A t u => True)
    (fun Γ A t u => forall B, [Γ |-[de] A ≅ B] -> [Γ |-[bn] t ≅ u : B])
    (fun Γ A t u => forall B, [Γ |-[de] A ≅ B] -> isType B -> [Γ |-[bn] t ≅h u : B]).
Proof.
  red.
  prod_splitter; try easy.
  all: intros * h ? hconv;  pose proof h as []; econstructor; tea.
  all: try now econstructor + now boundary.
  all: eapply bundled_conv_conv; tea.
  all: now eapply ctx_refl.
Qed.

(** ** Lifting of algorithmic conversion from terms at the universe to types *)

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
    - intros.
      congruence.
    - intros.
      congruence.
    - intros.
      congruence.
    - intros; congruence.
    - intros. congruence.
    - intros. congruence.
    - intros. 
      now econstructor.
  Qed.
  
End TermTypeConv.

(** ** Symmetry *)

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
      econstructor.
      all: intuition eauto.
    - intros * ? IHA ? IHB  **.
      econstructor.
      1: now intuition eauto.
      eapply IHB.
      econstructor ; tea.
      eapply IHA.
    - now econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros * ? ihA ? ihB **.
      econstructor.
      1: now eapply ihA.
      eapply ihB.
      econstructor; tea.
      now eapply ihA.
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
      eapply red_ty_compl_prod_l in Hconv as (?&?&[Hred]).
      eapply redty_red, red_whnf in Hred as ->.
      2: now eapply algo_conv_wh in IHm' as [] ; gen_typing.
      eexists ; split.
      + econstructor.
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
        econstructor.
        2: now symmetry.
        eapply stability ; tea.
        now symmetry.
    - intros * ? IHn ? IHP ? IHz ? IHs **.
      edestruct IHn as [[? [IHn' Hconv]] []] ; tea ; clear IHn.
      eapply red_ty_compl_nat_l, redty_red, red_whnf in Hconv as ->.
      2: now eapply algo_conv_wh in IHn' as [] ; gen_typing.
      eexists ; split.
      1: econstructor ; tea.
      + eapply IHP.
        econstructor ; tea.
        now do 2 econstructor.
      + eapply algo_conv_conv.
        * now eapply IHz.
        * now eapply conv_ctx_refl_r.
        * eapply stability.
          2: now symmetry.
          eapply typing_subst1.
          2: eapply IHP.
          now do 2 econstructor.
        * eapply stability.
          2: now symmetry.
          destruct IHz.
          now boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHz.
          now boundary.
      + eapply algo_conv_conv.
        * now eapply IHs.
        * now eapply conv_ctx_refl_r.
        * eapply stability.
          2: now symmetry.
          destruct IHP.
          eapply elimSuccHypTy_conv ; tea.
          now boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHs.
          boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHs.
          boundary.
      + eapply (typing_subst1 _).
        * eapply stability ; tea.
          now symmetry.
        * eapply stability.
          1: now eapply IHP.
          symmetry.
          econstructor ; tea.
          now do 2 econstructor.
    - intros * ? IHe ? IHP **.
      edestruct IHe as [[? [IHe' Hconv]] []] ; tea ; clear IHe.
      eapply red_ty_compl_empty_l, redty_whnf in Hconv as ->.
      2: now eapply algo_conv_wh in IHe' as [] ; gen_typing.
      eexists ; split.
      1: econstructor ; tea.
      + eapply IHP.
        econstructor ; tea.
        now do 2 econstructor.
      + eapply (typing_subst1 _).
        * eapply stability ; tea.
          now symmetry.
        * eapply stability.
          1: now eapply IHP.
          symmetry.
          econstructor ; tea.
          now do 2 econstructor.
    - intros * ? [ih []] ?????.
      edestruct ih as [? [hconv [?[?[r%redty_whnf]]]%red_ty_compl_sig_l]]; tea; subst.
      2: now apply algo_conv_wh in hconv as [].
      eexists; split.
      1: now econstructor.
      now symmetry.
    - intros * ? [ih []] ?????.
      edestruct ih as [? [hconv [?[?[r%redty_whnf]]]%red_ty_compl_sig_l]]; tea; subst.
      2: now apply algo_conv_wh in hconv as [].
      eexists; split.
      1: now econstructor.
      eapply typing_subst1; tea.
      eapply TermConv; refold; [|now symmetry].
      eapply stability; [now econstructor|now symmetry].
    - intros * hmap ? [ih [? ihfst ihsnd]] ? [ihtgtTy] ? [ihfn] ?????.
      set (rx := Map.extract _ _) in *.
      set (rx' := Map.extract l' l).
      exists (tList (Map.tgtTy (fst rx'))); split.
      2: unfold rx'; rewrite map_extract_sym;
        econstructor; eapply stability; tea; now symmetry.
      edestruct ih as [? [tylst [? [r]]%red_ty_compl_list_l]]; tea.
      pose proof tylst as [_ _ wh]%algo_conv_wh.
      pose proof (redty_whnf r wh); subst.
      econstructor; try rewrite map_extract_sym, (@map_extract_sym_alt l' l); tea.
      1: now rewrite orbC.
      1: eapply ihtgtTy; now symmetry.
      unshelve epose proof (extract_well_typed hmap _ _ _) as [[?%ihfst%list_ty_inj] [?%ihsnd%list_ty_inj]]; cycle 2; tea.
      assert [Γ |-[de] arr (Map.srcTy (fst rx)) (Map.tgtTy (fst rx)) ≅ arr (Map.srcTy (snd rx)) (Map.tgtTy (snd rx))]
        by now eapply convty_simple_arr.
      eapply algo_conv_conv.
      + eapply ihfn; tea.
      + etransitivity; tea; now symmetry. 
      + eapply stability; [tea|now symmetry].
      + eapply stability; [|now symmetry]; econstructor; tea; now symmetry.
      + eapply stability; [|now symmetry]; tea.
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
      pose proof Hconv' as [? []]%red_ty_complete.
      2: now eapply type_isType ; boundary.
      eexists ; split.
      + econstructor.
        * eassumption.
        * now eapply redty_red.
        * gen_typing.
      + etransitivity ; tea.
        now eapply RedConvTyC.
    - intros.
      econstructor.
      all: intuition eauto.
    - intros * ? IHA ? IHB **.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      econstructor ; tea.
      now econstructor ; intuition eauto.
    - now econstructor.
    - now econstructor.
    - intros * ? IH **.
      econstructor.
      now eapply IH.
    - now econstructor.  
    - intros * ? ? ? IH ? Hf  **.
      econstructor.
      1-2: assumption.
      eapply IH.
      econstructor ; tea.
      eapply boundary, prod_ty_inv in Hf as [].
      now econstructor.
    - intros * ? ihA ? ihB ? ihSig **.
      econstructor.
      1: now eapply ihA.
      eapply ihB; econstructor; tea.
      econstructor; now eapply ihA.
    - intros * ??? [ihFst] ? [ihSnd] ? ihp ihq **.
      econstructor; tea.
      1: now eapply ihFst.
      assert [Δ |-[ de ] B[(tFst p)..] ≅ B[(tFst q)..]]. 1:{
        eapply stability; [|now symmetry].
        eapply typing_subst1; tea.
        eapply boundary, sig_ty_inv in ihp as [].
        now econstructor.
      }
      eapply algo_conv_conv.
      * eapply ihSnd; tea.
      * eapply ctx_refl; now boundary.
      * tea.
      * eapply wfTermConv; refold.
        1: eapply stability.
        2,3: now symmetry.
        now econstructor.
      * eapply stability; [now econstructor| now symmetry].
    - now econstructor.
    - intros; econstructor.
    - intros * ? [ihhd] ? [ihtl] ? [?[[->] ?%list_ty_inj]]%termGen' [?[[->] ?%list_ty_inj]]%termGen' ? ctxconv.
      assert [Γ |-[de] A' ≅ A] by (etransitivity; tea; now symmetry).
      specialize (ihhd _ ctxconv); specialize (ihtl _ ctxconv).
      econstructor; eapply algo_conv_conv; tea.
      1,5: now eapply urefl.
      all: eapply stability; [|now symmetry];tea. 
      * now symmetry.
      * now econstructor.
      * constructor; now econstructor.
      * econstructor; tea; now econstructor. 
    - intros * ? IH  **.
      edestruct IH as [[? []] []] ; tea.
      now econstructor.
  Qed.
  
End Symmetry.

Lemma bn_conv_sym :
  BundledConvInductionConcl
    (fun Γ A B => [Γ |-[bn] B ≅ A])
    (fun Γ A B => [Γ |-[bn] B ≅h A])
    (fun Γ A t u => ∑ A', [Γ |-[bn] u ~ t ▹ A'] × [Γ |-[de] A ≅ A'])
    (fun Γ A t u => ∑ A', [Γ |-[bn] u ~h t ▹ A'] × [Γ |-[de] A ≅ A'])
    (fun Γ A t u => [Γ |-[bn] u ≅ t : A])
    (fun Γ A t u => [Γ |-[bn] u ≅h t : A]).
Proof.
  red.
  prod_splitter.
  all: intros * h; pose proof h as []; eapply algo_conv_sym in h; try now eapply ctx_refl.
  all: try now econstructor.
  all: destruct h as [A' []]; exists A'; split; tea; now econstructor.
Qed.


(** ** Transitivity *)

Lemma algo_conv_det_conv {Γ t u v A B} : 
  well_typed Γ t ->
  well_typed Γ u ->
  well_typed Γ v ->
  [Γ |-[ al ] t ~h u ▹ A] ->  
  [Γ |-[ al ] t ~h v ▹ B] ->  
  [Γ |-[de] A ≅ B].
Proof.
  intros ??? [_ h _]%algo_conv_sound [? _ _]%algo_conv_sound; tea.
  eapply h; now boundary.
Qed.

Lemma algo_conv_det_conv_alt {Γ t u v A B} : 
  well_typed Γ t ->
  well_typed Γ u ->
  well_typed Γ v ->
  [Γ |-[ al ] t ~ u ▹ A] ->  
  [Γ |-[ al ] t ~ v ▹ B] ->  
  [Γ |-[de] A ≅ B].
Proof.
  intros ??? [_ h _]%algo_conv_sound [? _ _]%algo_conv_sound; tea.
  eapply h; now boundary.
Qed.


Lemma bn_conv_det_conv {Γ Δ t u v A B} : 
  [|-[de] Γ ≅ Δ] ->
  [Γ |-[ bn ] t ~h u ▹ A] ->  
  [Δ |-[ bn ] t ~h v ▹ B] ->  
  [Γ |-[de] A ≅ B].
Proof.
  intros ctxeq h1 h.
  assert (∑ A', [× [Γ |-[ al ] t ~h v ▹ A'], [Γ |-[ de ] A' ≅ B] & isType A']) as [B' [? ? ?]]
  by now eapply bundled_conv_conv.
  pose proof h1 as ?%bn_conv_sound.
  pose proof h as ?%bn_conv_sound.
  destruct h1, h as [??? []].
  etransitivity; tea; eapply algo_conv_det_conv; cycle 3; tea.
  eexists; now eapply stability.
Qed.

Lemma bn_conv_det_conv_sym {Γ Δ t u v A B} : 
  [|-[de] Γ ≅ Δ] ->
  [Γ |-[ bn ] u ~h t ▹ A] ->  
  [Δ |-[ bn ] v ~h t ▹ B] ->  
  [Γ |-[de] A ≅ B].
Proof.
  intros ? [? [??]]%bn_conv_sym [? [??]]%bn_conv_sym.
  etransitivity; tea; etransitivity; [|eapply stability; tea; now symmetry].
  now eapply bn_conv_det_conv.
Qed.

Lemma bn_conv_det_conv_alt {Γ Δ t u v A B} : 
  [|-[de] Γ ≅ Δ] ->
  [Γ |-[ bn ] t ~ u ▹ A] ->  
  [Δ |-[ bn ] t ~ v ▹ B] ->  
  [Γ |-[de] A ≅ B].
Proof.
  intros ctxeq h1 h.
  assert (∑ A', [Γ |-[ al ] t ~ v ▹ A'] × [Γ |-[ de ] A' ≅ B]) as [B' [? ? ]]
  by now eapply bundled_conv_conv.
  pose proof h1 as ?%bn_conv_sound.
  pose proof h as ?%bn_conv_sound.
  destruct h1, h as [??? []].
  etransitivity; tea; eapply algo_conv_det_conv_alt; cycle 3; tea.
  eexists; now eapply stability.
Qed.

Lemma bn_conv_det_conv_alt_sym {Γ Δ t u v A B} : 
  [|-[de] Γ ≅ Δ] ->
  [Γ |-[ bn ] u ~ t ▹ A] ->  
  [Δ |-[ bn ] v ~ t ▹ B] ->  
  [Γ |-[de] A ≅ B].
Proof.
  intros ? [? [??]]%bn_conv_sym [? [??]]%bn_conv_sym.
  etransitivity; tea; etransitivity; [|eapply stability; tea; now symmetry].
  now eapply bn_conv_det_conv_alt.
Qed.

Lemma bun_conv_ty_len Γ A B (h : [Γ |-[bn] A ≅ B]): #|h| = #|h.(bun_conv_ty)|.
Proof. reflexivity. Qed.

Lemma bun_conv_ty_red_len Γ A B (h : [Γ |-[bn] A ≅h B]) : #|h| = #|h.(bun_conv_ty_red)|.
Proof. reflexivity. Qed.

Lemma bun_conv_tm_len Γ A t u (h : [Γ |-[bn] t ≅ u : A]) : #|h| = #|h.(bun_conv_tm)|.
Proof. reflexivity. Qed.

Lemma bun_conv_tm_red_len Γ A t u (h : [Γ |-[bn] t ≅h u : A]) : #|h| = #|h.(bun_conv_tm_red)|.
Proof. reflexivity. Qed.

Lemma bun_conv_ne_len Γ A m n (h : [Γ |-[bn] m ~ n ▹ A]) : #|h| = #|h.(bun_conv_ne)|.
Proof. reflexivity. Qed.

Lemma bun_conv_ne_red_len Γ A m n (h : [Γ |-[bn] m ~h n ▹ A]) : #|h| = #|h.(bun_conv_ne_red)|.
Proof. reflexivity. Qed.

#[global]
Hint Rewrite bun_conv_ty_len bun_conv_ty_red_len bun_conv_tm_len bun_conv_tm_red_len bun_conv_ne_len bun_conv_ne_red_len : sizeLemmas.

Tactic Notation "simpl_size" "in" hyp(H) := (autorewrite with sizeLemmas in H).

From Coq Require Import Nat Lia Arith ssreflect.

(* Helper lemma for transitivity on neutrals with a map only on the right *)
Lemma algo_conv_trans_map_r Γ Δ A A' t u v 
  (rx := (Map.extract u v)) (r := fst rx) (r' := snd rx) 
  (htu : [Γ |-[bn] t ~ u ▹ A]) :
  ~~ is_map t ->
  ~~ is_map u ->
  is_map v ->
  (* [Γ |-[al] t ~ u ▹ A] -> *)
  [|-[de] Γ ≅ Δ] ->
  [Δ |-[bn] Map.lst r ~h Map.lst r' ▹ tList A'] ->
  (forall A'' (htu' : [Γ |-[bn] t ~h u ▹ tList A'']), 
    u = Map.lst r -> 
    #|htu'| <= S #|htu| -> 
    ∑ B, [Γ |-[al] t ~h Map.lst r' ▹ B]) ->
  [Δ |-[bn] Map.tgtTy r ≅ Map.tgtTy r'] ->
  [Δ |-[bn] Map.fn r  ≅ Map.fn r' : arr (Map.srcTy r) (Map.tgtTy r)] ->
  ∑ B, [Γ |-[al] t ~ v ▹ B].
Proof.
  unfold Map.extract in rx.
  intros hmapt hmapu hmapv convctx convlst convih convty convfn.
  pose proof (is_map_compact_id hmapv) as [rv eqv].
  assert (Hx : rx = Map.combine (Map.IsNotMap u) (Map.IsMap rv)). 1:{
    now rewrite <- eqv, <- (not_is_map_compact_id hmapu).
  }
  set (ry := Map.extract t v).
  assert (Hy : ry = Map.combine (Map.IsNotMap t) (Map.IsMap rv)). 1:{
    rewrite <- eqv, <- (not_is_map_compact_id hmapt).
    now unfold ry, Map.extract.
  }
  cbn in Hx, Hy.
  unfold r', r, rx in *; clear r r' rx ; rewrite -> Hx in *; cbn in *.
  assert [Γ |-[de] A ≅ tList A'] as [T [rT]]%red_ty_compl_list_r. 1:{
    pose proof htu as [? [? ?]]%bn_conv_sym.
    etransitivity; tea.
    inv_bn convlst.
    etransitivity.
    2:{
      eapply subject_reduction_type; tea.
      eapply stability; tea.
      pose proof conv as ?%bn_conv_sound; boundary.
    }
    now eapply bn_conv_det_conv_alt.
  }
  unshelve epose proof (convih _ _ eq_refl _) as [B convih'].
  1: exact T.
  1:{ destruct htu; econstructor; tea; econstructor; tea; [apply rT|constructor]. }
  1:{ destruct htu; cbn; simpl_size; cbn; simpl_size; lia. }
  exists (tList (Map.tgtTy (fst ry))).
  pose proof convih' as [?? wh]%algo_conv_wh.
  assert [Γ |-[de] B ≅ tList A'] as [? [r]]%red_ty_compl_list_r.
  1:{
    eapply bn_conv_det_conv_sym; tea.
    destruct convlst as [??? []], htu.
    econstructor; last tea; tea.
    eexists; now eapply stability.
  }
  pose proof (redty_whnf r wh); subst.
  econstructor; fold ry; rewrite ?Hy; cbn; tea.
  + now rewrite hmapv orbT.
  + now eapply bundled_conv_conv.
  + eapply bundled_conv_conv; tea.
    eapply bn_conv_sound in convfn.
    eapply stability; tea; eapply TypeRefl; refold; boundary.
Qed.

(* Helper lemma for transitivity on neutrals with a map only on the left *)
Lemma algo_conv_trans_map_l Γ Δ A A' v u t 
  (rx := (Map.extract v u)) (r := fst rx) (r' := snd rx) 
  (htu : [Δ |-[bn] u ~ t ▹ A]) :
  ~~ is_map t ->
  ~~ is_map u ->
  is_map v ->
  (* [Γ |-[al] t ~ u ▹ A] -> *)
  [|-[de] Γ ≅ Δ] ->
  [Γ |-[bn] Map.lst r ~h Map.lst r' ▹ tList A'] ->
  (forall A'' (htu' : [Δ |-[bn] u ~h t ▹ tList A'']), 
    u = Map.lst r' -> 
    #|htu'| <= S #|htu| -> 
    ∑ B, [Γ |-[al] Map.lst r ~h t ▹ B]) ->
  [Γ |-[bn] Map.tgtTy r ≅ Map.tgtTy r'] ->
  [Γ |-[bn] Map.fn r  ≅ Map.fn r' : arr (Map.srcTy r) (Map.tgtTy r)] ->
  ∑ B, [Γ |-[al] v ~ t ▹ B].
Proof.
  unfold Map.extract in rx.
  intros hmapt hmapu hmapv convctx convlst convih convty convfn.
  pose proof (is_map_compact_id hmapv) as [rv eqv].
  assert (Hx : rx = Map.combine (Map.IsMap rv) (Map.IsNotMap u)). 1:{
    now rewrite <- eqv, <- (not_is_map_compact_id hmapu).
  }
  set (ry := Map.extract v t).
  assert (Hy : ry = Map.combine (Map.IsMap rv) (Map.IsNotMap t)). 1:{
    rewrite <- eqv, <- (not_is_map_compact_id hmapt).
    now unfold ry, Map.extract.
  }
  cbn in Hx, Hy.
  unfold r', r, rx in *; clear r r' rx ; rewrite -> Hx in *; cbn in *.
  assert [Γ |-[de] A ≅ tList A'] as [T [rT]]%red_ty_compl_list_r. 1:{
    pose proof htu as [? [? ?]]%bn_conv_sym.
    etransitivity; [now eapply stability|].
    inv_bn convlst.
    etransitivity.
    2:{
      eapply subject_reduction_type; tea.
      pose proof conv as ?%bn_conv_sound; boundary.
    }
    symmetry; now eapply bn_conv_det_conv_alt_sym.
  }
  unshelve epose proof (convih _ _ eq_refl _) as [B convih'].
  1: exact T.
  1:{ destruct htu; econstructor; tea; econstructor; tea; [apply rT|constructor]. }
  1:{ destruct htu; cbn; simpl_size; cbn; simpl_size; lia. }
  exists (tList (Map.tgtTy (fst ry))).
  pose proof convih' as [?? wh]%algo_conv_wh.
  assert [Γ |-[de] B ≅ tList A'] as [? [r]]%red_ty_compl_list_r.
  1:{
    destruct convlst.
    eapply algo_conv_det_conv; cycle 3; tea.
    pose proof htu as ?%bn_conv_sound.
    eexists. eapply stability; tea; boundary.
  }
  pose proof (redty_whnf r wh); subst.
  econstructor; fold ry; rewrite ?Hy; cbn; tea.
  + now rewrite hmapv.
  + now destruct convty.
  + now destruct convfn.
Qed.


From Equations Require Import Equations.

Ltac inv_bn H :=
  match type of H with
  | [_ |-[bn] _ ≅ _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ty_inv H); depelim h; destruct H; cbn in *; subst
  | [_ |-[bn] _ ≅h _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ty_red_inv H); depelim h; destruct H; cbn in *; subst 
  | [_ |-[bn] _ ~ _ ▹ _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ne_inv H); depelim h; destruct H; cbn -[Map.extract] in *; subst
  | [_ |-[bn] _ ~h _ ▹ _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ne_red_inv H); depelim h; destruct H; cbn in *; subst 
  | [_ |-[bn] _ ≅ _ : _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_tm_inv H); depelim h; destruct H; cbn in *; subst
  | [_ |-[bn] _ ≅h _ : _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_tm_red_inv H); depelim h; destruct H; cbn in *; subst
  end.

Lemma extract_lst_threesome {t u v} 
  (rtu := Map.extract t u)
  (ruv := Map.extract u v)
  (rtv := Map.extract t v) :
  is_map t || is_map u ->
  is_map u || is_map v ->
  is_map t || is_map v ->
  [× Map.lst (fst rtu) = Map.lst (fst rtv),
     Map.lst (snd rtu) = Map.lst (fst ruv)&
     Map.lst (snd rtv) = Map.lst (snd ruv)].
Proof.
  destruct (is_map t) eqn:hmapt, (is_map u) eqn:hmapu, (is_map v) eqn:hmapv; cbn; try discriminate.
  all: intros _ _ _.
  all: unfold rtu, ruv, rtv, Map.extract.
  all: repeat match goal with
    | H : _ = false |- _ => eapply negbT, not_is_map_compact_id in H; rewrite H
    | H : _ = true |- _ => eapply is_map_compact_id in H as [? ->]
    end. 
  all: cbn in *; split; reflexivity.
Qed.

Section Transitivity.

  Let PTyEq (n : nat) :=
    forall Γ Δ A B C
      (hΓ : [|- Γ ≅ Δ])
      (hA : [Γ |-[bn] A ≅ B])
      (hB : [Δ |-[bn] B ≅ C]),
      #|hA| + #|hB| <= n ->
      [Γ |-[al] A ≅ C].

  Let PTyRedEq (n : nat) :=
    forall Γ Δ A B C
      (hΓ : [|- Γ ≅ Δ])
      (hA : [Γ |-[bn] A ≅h B])
      (hB : [Δ |-[bn] B ≅h C]),
      #|hA| + #|hB| <= n ->
      [Γ |-[al] A ≅h C].

  Let PNeEq (n : nat) :=
    forall Γ Δ A B t u v
      (hΓ : [|- Γ ≅ Δ])
      (ht : [Γ |-[bn] t ~ u ▹ A])
      (hu : [Δ |-[bn] u ~ v ▹ B]),
      #|ht| + #|hu| <= n ->
      ∑ C, [Γ |-[al] t ~ v ▹ C].

  Let PNeRedEq (n : nat) :=
    forall Γ Δ A B t u u' v
      (hΓ : [|- Γ ≅ Δ])
      (ht : [Γ |-[bn] t ~h u ▹ A])
      (hu : [Δ |-[bn] u' ~h v ▹ B]),
      u = u' ->
      #|ht| + #|hu| <= n ->
      ∑ C, [Γ |-[al] t ~h v ▹ C].
  
  Let PTmEq (n : nat) :=
    forall Γ Δ A B t u v
      (hΓ : [|- Γ ≅ Δ])
      (hAB : [Γ |-[de] A ≅ B])
      (ht : [Γ |-[bn] t ≅ u : A])
      (hu : [Δ |-[bn] u ≅ v : B]),
      #|ht| + #|hu| <= n ->
      [Γ |-[al] t ≅ v : A].

  Let PTmRedEq (n : nat) :=
    forall Γ Δ A B t u v
      (hΓ : [|- Γ ≅ Δ])
      (hAB : [Γ |-[de] A ≅ B])
      (ht : [Γ |-[bn] t ≅h u : A])
      (hu : [Δ |-[bn] u ≅h v : B]),
      #|ht| + #|hu| <= n ->
      [Γ |-[al] t ≅h v : A].

  Let transStmt (n : nat) :=
    PTyEq n × PTyRedEq n × PNeEq n × PNeRedEq n × PTmEq n × PTmRedEq n.

  Section TransitivityInductiveSteps.
    Context (n : nat) (ih : forall m, m < n -> transStmt m).

    Arguments bun_conv_ty_sized /.
    Arguments bun_conv_ty_red_sized /.
    Arguments bun_conv_ne_sized /.

    Derive Signature for ConvTypeBunAlg.
    Derive Signature for ConvTypeRedBunAlg.
    #[local]
    Lemma transTyEq : PTyEq n.
    Proof.
      intros ?????? hA hB hn; simpl_size in hn. 
      inv_bn hA; inv_bn hB.
      assert (A'0 = B'); subst. 1:{
        clear hn.
        destruct conv as [???? ?%isType_whnf], conv0 as [?? ?%isType_whnf].
        now eapply whred_det.
      }
      econstructor; refold; tea.
      unshelve eapply ih.
      8: reflexivity.
      3,4, 6: tea.
      revert hn; simpl_size; lia.
    Qed.
    
    #[local]
    Lemma transTyRedEq : PTyRedEq n.
    Proof.
      red. intros ?????? hA hB hn; simpl_size in hn.
      inv_bn hA.
      7:{
          inv_bn hB.
          1-6: destruct inf as [???? e]; inversion e.
          enough (∑ X, [Γ |-[al] A ~ C ▹ X]) as []
          by now econstructor.
          unshelve eapply ih.
          10: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; lia.
      }
      1-6: inv_bn hB; [|destruct inf as [?? e]; inversion e].
      2-4: now econstructor.
      - econstructor; refold.
        + unshelve eapply ih.
          8: reflexivity.
          3,4,6: tea.
          revert hn; simpl_size; lia.
        + unshelve eapply ih. 8: reflexivity.
          3,4: tea.
          1: revert hn; simpl_size; lia.
          econstructor; tea.
          now pose proof convA as ?%bn_conv_sound.
      - econstructor; refold.
        + unshelve eapply ih.
          8: reflexivity.
          3,4,6: tea.
          revert hn; simpl_size; lia.
        + unshelve eapply ih. 8: reflexivity.
          3,4: tea.
          1: revert hn; simpl_size; lia.
          econstructor; tea.
          now pose proof convA as ?%bn_conv_sound.
      - econstructor; refold.
        unshelve eapply ih. 8: reflexivity.
        3,4,6: tea.
        revert hn; simpl_size; lia.
    Qed.

    #[local]
    Lemma transNeuEq : PNeEq n.
    Proof.
      red; intros * hΓ ht hu hn; simpl_size in hn.
      inv_bn ht.
      1-6: inv_bn hu.
      - eexists; now econstructor.
      - assert (∑ B, [× [Γ |-[al] Map.lst r ~h Map.lst r' ▹ B], [Γ |-[de] B ≅ tList A0] & isType B])
        as [? [? _ _]] by now eapply bundled_conv_conv.
        eapply algo_conv_trans_map_r; tea.
        1,2: cbn; try easy.
        intros ?? eq ?; eexists; now rewrite {1}eq.
        Unshelve. 2: econstructor; tea; now econstructor.
      - pose proof convFun as [? [convnm hprod1]]%bn_conv_sym.
        assert [Γ |-[de] tProd A0 B0 ≅ tProd A B1] as []%prod_ty_inj.
        1: etransitivity; tea; eapply bn_conv_det_conv; tea.
        assert (∑ C, [Γ |-[al] m ~h n1 ▹ C]) as [T convmn1]. 1:{
          unshelve eapply ih. 11,12: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; lia.
        }
        assert (HmnT : [Γ |-[bn] m ~h n1 ▹ T]).
        1:{
          pose proof convmn1 as []%algo_conv_wh; econstructor; tea; eexists; try boundary.
          1: pose proof convFun as ?%bn_conv_sound; boundary.
          pose proof convFun0 as ?%bn_conv_sound;
          eapply stability ; tea; boundary.
        }
        assert [Γ |-[de] tProd A0 B0 ≅ T] as [? [? [r]]]%red_ty_compl_prod_l.
        1: eapply bn_conv_det_conv; cycle 1; tea; now eapply ctx_refl.
        destruct HmnT as [????? h']; inversion h'; subst; refold.
        unshelve epose proof (redty_whnf r _); tea; subst.
        eexists; econstructor; refold; tea.
        eapply algo_conv_conv.
        3: now symmetry.
        1:{
          unshelve eapply ih. 10: reflexivity.
          4,5,7: tea.
          2: now symmetry.
          revert hn; simpl_size; lia.
        }
        1: now eapply ctx_refl.
        1: pose proof convArg as ?%bn_conv_sound; now boundary.
        pose proof convArg0 as ?%bn_conv_sound.
        econstructor; refold; [eapply stability; tea; now boundary|tea].
      - eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        intros ? htu' eq ?.
        unshelve eapply ih. 12: reflexivity.
        5,7,9,10: tea.
        Unshelve. 3:{ econstructor; tea; set (x := neuAppCongAlg _ _) in hn; exact x. }
        revert hn H ; simpl_size; cbn; simpl_size.
        set (x:= #|_|); set (y := #|_|); set (z := #|_|); set (w := #|_|).
        set (a := #|_|); set (b := #|_|).
        assert (1 <= z) by apply size_positive. 
        assert (1 <= w) by apply size_positive.
        intros. lia.
      - assert (∑ C, [Γ |-[al] n0 ~h n'0 ▹ C]) as [T hconv].
        1:{
          unshelve eapply ih. 11,12: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; lia.
        }
        pose proof convn0 as ?%bn_conv_sound.
        assert [Γ |-[de] T ≅ tNat] as r%red_ty_compl_nat_r.
        1: destruct convn; eapply algo_conv_det_conv; cycle 3; tea; eexists; (eapply stability; tea; boundary).
        pose proof hconv as [?? wh]%algo_conv_wh.
        pose proof (redty_whnf r wh); subst.
        eexists; econstructor; refold; tea.
        + unshelve eapply ih. 8: reflexivity.
          3,4,6: tea.
          1: econstructor; tea; gen_typing.
          revert hn; simpl_size; lia.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea. 
          2:{ pose proof convP as ?%bn_conv_sound; eapply typing_subst1; tea; gen_typing. }
          revert hn; simpl_size; lia.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea.
          2:{ pose proof convP as ?%bn_conv_sound; eapply elimSuccHypTy_conv; tea; boundary. }
          revert hn; simpl_size; lia.
      - eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        intros ? htu' eq H.
        unshelve eapply ih. 12: reflexivity.
        5,7,9,10: tea.
        Unshelve. 3:{ econstructor; tea; set (x := neuNatElimCong _ _ _ _) in hn; exact x. }
        revert hn H; simpl_size; cbn; simpl_size. 
        repeat let h := fresh "x" in set (h := #|_|).
        assert (1 <= x3) by apply size_positive. 
        assert (1 <= x4) by apply size_positive.
        lia.
      - assert (∑ C, [Γ |-[al] e ~h e'0 ▹ C]) as [T hconv]. 1:{
          unshelve eapply ih. 11,12: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; lia.
        } 
        pose proof conve0 as ?%bn_conv_sound.
        assert [Γ |-[de] T ≅ tEmpty] as r%red_ty_compl_empty_r.
        1: destruct conve; eapply algo_conv_det_conv; cycle 3; tea; eexists; (eapply stability; tea; boundary).
        pose proof hconv as [?? wh]%algo_conv_wh.
        pose proof (redty_whnf r wh); subst.
        eexists; econstructor ; tea; refold.
        unshelve eapply ih. 8: reflexivity.
        3,4: tea.
        2: econstructor ; tea; gen_typing.
        revert hn; simpl_size; lia.
      - eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        intros ? htu' eq H.
        unshelve eapply ih. 12: reflexivity.
        5,7,9,10: tea.
        Unshelve. 3:{ econstructor; tea; set (x := neuEmptyElimCong _ _) in hn; exact x. }
        revert hn H; simpl_size; cbn; simpl_size. 
        repeat let h := fresh "x" in set (h := #|_|).
        assert (1 <= x1) by apply size_positive. 
        assert (1 <= x2) by apply size_positive.
        lia.
      - assert (∑ C, [Γ |-[al] m ~h n1 ▹ C]) as [T hconv]. 1:{
          unshelve eapply ih. 11,12: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; lia.
        }
        pose proof convm0 as ?%bn_conv_sound.
        assert [Γ |-[de] T ≅ tSig A B0] as [? [? [r]]]%red_ty_compl_sig_r.
        1: destruct convm; eapply algo_conv_det_conv; cycle 3; tea; eexists; (eapply stability; tea; boundary).
        pose proof hconv as [?? wh]%algo_conv_wh.
        pose proof (redty_whnf r wh); subst.
        eexists; now econstructor.
      - eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        intros ? htu' eq H.
        unshelve eapply ih. 12: reflexivity.
        5,7,9,10: tea.
        Unshelve. 3:{ econstructor; tea; set (x := neuFstCongAlg _) in hn; exact x. }
        revert hn H; simpl_size; cbn; simpl_size. 
        repeat let h := fresh "x" in set (h := #|_|).
        assert (1 <= x0) by apply size_positive. 
        assert (1 <= x1) by apply size_positive.
        lia.
      - assert (∑ C, [Γ |-[al] m ~h n1 ▹ C]) as [T hconv]. 1:{
          unshelve eapply ih. 11,12: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; lia.
        }
        pose proof convm0 as ?%bn_conv_sound.
        assert [Γ |-[de] T ≅ tSig A0 B0] as [? [? [r]]]%red_ty_compl_sig_r.
        1: destruct convm; eapply algo_conv_det_conv; cycle 3; tea; eexists; (eapply stability; tea; boundary).
        pose proof hconv as [?? wh]%algo_conv_wh.
        pose proof (redty_whnf r wh); subst.
        eexists; now econstructor.
      - eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        intros ? htu' eq H.
        unshelve eapply ih. 12: reflexivity.
        5,7,9,10: tea.
        Unshelve. 3:{ econstructor; tea; set (x := neuSndCongAlg _) in hn; exact x. }
        revert hn H; simpl_size; cbn; simpl_size. 
        repeat let h := fresh "x" in set (h := #|_|).
        assert (1 <= x0) by apply size_positive. 
        assert (1 <= x1) by apply size_positive.
        lia.
      - case hmaptuv: (~~is_map l && is_map l' && ~~ is_map v); last case hmapuv: (is_map l' || is_map v).
        + move: hmaptuv=> /andP-[/andP-[hmapt hmapu] hmapv].
          inv_bn hu; try discriminate hmapu.
          case: (is_not_map_extract hmapu (negbTE hmapv))=> <- _ _.
          case: (is_not_map_extract hmapu (negbTE hmapt))=> <- _ _.
          rewrite (@map_extract_sym l'0).
          enough (∑ C, [Γ|-[al] Map.lst r ~h Map.lst r'0 ▹ C]) as [? hconv].
          by (inversion hconv; now eexists).
          unfold r, r', rx, r0, r'0, rx0 in *.
          unshelve eapply ih; last reflexivity.
          5,7,9: tea.
          2:{ 
            eapply is_map_compact_id in hmapu as [? equ]. 
            eapply not_is_map_compact_id in hmapt. 
            eapply not_is_map_compact_id in hmapv.
            now rewrite /Map.extract hmapt equ hmapv.
          }
          revert hn; simpl_size; lia.
        + inv_bn hu; try discriminate hmapuv.
          have hmap1: is_map l || is_map l'0 
          by move: {hn}hmap hmaptuv hmapuv; (do 3 case: (is_map _))=> //=.
          have [eqt equ eqv]:= (extract_lst_threesome hmap hmap0 hmap1).
          pose (rx1 := Map.extract l l'0).
          exists (tList (Map.tgtTy (fst rx1))).
          assert (∑ C, [Γ |-[al] Map.lst (fst rx) ~h Map.lst (snd rx0) ▹ C]) as [T hconv]. 1:{
            unshelve eapply ih. 12: reflexivity.
            5,7,9: tea.
            2: apply equ.
            revert hn; simpl_size.
            repeat let h := fresh "x" in set (h := #|_|).
            lia. 
          }
          assert [Γ |-[de] T ≅ tList A0] as [? [rT]]%red_ty_compl_list_r.  1:{
            destruct convlst; unfold r in *.
            pose proof convlst0 as ?%bn_conv_sound.
            eapply algo_conv_det_conv; cycle 3;  tea.
            eexists; eapply stability; tea; boundary.
          }
          pose proof hconv as [_ _ wh]%algo_conv_wh.
          pose proof (redty_whnf rT wh); subst.
          econstructor; refold; tea.
          * now rewrite <- eqt, eqv.
          * move: (hmap) (hmap0) hmaptuv hmap1;
             unfold r, r', rx, r0, r'0, rx0, Map.extract in *.
             clear hn.
            (do 3 (let h:= fresh "E" in case h: (is_map _)))=> //= _ _ _ _.
            all: repeat match goal with
                | H : is_map _ = false |- _ => eapply negbT, not_is_map_compact_id in H; rewrite -> H in *
                | H : is_map _ = true |- _ => let H' := fresh "H" in eapply is_map_compact_id in H as [? H']; rewrite -> H' in *
                end.
            all: cbn in *.
            1: destruct convtgtty.
            rewrite H in convlst0. 
          
          admit.
          * admit.
        + move: hmapuv (hmap)=> /negbT /norP-[/[dup] hmapu /negbTE->] hmapv /=.
          rewrite orbF=> hmapt.
          eapply algo_conv_trans_map_l=> //; first exact hmapu; tea.
          intros ? htu' eq H.
          unshelve eapply ih; last reflexivity.
          5,7,9: tea.
          2: symmetry; exact eq.
          Unshelve. 3: tea.
          revert hn H; simpl_size; repeat let h := fresh "x" in set (h := #|_|).
          have: 1 <= x0 by apply size_positive. 
          have: 1 <= x by apply size_positive. 
          lia. 
      admit.
    Admitted.
    (* Qed. *)

    #[local]
    Lemma transNeuRedEq : PNeRedEq n.
    Proof.
      red; intros * hΓ ht hu eq hn.
      inv_bn ht; inv_bn hu.
      assert (∑ C, [Γ |-[al] t ~ v ▹ C]) as [T hconv]. 1:{
        unshelve eapply ih. 10: reflexivity.
        4,6,8: tea.
        revert hn; simpl_size; cbn; simpl_size; lia.
      }
      assert [Γ |-[de] A0 ≅ T].
      1:{ 
        pose proof conv0 as ?%bn_conv_sound; destruct conv.
        eapply algo_conv_det_conv_alt; cycle 3; tea. 
        eexists; eapply stability; tea; boundary.
      }
      assert (WN T) as [T0] by (eapply typing_nf_alt; exists istype; boundary).
      exists T0; now econstructor.
    Qed.

    #[local]
    Lemma transTmEq : PTmEq n.
    Proof.
      red; intros * hΓ hAB ht hu hn.
      inv_bn ht; inv_bn hu.
      unshelve epose proof (whred_det _ _ _ _ _ redu _); cycle 3; tea; subst.
      2,3: now destruct conv, conv0.
      econstructor ; tea; refold.
      unshelve eapply ih. 10: reflexivity.
      4,5,7: tea.
      1: revert hn; simpl_size; cbn; simpl_size; lia.
      etransitivity; [symmetry |etransitivity; tea].
      all: eapply subject_reduction_type; boundary.
    Qed.

    #[local]
    Lemma transTmRedEq : PTmRedEq n.
    Proof.
      red; intros * hΓ hAB ht hu hn.
      inv_bn ht.
      - assert (Hdiscr : B = U).  1:{
          destruct hu.
          eapply red_whnf; [|gen_typing].
          now eapply red_ty_compl_univ_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        econstructor; refold.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea. 2: gen_typing.
          revert hn; simpl_size; cbn; simpl_size; lia.
        + unshelve eapply ih. 10: reflexivity.
          4,5: tea. 
          3: pose proof convB as ?%bn_conv_sound; do 2 econstructor; refold; boundary. 
          2: pose proof convA as ?%bn_conv_sound; econstructor; tea; gen_typing.
          revert hn; simpl_size; cbn; simpl_size; lia.
      - assert (Hdiscr: B = U).  1:{
          destruct hu.
          eapply red_whnf; [| gen_typing].
          now eapply red_ty_compl_univ_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        now econstructor.
      - assert (Hdiscr: B = tNat). 1:{
          destruct hu; eapply red_whnf.
          2: gen_typing.
          now eapply red_ty_compl_nat_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        now econstructor.
      - assert (Hdiscr: B = tNat). 1:{
          destruct hu; eapply red_whnf.
          2: gen_typing.
          now eapply red_ty_compl_nat_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        econstructor; refold.
        unshelve eapply ih. 10: reflexivity.
        4,5,7: tea. 2: gen_typing.
        revert hn; simpl_size; cbn; simpl_size; lia.
      - assert (Hdiscr: B = U).  1:{
          destruct hu.
          eapply red_whnf; [| gen_typing].
          now eapply red_ty_compl_univ_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        now econstructor.
      - inv_bn hu.
        all: try match goal with H : isPosType _ |- _ => destruct H end.
        all: try solve [now unshelve eapply ty_conv_inj in hAB ; [econstructor | econstructor | cbn in *]].
        eapply prod_ty_inj in hAB as [].
        econstructor ; tea; refold.
        unshelve eapply ih. 10: reflexivity.
        4,5,7: tea.
        3: eapply stability1; cycle 2; tea; try boundary; now symmetry.
        1: econstructor; tea; now symmetry.
        revert hn; simpl_size; cbn; simpl_size; lia.
      - assert (Hdiscr : B = U).  1:{
          destruct hu.
          eapply red_whnf; [|gen_typing].
          now eapply red_ty_compl_univ_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        econstructor; refold.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea. 2: gen_typing.
          revert hn; simpl_size; cbn; simpl_size; lia.
        + unshelve eapply ih. 10: reflexivity.
          4,5: tea. 
          3: pose proof convB as ?%bn_conv_sound; do 2 econstructor; refold; boundary. 
          2: pose proof convA as ?%bn_conv_sound; econstructor; tea; gen_typing.
          revert hn; simpl_size; cbn; simpl_size; lia.
      - inv_bn hu.
        all: try match goal with H : isPosType _ |- _ => destruct H end.
        all: try solve [now unshelve eapply ty_conv_inj in hAB ; [econstructor | econstructor | cbn in *]].
        eapply sig_ty_inj in hAB as [].
        econstructor ; tea; refold.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea. 2: now symmetry.
          revert hn; simpl_size; cbn; simpl_size; lia.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea. 
          2: epose proof convfst as ?%bn_conv_sound; eapply typing_subst1; tea; eapply stability1; cycle 2;  tea; try boundary; now symmetry.
          revert hn; simpl_size; cbn; simpl_size; lia.
      - assert (Hdiscr : B = U).  1:{
          destruct hu.
          eapply red_whnf; [|gen_typing].
          now eapply red_ty_compl_univ_l, redty_red in hAB.
        }
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        econstructor; refold.
        unshelve eapply ih. 10: reflexivity.
        4,5,7: tea. 2: gen_typing.
        revert hn; simpl_size; cbn; simpl_size; lia.
      - pose proof hAB as [? [r ?]]%red_ty_compl_list_l.
        pose proof hu as [_ _ wh%isType_whnf].
        pose proof (Hdiscr:= red_whnf _ _ (redty_red r) wh).
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        econstructor.
      - pose proof hAB as [? [r ?]]%red_ty_compl_list_l.
        pose proof hu as [_ _ wh%isType_whnf].
        pose proof (Hdiscr:= red_whnf _ _ (redty_red r) wh).
        inv_bn hu; try solve [inversion Hdiscr| destruct inf as [?? e]; inversion e]; clear Hdiscr.
        assert [Γ |-[de] A0 ≅ A']. 1:{
          pose proof hAB as ?%list_ty_inj.
          pose proof bun_conv_tm_red_l as [? [[->] ?%list_ty_inj]]%termGen'.
          pose proof bun_conv_tm_red_l1 as [? [[->] ?%list_ty_inj]]%termGen'.
          etransitivity; [|now eapply stability].
          symmetry; now etransitivity.
        }
        econstructor; refold.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7,8: tea.
          revert hn; simpl_size; cbn; simpl_size; lia.
        + unshelve eapply ih. 10: reflexivity.
          4,5,7: tea. 2: now econstructor.
          revert hn; simpl_size; cbn; simpl_size; lia.
      - inv_bn hu; try solve [ destruct inf as []; inv_whne].
        1,2: destruct ispos; (unshelve eapply ty_conv_inj in hAB; [now econstructor | now econstructor | cbn in *; inversion hAB]).
        assert (∑ C, [Γ |-[al] t ~ v ▹ C]) as [??]. 1:{
          unshelve eapply ih. 10: reflexivity.
          4,6,8: tea.
          revert hn; simpl_size; cbn; simpl_size; lia.
        }
        now econstructor.
    Qed.

  End TransitivityInductiveSteps.

  #[local]
  Lemma trans_aux : forall n, transStmt n.
    intro n; apply lt_wf_rect; clear n.
    cbn; intros n ih; repeat split.
    - now apply transTyEq.
    - now apply transTyRedEq.
    - now apply transNeuEq.
    - now apply transNeuRedEq.
    - now apply transTmEq.
    - now apply transTmRedEq.
  Qed.

  Let QTyEq (Γ : context) (A B : term) := forall Δ C,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[bn] B ≅ C] ->
    [Γ |-[al] A ≅ C].
  Let QTyRedEq (Γ : context) (A B : term) := forall Δ C,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[bn] B ≅h C] ->
    [Γ |-[al] A ≅h C].
  Let QNeEq (Γ : context) (A t u : term) := forall Δ v A',
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[bn] u ~ v ▹ A'] ->
    ∑ B, [Γ |-[al] t ~ v ▹ B].
  Let QNeRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[bn] u ~h v ▹ A'] ->
    ∑ B, [Γ |-[al] t ~h v ▹ B].
  Let QTmEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Γ |-[de] A' ≅ A] ->
    [Δ |-[bn] u ≅ v : A'] ->
    [Γ |-[al] t ≅ v : A].
  Let QTmRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Γ |-[de] A' ≅ A] ->
    [Δ |-[bn] u ≅h v : A'] ->
    [Γ |-[al] t ≅h v : A].

  Theorem algo_conv_trans :
    BundledConvInductionConcl QTyEq QTyRedEq QNeEq QNeRedEq QTmEq QTmRedEq.
  Proof.
    subst QTyEq QTyRedEq QNeEq QNeRedEq QTmEq QTmRedEq.
    red; prod_splitter; intros; eapply trans_aux; try reflexivity; tea; now symmetry.
    Unshelve.
    all: try match goal with |- context [bn] => tea end.
  Qed.

End Transitivity.


Section Transitivity.

  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction.
    - intros ? ? ? ? B' ? ? Hconv IH ? ? ? * ? Hconv'.
      inv_bn Hconv'.
      assert (A'0 = B') as ->.
      {
        eapply whred_det ; tea.
        - destruct conv; now eapply isType_whnf.
        - eapply algo_conv_wh in Hconv as [] ; gen_typing. 
      }
      econstructor ; tea.
      eapply IH ; tea.
    - intros * ? [IHA ] ? IHB ? ? ? * ? Hconv.
      inv_bn Hconv.
      2: destruct inf as [_ _ e _ _ _]; inversion e.
      econstructor.
      + eapply IHA ; tea.
      + eapply IHB ; tea.
        now econstructor.
    - intros * ? ? _ * ? Hconv.
      inv_bn Hconv.
      2: destruct inf as [?? e]; inversion e. 
      now constructor.
    - intros * ? ? _ * ? Hconv.
      inv_bn Hconv.
      1: now constructor.
      destruct inf as [?? e]; inversion e.
    - intros * ? ? _ * ? hconv.
      inv_bn hconv.
      2:{ destruct inf as [?? e]; now inversion e. }
      now constructor.
    - intros * ? [IHA ] ? IHB ? ? ? * ? Hconv.
      inv_bn Hconv.
      2: destruct inf as [?? e]; inversion e.
      econstructor.
      + eapply IHA ; tea.
      + eapply IHB ; tea.
        now econstructor.
    - intros * ? [ih ] _ * ? ???? hconv.
      inv_bn hconv.
      2:{ destruct inf as [?? e]; now inversion e. }
      econstructor; refold; now eapply ih.
    - intros * ? [IH] ? ? ? * ? Hconv.
      inv_bn Hconv.
      1-6: apply algo_conv_wh in H as [_ e] ; now inversion e.
      edestruct IH as [?]; tea.
      now econstructor.
    - intros * Hin ? _ _ * ? Hconv.
      inv_bn Hconv.
      (** Need to find a generic solution for this case and the following ones *)
      2:{
        assert (∑ B, [× [Γ |-[al] Map.lst r ~h Map.lst r' ▹ B], [Γ |-[de] B ≅ tList A] & isType B])
        as [? [? _ _]] by now eapply bundled_conv_conv.
        eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        1: eexists; now econstructor.
        unshelve epose proof (@is_not_map_extract (tRel n) v _ _) as [eq]; tea; try easy.
        now rewrite <- eq at 1.
      }
      exists decl.
      now econstructor.
      (* + eapply in_ctx_conv_l in Hin as [? [Hin ]]; tea. 
        etransitivity; tea; now symmetry.
      + eapply in_ctx_conv_l in Hin as [? [Hin ]]; tea.
        eapply in_ctx_inj in Hin.
        2: clear Hin ; tea.
        now subst. *)
    - intros * ? [IHm []] ? [IHt] ? ? ? * ? Hconv.
      inv_bn Hconv.
      2:{
        eapply algo_conv_trans_map_r; tea.
        1,2: cbn; easy.
        1: eexists; now econstructor.

      } admit; cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      assert (h : [Γ |-[bn] m ~h n ▹ tProd A B]). 
      1: pose proof H as []%algo_conv_wh; econstructor; tea; eexists; boundary.
      pose proof h as [? [convnm hprod1]]%bn_conv_sym.
      assert [Γ |-[de] tProd A B ≅ tProd A0 B0] as []%prod_ty_inj.
      1: etransitivity; tea; eapply bn_conv_det_conv; tea.
      edestruct IHm as [T convmn0]; tea.
      assert [Γ |-[bn] m ~h n0 ▹ T].
      1:{
        pose proof convmn0 as []%algo_conv_wh; econstructor; tea; eexists; try boundary.
        eapply bn_conv_sound in convFun; eapply stability ; tea; boundary.
      }
      assert [Γ |-[de] tProd A B ≅ T] as [? [? [r]]]%red_ty_compl_prod_l.
      1: eapply bn_conv_det_conv; cycle 1; tea; now eapply ctx_refl.
      destruct H5 as [????? h']; inversion h'; subst; refold.
      unshelve epose proof (redty_whnf r _); tea; subst.
      eexists; econstructor; refold; tea.
      eapply algo_conv_conv.
      3: now symmetry.
      1: eapply IHt; tea.
      2: now eapply ctx_refl.
      2: now boundary.
      2: econstructor; refold.
      2: eapply stability; tea; eapply bn_conv_sound in convArg; boundary.
      2: tea.
      eapply bn_conv_conv; tea.
      eapply stability; [|now symmetry].
      etransitivity; tea;  now symmetry.
    - intros * ? [IHn[]] ? IHP ? IHz ? IHs ? ? ? * ? Hconv.
      inv_bn Hconv.
      2: admit; cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      edestruct IHn as [T hconv]; tea.
      pose proof convn as ?%bn_conv_sound.
      assert [Γ |-[de] T ≅ tNat] as r%red_ty_compl_nat_r.
      1: eapply algo_conv_det_conv; cycle 3; tea; eexists; boundary + (eapply stability; tea; boundary).
      pose proof hconv as [?? wh]%algo_conv_wh.
      pose proof (redty_whnf r wh); subst.
      eexists; econstructor; refold; tea.
      * eapply IHP ; tea.
        econstructor ; tea.
        now do 2 econstructor.
      * eapply IHz ; tea.
        symmetry.
        eapply typing_subst1.
        2: eapply IHP.
        now do 2 econstructor.
      * eapply IHs ; tea.
        symmetry.
        destruct IHP.
        eapply elimSuccHypTy_conv ; tea.
        now boundary.
    - intros * ? [IHe []] ? IHP ? ? ? ? * ? Hconv.
      inv_bn Hconv.
      2: admit; cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      edestruct IHe as [T hconv]; tea.
      pose proof conve as ?%bn_conv_sound.
      assert [Γ |-[de] T ≅ tEmpty] as r%red_ty_compl_empty_r.
      1: eapply algo_conv_det_conv; cycle 3; tea; eexists; boundary + (eapply stability; tea; boundary).
      pose proof hconv as [?? wh]%algo_conv_wh.
      pose proof (redty_whnf r wh); subst.
      eexists; econstructor ; tea.
      eapply IHP ; tea.
      econstructor ; tea.
      now do 2 econstructor.
    - intros * ? [ih []] ??????? hconv.
      inv_bn hconv.
      2: admit; cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      edestruct ih as [T hconv]; tea.
      pose proof convm as ?%bn_conv_sound.
      assert [Γ |-[de] T ≅ tSig A B] as [? [? [r]]]%red_ty_compl_sig_r.
      1: eapply algo_conv_det_conv; cycle 3; tea; eexists; boundary + (eapply stability; tea; boundary).
      pose proof hconv as [?? wh]%algo_conv_wh.
      pose proof (redty_whnf r wh); subst.
      eexists; now econstructor.
    - intros * ? [ih []] ??????? hconv.
      inv_bn hconv.
      2: admit; cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      edestruct ih as [T hconv]; tea.
      pose proof convm as ?%bn_conv_sound.
      assert [Γ |-[de] T ≅ tSig A B] as [? [? [r]]]%red_ty_compl_sig_r.
      1: eapply algo_conv_det_conv; cycle 3; tea; eexists; boundary + (eapply stability; tea; boundary).
      pose proof hconv as [?? wh]%algo_conv_wh.
      pose proof (redty_whnf r wh); subst.
      eexists; now econstructor.
    - admit.
    - intros * ? IH ? ? ? ? ? * ? Hconv.
      inv_bn Hconv.
      edestruct IH as [[T HconvA] []] ; tea.
      assert [Γ |-[de] A ≅ T].
      1:{ 
        eapply algo_conv_det_conv_alt; cycle 3; tea. 
        eapply bn_conv_sound in conv; eexists; eapply stability; tea; boundary.
      }
      assert (WN T) as [T0] by (eapply typing_nf_alt; exists istype; boundary).
      exists T0; now econstructor.
    - intros * ? ? Hu Ht' IHt ? ? ? * ? HconvA Hconv.
      inv_bn Hconv.
      eapply whred_det in Hu ; tea; subst.
      2: now destruct conv.
      2: now eapply algo_conv_wh in Ht' as []. 
      econstructor ; tea.
      eapply IHt ; tea.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; boundary.
      eassumption.
    - intros * ? [IHA HpostA] ? IHB ? ? ? ? A'' ? HΓ Hconvty Hconv.
      replace A'' with U in *.
      2:{
        destruct Hconv.
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_univ_r, redty_red in Hconvty.
      }
      inv_bn Hconv.
      2:{ destruct inf as [?? e]; inversion e. }
      econstructor; refold.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor.
        * now symmetry in HΓ ; boundary.
        * econstructor; refold; boundary.
    - intros * ? ? _ ? A' ? ? Hconvty Hconv.
      replace A' with U in *.
        2:{
          destruct Hconv.
          symmetry.
          eapply red_whnf.
          2: gen_typing.
          now eapply red_ty_compl_univ_r, redty_red in Hconvty.
        }
      inv_bn Hconv.
      + now econstructor.
      + destruct inf as [?? e]; inversion e.
    - intros * ?? _ ? A' ? ? Hconvty Hconv.
      replace A' with tNat in *.
        2:{
            destruct Hconv.
          symmetry.
          eapply red_whnf.
          2: gen_typing.
          now eapply red_ty_compl_nat_r, redty_red in Hconvty.
        }
      inv_bn Hconv.
      2: destruct inf as [???e] ; inversion e.
      now econstructor.
    - intros * ? [IHt ] ??? ? A' ? ? Hconvty Hconv.
      replace A' with tNat in *.
      2:{
        destruct Hconv.
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_nat_r, redty_red in Hconvty.
      }
      inv_bn Hconv.
      2: destruct inf as [?? e]; inversion e.
      econstructor; refold; now eapply IHt.
    - intros * ? IHt _ ? A' ? ? Hconvty Hconv.
      replace A' with U in *.
      2:{
        destruct Hconv.
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_univ_r, redty_red in Hconvty.
      }  
      inv_bn Hconv.
      2: destruct inf as [?? e]; inversion e.
      now econstructor.
    - intros * ? ? ? IH ? ? ? * ? h Hconv.
      inv_bn Hconv.
      all: try match goal with H : isPosType _ |- _ => destruct H end.
      all: try solve [now unshelve eapply ty_conv_inj in h ; [econstructor | econstructor | cbn in *]].
      eapply prod_ty_inj in h as [].
      econstructor ; tea.
      eapply IH ; tea.
      now econstructor.
    - intros * ? [IHA HpostA] ? IHB ? ? ? ? A'' ? HΓ Hconvty Hconv.
      replace A'' with U in *.
      2:{
        destruct Hconv.
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_univ_r, redty_red in Hconvty.
      }
      inv_bn Hconv.
      2: destruct inf as [?? e]; inversion e.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor.
        * now symmetry in HΓ ; boundary.
        * econstructor; refold;
          boundary.
    - intros * ? ? ? [ihFst] ? ihSnd ? ? ????? h Hconv.
      inv_bn Hconv.
      all: try match goal with H : isPosType _ |- _ => destruct H end.
      all: try solve [now unshelve eapply ty_conv_inj in h ; [econstructor | econstructor | cbn in *]].
      eapply sig_ty_inj in h as [].
      econstructor ; tea.
      1: eapply ihFst ; tea; now econstructor.
      eapply ihSnd; tea.
      eapply typing_subst1; tea.
      now symmetry.
    - intros * ? [ihA] ???? X ?? hconvty hconv.
      replace X with U in *. 2:{
        destruct hconv as [?? ?%isType_whnf].
        symmetry; eapply red_whnf; tea.
        now eapply red_ty_compl_univ_r, redty_red in hconvty.
      }
      inv_bn hconv.
      2: destruct inf as [?? e]; inversion e.
      econstructor; refold; now eapply ihA.
    - intros * ? ?? ? X ? ? [? [r ?]]%red_ty_compl_list_r hconv.
      pose proof hconv as [_ _ wh%isType_whnf].
      pose proof (red_whnf _ _ (redty_red r) wh); subst.
      inv_bn hconv.
      2: destruct inf as [?? e]; inversion e.
      econstructor.
    - intros * ? [ihhd] ? [ihtl] ??? ? X ? ? [? [r ?]]%red_ty_compl_list_r hconv.
      pose proof hconv as [_ _ wh%isType_whnf].
      pose proof (red_whnf _ _ (redty_red r) wh); subst.
      inv_bn hconv.
      2: destruct inf as [?? e]; inversion e.
      assert [Γ |-[de] A0 ≅ A]. 1:{
        eapply termGen' in H2 as [? [[->] ?%list_ty_inj]].
        eapply termGen' in H3 as [? [[->] ?%list_ty_inj]].
        etransitivity; tea; now symmetry.
      }
      econstructor.
      + eapply ihhd; tea.
      + eapply ihtl; tea; now econstructor.
    - intros * Hnconv [IH] ? ? ? ? * ? h Hconv.
      inv_bn Hconv.
      all: try solve [apply algo_conv_wh in Hnconv as [_ ?]; inv_whne].
      1,2: destruct H ;
          now unshelve eapply ty_conv_inj in h ; [now econstructor | now econstructor | cbn in *].
      edestruct IH as []; tea. 
      now econstructor.
Admitted.
(* Qed. *)

End Transitivity.

(** ** Instances *)

Module AlgorithmicConvProperties.
  Export AlgorithmicTypingData.

  #[local] Ltac intros_bn :=
    intros ;
    repeat match goal with | H : context [bn] |- _ => destruct H end ;
    econstructor ; try assumption.

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
      1-2: now eapply algo_typing_sound.
      inversion bun_conv_ty ; subst ; clear bun_conv_ty.
      econstructor.
      1-2: now etransitivity.
      eassumption.
    - intros_bn.
      1-2: now econstructor.
      do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_refl.
        * symmetry.
          now eapply algo_conv_sound in bun_conv_ty0.
      + now do 2 econstructor.
    - intros_bn.
      all: now do 2 econstructor.
    - intros_bn.
      1-2: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_refl.
        * symmetry.
          now eapply algo_conv_sound in bun_conv_ty0.
      + now do 2 econstructor.
    - intros_bn; econstructor; tea.
      1,2: reflexivity.
      now econstructor.
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
      all: eapply algo_conv_sound in bun_conv_ty ; tea.
      1-2: now econstructor.
      eapply algo_conv_conv ; tea.
      now apply ctx_refl.
    - intros_bn.
      1-3: now apply typing_wk.
      now apply algo_conv_wk.
    - intros_bn.
      all: eapply algo_typing_sound in bun_red_ty_ty, bun_inf_conv_inf0, bun_inf_conv_inf ; tea.
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
        (eapply algo_conv_sound in Hconvn as [[]%boundary] ; tea ; now gen_typing).
      assert [Γ |-[de] n' : A'] by
        (eapply algo_conv_sound in Hconvn as [[]%boundary] ; tea ; now gen_typing).
      split ; tea.
      1-2: now gen_typing.
      eapply algo_conv_conv ; tea.
      2: now eapply ctx_refl.
      apply ne_conv_conv; tea.
      boundary.
    - intros_bn.
      + now constructor.
      + constructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now apply ctx_refl.
        eapply algo_conv_sound in bun_conv_tm0 ; tea.
        symmetry.
        now constructor.
      + now do 2 econstructor.
    - intros_bn.
      + now constructor.
      + constructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now apply ctx_refl.
        eapply algo_conv_sound in bun_conv_tm0 ; tea.
        symmetry.
        now constructor.
      + now do 2 econstructor.
    - intros_bn.
      + boundary.
      + eauto using inf_conv_decl.
      + eauto using inf_conv_decl.
      + econstructor.
        1-3: reflexivity.
        econstructor.
        1-2: gen_typing.
        eassumption.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros_bn.
      1-2: gen_typing.
      now do 2 econstructor.
    - intros_bn.
      + boundary.
      + eauto using inf_conv_decl.
      + eauto using inf_conv_decl.
      + econstructor.
        1-3: reflexivity.
        econstructor; tea; gen_typing.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros_bn.
      1,2: now econstructor.
      econstructor; try reflexivity; now econstructor.
    - intros * hconv.
      pose proof hconv as ?%bn_conv_sound.
      destruct hconv; split; tea.
      1,2: now econstructor.
      * do 2 econstructor; tea; now symmetry.
      * econstructor; try reflexivity; econstructor.
    - intros * hconv [] [].
      pose proof hconv as ?%bn_conv_sound.
      split; tea.
      * now econstructor.
      * do 2 econstructor.
        1: boundary.
        3: now symmetry.
        all: econstructor; tea; now econstructor.
      * econstructor; try reflexivity; now econstructor.
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
      now eapply algo_conv_sound in bun_conv_ty.
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
    - now intros * [].
    - intros * [? ? Hty].
      inversion Hty ; subst ; clear Hty.
      econstructor.
      + assumption.
      + eexists. now econstructor.
      + gen_typing.
      + eexists. now econstructor.
      + gen_typing.
      + now econstructor.
      + eassumption.
  - intros *
    [? ? ? ? ? ? Hf (?&?&[])%red_ty_compl_prod_r]
    [? ? ? ? Ht].
    econstructor ; tea.
    + eapply algo_conv_sound in Hf as [Hf] ; tea.
      eapply boundary in Hf as [_ Hf _].
      eexists ; econstructor.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + gen_typing.
    + eapply algo_conv_sound in Hf as [Hg] ; tea.
      eapply boundary in Hg as [_ _ Hg].
      eexists ; econstructor.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + gen_typing.
    + econstructor.
      * econstructor ; tea.
        2: econstructor.
        now eapply redty_red.
      * eapply algo_conv_conv ; tea.
        now eapply ctx_refl.
    + eapply typing_subst1 ; tea.
      econstructor.
      eassumption.
  - intros_bn.
    + eexists.
      econstructor ; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + now econstructor.
    + eexists.
      econstructor ; tea.
      * econstructor ; tea.
        eapply typing_subst1 ; tea.
        2: now eapply algo_conv_sound in bun_conv_ty.
        now do 2 econstructor.
      * econstructor ; tea.
        eapply elimSuccHypTy_conv ; tea.
        now eapply algo_conv_sound in bun_conv_ty.
      * eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
        eapply boundary in Hconv as [].
        now econstructor.
    + now econstructor.
    + econstructor ; tea.
      econstructor ; tea.
      2: now econstructor.
      now eapply redty_red, red_ty_compl_nat_r.
    + econstructor.
      eapply typing_subst1 ; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
  - intros_bn.
    + eexists.
      econstructor ; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + now econstructor.
    + eexists.
      econstructor ; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + now econstructor.
    + econstructor ; tea.
      econstructor ; tea.
      2: now econstructor.
      now eapply redty_red, red_ty_compl_empty_r.
    + econstructor.
      eapply typing_subst1 ; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
  - intros * [].
    pose proof bun_conv_ne_conv_conv as [?[?[]]]%red_ty_compl_sig_r.
    econstructor; tea.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + gen_typing.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + gen_typing.
    + do 2 econstructor; tea.
      2: constructor.
      now eapply redty_red.
  - intros * [].
    pose proof bun_conv_ne_conv_conv as [?[?[]]]%red_ty_compl_sig_r.
    econstructor; tea.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + gen_typing.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound in bun_conv_ne_conv as [Hconv _]; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + gen_typing.
    + do 2 econstructor; tea.
      2: constructor.
      now eapply redty_red.
    + eapply typing_subst1.
      2: now symmetry.
      apply algo_conv_sound in bun_conv_ne_conv as []; tea.
      econstructor; eapply lrefl.
      eapply TermConv; tea; refold.
      etransitivity; tea.
      symmetry; econstructor; tea.
      1: boundary.
      now symmetry.
    - intros * tyeqA tyeqB tyeqC tyeqg tyeqf [?????? lstconv tyl].
      pose proof tyeqA as [? ? _ _].
      pose proof tyeqB as [_ ? _ _].
      pose proof tyeqC as [_ ? _ _].
      pose proof tyeqg as [_ ? ? _ _].
      pose proof tyeqf as [_ ? ? _ _].
      pose proof lstconv as []%algo_conv_sound; tea.
      (* pose proof tyl as [? [r]]%red_ty_compl_list_r. *)
      pose proof lstconv as []%algo_conv_wh.
      econstructor; tea.
      2, 4: now repeat constructor.
      * eexists; econstructor; tea; econstructor; tea; econstructor; tea; boundary.
      * eexists; econstructor; tea.
        1: eapply ty_comp; cycle 3; tea.
        econstructor; tea; boundary.
      * 
        assert (h : forall t, t⟨↑⟩⟨upRen_term_term ↑⟩ = t⟨↑⟩⟨↑⟩) by now (intro; asimpl).
        assert (h' : forall A f g ρ, comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩ = (comp A f g)⟨ρ⟩) by ( intros; now asimpl).
        destruct (is_map l || is_map l') eqn: hmap.
        1: inversion lstconv; subst; cbn in hmap; try inversion hmap.
        all: econstructor; try solve [cbn; easy].
        2,5: cbn; now destruct tyeqC.
        + admit. (* lemmas on compact_map fusion *)
        + cbn.
          rewrite !h, !h'.
          (* lemma on alg typing of comp + problem of reflexivity on f, g *)
          admit.
        + cbn; admit. (*lemma on compact_map for not map *)
        + cbn. rewrite !h, !h'.
        (* lemma on alg typing of comp + problem of reflexivity on f, g + lemma on compact_map for not map *)
          admit.
      * cbn; econstructor; now econstructor.
    - intros * tyeqA [?????? lstconv tyl].
      pose proof tyeqA as [? ? _].
      pose proof tyeqA as ?%bn_conv_sound.
      pose proof lstconv as [? hwtyl]%algo_conv_sound; tea.
      pose proof lstconv as []%algo_conv_wh.
      econstructor.
      1,3,4,5: tea.
      1: now econstructor.
      3: eapply TypeRefl; now econstructor.
      2: destruct (is_map l || is_map l') eqn: hmap.
      2: inversion lstconv; subst; cbn in hmap; try inversion hmap.
      + eexists. econstructor; tea.
        1: now eapply ty_id.
        destruct bun_conv_ne_conv_l as [Tl wtyl].
        econstructor; tea.
        etransitivity; tea.
        symmetry; now eapply hwtyl.
      + refold. admit.
      + set (t := tMap _ _ _ _).
        change (tList A) with (tList (Map.tgtTy (compact_map A t))).
        econstructor; cbn; try easy.
        all: admit. (* lemmas on map compactification *)
    - intros * convA convB [] [?????? convl].
      pose proof convA as ?%bn_conv_sound.
      pose proof convB as ?%bn_conv_sound.
      pose proof convl as []%algo_conv_wh.
      pose proof convl as [? _ _]%algo_conv_sound; tea.
      destruct convA, convB; econstructor; tea.
      2,4: now econstructor.
      * do 2 econstructor; tea; econstructor; tea; now boundary.
      * do 2 econstructor; tea; econstructor; tea.
        1: eapply convty_simple_arr; tea.
        1: now boundary.
        etransitivity; tea; now econstructor.
      * destruct (is_map l || is_map l') eqn: hmap.
        + inversion convl; subst; cbn in hmap; try inversion hmap.
          econstructor; cbn; try easy.
          1,2: admit.
        + econstructor; cbn; try easy.
          1,2: admit.
      * cbn; econstructor; now econstructor.
  Admitted.
  (* Qed. *)

End AlgorithmicConvProperties.

Module IntermediateTypingProperties.
  Export BundledIntermediateData.
  Import AlgorithmicConvProperties.

  #[export, refine] Instance WfCtxIntProperties : WfContextProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    1-2: now econstructor.
    1-2: gen_typing.
    1-4: intros * [] ; gen_typing.
  Qed.

  #[export, refine] Instance WfTypeIntProperties : WfTypeProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni ; gen_typing.
  Qed.

  #[export, refine] Instance TypingIntProperties : TypingProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - intros * ? [].
      econstructor ; tea.
      symmetry.
      eapply RedConvTyC, subject_reduction_type ; tea.
    - intros * ? [].
      econstructor ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
  Qed.

  #[export, refine] Instance ConvTypeIntProperties : ConvTypeProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros * ? ?.
      apply convty_wk ; tea.
      now split.
    - intros * [] [] [] ; econstructor.
      1-3: eassumption.
      inversion bun_conv_ty ; subst ; clear bun_conv_ty ; refold.
      econstructor.
      3: eassumption.
      1-2: now etransitivity.
    - intros ? ?.
      split.
      2-3: econstructor.
      1-3: assumption.
      do 2 econstructor.
    - intros * ?  [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        now eapply algo_conv_sound in bun_conv_ty.
      + now do 2 econstructor.
    - econstructor ; tea.
      1-3: econstructor ; tea.
      all: now econstructor.
    - econstructor ; tea.
      1-2: now econstructor.
      now do 2 econstructor.
    - intros * ?  [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        now eapply algo_conv_sound in bun_conv_ty.
      + now do 2 econstructor.
    - intros * []; split; tea.
      1,2: gen_typing.
      econstructor; try reflexivity; now econstructor.
  Qed.

  #[export, refine] Instance ConvTermIntProperties : ConvTermProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros.
      apply (convtm_wk (ta := bn)) ; tea.
      now econstructor.
    - intros * [] [] [] [].
      econstructor ; tea.
      + eapply subject_reduction_type, RedConvTyC in buni_red_ty ; tea.
        symmetry in buni_red_ty.
        now gen_typing.
      + eapply subject_reduction_type, RedConvTyC in buni_red_ty ; tea.
          symmetry in buni_red_ty.
          now gen_typing.
      + inversion bun_conv_tm ; subst ; clear bun_conv_tm ; refold.
        econstructor.
        4: eassumption.
        all: now etransitivity. 
    - gen_typing.
    - intros * ? [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        econstructor.
        now eapply algo_conv_sound in bun_conv_tm.
      + now do 2 econstructor.
    - intros * ? [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        econstructor.
        now eapply algo_conv_sound in bun_conv_tm.
      + now do 2 econstructor.
    - intros * ? ? ? ? ? ? [].
      split ; tea.
      + gen_typing.
      + boundary.
      + do 2 econstructor ; gen_typing.
    - intros.
      eapply (convtm_nat (ta := bn)).
      now econstructor.
    - intros.
      eapply (convtm_zero (ta := bn)).
      now econstructor.
    - intros.
      now eapply (convtm_succ (ta := bn)).
    - intros * ? ? ? ? ? ? [] [].
      split ; tea.
      + gen_typing.
      + econstructor.
        1-3: reflexivity.
        econstructor; gen_typing.
    - intros ? HΓ.
      eapply (convtm_empty (ta := bn)).
      now econstructor.
    - intros; now eapply (convtm_list (ta:=bn)).
    - intros; now eapply (convtm_nil (ta:=bn)).
    - intros; now eapply (convtm_cons (ta:=bn)).
  Qed. 

  #[export, refine] Instance ConvNeuIntProperties : ConvNeuProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros.
      apply convneu_wk ; tea.
      now split.
    - now intros * [].
    - intros * [? [[? [-> ]]]]%termGen'.
      econstructor.
      + gen_typing.
      + now eexists ; gen_typing.
      + gen_typing.
      + now eexists ; gen_typing.
      + gen_typing.
      + now econstructor.
      + eassumption.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
  Qed.

  #[export, refine] Instance RedTermIntProperties :
    RedTermProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - intros * ? [].
      econstructor ; tea.
      + now eapply typing_wk.
      + now eapply credalg_wk.
    - intros * []; assumption.
    - now intros * []. 
    - intros; constructor.
      + boundary.
      + econstructor ; tea.
        now econstructor.
      + do 2 econstructor.
    - constructor; unfold_bni.
      + boundary.
      + econstructor ; tea.
        econstructor.
        now boundary.
      + econstructor ; [| reflexivity]; econstructor.
    - constructor; unfold_bni.
      + boundary.
      + econstructor ; tea.
        econstructor.
        now boundary.
      + econstructor ; [| reflexivity]; econstructor.
    - intros * [] ?.
      split.
      + boundary.
      + now econstructor.
      + clear -buni_red_tm.
        induction buni_red_tm.
        1: econstructor.
        econstructor.
        1: now econstructor.
        eassumption.
    - intros ? ? ? ? ? ? ? ? ? [? ? Hr]; econstructor.
      + now eapply boundary_tm_ctx.
      + now constructor.
      + clear - Hr; induction Hr; try constructor.
        econstructor; [|eassumption].
        now constructor.
    - intros ? ? ? ? ? [? ? Hr]; econstructor.
      + now eapply boundary_tm_ctx.
      + now constructor.
      + clear - Hr; induction Hr; try constructor.
        econstructor; [|eassumption].
        now constructor.
    - intros; econstructor; tea.
      1: boundary.
      1: gen_typing.
      econstructor. 
      2: reflexivity.
      constructor.
    - intros * [].
      econstructor; tea.
      1: gen_typing.
      clear -buni_red_tm; induction buni_red_tm.
      1: reflexivity.
      econstructor; eauto. 
      now constructor.
    - intros; econstructor; tea.
      1: boundary.
      1: gen_typing.
      econstructor. 
      2: reflexivity.
      constructor.
    - intros * [].
      econstructor; tea.
      1: gen_typing.
      clear -buni_red_tm; induction buni_red_tm.
      1: reflexivity.
      econstructor; eauto. 
      now constructor.
    - intros * ??? []; econstructor; tea.
      1: now econstructor.
      now eapply redalg_map.
    - intros * ?? ?%bn_conv_sound ??; split ; tea.
      + boundary.
      + gen_typing.
      + eapply redalg_one_step; econstructor.
    - intros * ?? ?%bn_conv_sound ????; econstructor; tea.
      + boundary.
      + gen_typing.
      + eapply redalg_one_step; econstructor.
    - intros * [] [].
      econstructor ; tea.
      econstructor ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
    - intros.
      split.
      + boundary.
      + assumption.
      + reflexivity.
    - red ; intros * [] [].
      econstructor ; tea.
      now etransitivity.
    Qed.

  #[export, refine] Instance RedTypeIntProperties :
    RedTypeProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - intros * ? [].
      econstructor ; tea.
      + now eapply typing_wk.
      + now eapply credalg_wk.
    - intros * []; assumption.
    - now intros * [].
    - intros * [].
      split.
      + boundary.
      + now econstructor.
      + eassumption.
    - intros.
      split.
      + boundary.
      + eassumption.
      + reflexivity.
    - red. intros * [] [].
      econstructor ; tea.
      now etransitivity.
  Qed.

  #[export] Instance IntermediateTypingProperties : GenericTypingProperties bni _ _ _ _ _ _ _ _ _ _ := {}.

End IntermediateTypingProperties.

(** ** Consequence: Completeness of algorithmic conversion  *)

(** We use the intermediate instance derived above, and the fundamental lemma. *)

Import BundledIntermediateData IntermediateTypingProperties.

Lemma algo_conv_complete Γ A B :
  [Γ |-[de] A ≅ B] ->
  [Γ |-[al] A ≅ B].
Proof.
  now intros [HΓ ? _ []%(escapeEq (ta := bni))]%Fundamental.
Qed.