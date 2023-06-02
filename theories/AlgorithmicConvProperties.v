(** * LogRel.AlgorithmicConvProperties: properties of algorithmic conversion. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping DeclarativeSubst TypeConstructorsInj Normalisation BundledAlgorithmicTyping Fundamental.
From LogRel.LogicalRelation Require Import Escape.
From LogRel.Substitution Require Import Properties Escape.


Import AlgorithmicTypingData BundledTypingData DeclarativeTypingProperties.

(* Lemmas on Map *)
Lemma not_is_map_compact_id {t} : ~~ is_map t -> Map.compact t = Map.IsNotMap t.
Proof.
  destruct t; cbn; try reflexivity; discriminate.
Qed.

Lemma is_map_compact_id {t} : is_map t -> ∑ r,  Map.compact t = Map.IsMap r.
Proof.
  destruct t; cbn; try discriminate.
  intros; eexists; reflexivity.
Qed.

Definition map_data_wty Γ (r : Map.data) := 
  [× [Γ |-[de] Map.lst r : tList (Map.srcTy r)],
    [Γ |-[de] Map.srcTy r],
    [Γ |-[de] Map.tgtTy r] &
    [Γ |-[de] Map.fn r : arr (Map.srcTy r) (Map.tgtTy r)]].

Lemma compact_well_typed {Γ t A r} : 
  [Γ |-[de] t : A] ->
  Map.compact t = Map.IsMap r ->
  [Γ |-[de] tList (Map.tgtTy r) ≅ A] × map_data_wty Γ r.
Proof.
  induction t in A, r |- *;cbn; intros ? [=].
  destruct (Map.compact t4) eqn:E; subst; cbn in *.
  all: pose proof H as [? [[->]]]%termGen'.
  2: now (split; [|split]).
  edestruct IHt4 as [? []]; [tea|reflexivity|].
  split;[|split]; cbn; tea.
  eapply ty_comp; try assumption; cycle 2; tea.
  eapply list_ty_inj in c0.
  econstructor; tea.
  eapply convty_simple_arr; tea.
  2: now symmetry.
  now econstructor.
Qed.

Lemma map_id_well_typed {Γ t A} : [Γ |-[de] t : tList A] -> map_data_wty Γ (Map.id A t).
Proof.
  intros.
  assert [Γ |-[de] A] by (eapply list_ty_inv; boundary).
  split; cbn; tea.
  eapply ty_id; tea; now econstructor.
Qed.

Lemma extract_well_typed {Γ l A l' A'} (rx := Map.extract l l') :
  is_map l || is_map l' ->
  [Γ |-[de] l : A] ->
  [Γ |-[de] l' : A'] ->
  [Γ |-[de] A ≅ A'] ->
  map_data_wty Γ (fst rx) × map_data_wty Γ (snd rx).
Proof.
  unfold Map.extract in rx.
  destruct (Map.compact l) eqn:El, (Map.compact l') eqn: El'.
  + intros _ ???; split; now (eapply compact_well_typed; [|tea]).
  + intros _ ???.
    eapply compact_well_typed in El; tea; destruct El.
    split; tea; cbn in *. eapply map_id_well_typed; econstructor; tea.

    1: eapply compact_well_typed; [|tea]; tea.
    cbn in *.
  


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
    - intros * hmap  ? [ih [? ihl ihr]] ? [] ? [] ?????.
      edestruct ih as [? []]; tea.
      eexists; split.
      2:{ 
        eapply TypeRefl; refold; econstructor.
        eapply stability; tea.


      }

    
    admit.
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
    - intros * ? IHm HtyP ? ? ? * ? HconvN HtyA'.
      edestruct IHm as [[? []] ?] ; tea.
      unshelve eapply ty_conv_inj in HconvN.
      1: now gen_typing.
      1: assumption.
      econstructor ; tea.
      destruct HtyP, HtyA'.
      all: cbn in HconvN ; try now exfalso.
      all: now constructor.
  Admitted.
  (* Qed. *)

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
    - admit.
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
  Admitted.
  (* Qed. *)
  
End Symmetry.

(** ** Transitivity *)

(* Helper lemma for transitivity on neutrals with a map only on the right *)
Lemma algo_conv_trans_map_r Γ Δ A A' t u v 
  (r := snd (Map.extract u v)) :
  ~~ is_map t ->
  ~~ is_map u ->
  is_map v ->
  (* [Γ |-[al] t ~ u ▹ A] -> *)
  [Δ |-[al] u ~h Map.lst r ▹ tList A'] ->
  [Γ |-[al] t ~h Map.lst r ▹ A] ->
  [Γ |-[de] A ≅ tList A'] ->

  (* [Δ |-[al] A' ≅ Map.tgtTy r] ->
  [Δ |-[al] idterm A' ≅ Map.fn r : arr A' A'] ->
  [Γ |-[al] t ~ v ▹ A] × [Γ |-[de] A ≅ tList A']. *)
  [Δ |-[al] Map.srcTy r ≅ Map.tgtTy r] ->
  [Δ |-[al] idterm (Map.srcTy r) ≅ Map.fn r : arr (Map.srcTy r) (Map.tgtTy r)] ->
  ∑ B, [Γ |-[al] t ~ v ▹ B] × [Γ |-[de] A ≅ tList (Map.srcTy r)].
Proof.
  set (rx := Map.extract u v) in *.
  unfold Map.extract in rx.
  intros hmapt hmapu hmapv convul convtl convtytl convty convfn.
  pose proof (is_map_compact_id hmapv) as [rv eqv].
  assert (rx = Map.combine (Map.IsNotMap u) (Map.IsMap rv)). 1:{
    now rewrite <- eqv, <- (not_is_map_compact_id hmapu).
  }
  cbn in H.
  unfold r in *; clear r; rewrite H in *.
  cbn in *.
  
Admitted.

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
    ∑ B, [× [Γ |-[al] t ~ v ▹ B], [Γ |-[de] B ≅ A] & [Γ |-[de] B ≅ A']].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ~h v ▹ A'] ->
    ∑ B, [× [Γ |-[al] t ~h v ▹ B], [Γ |-[de] B ≅ A] & [Γ |-[de] B ≅ A']].
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
        econstructor.
        + eapply IHA ; tea.
        + eapply IHB ; tea.
          now econstructor.
    - intros * ? ? _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{ apply algo_conv_wh in H2 as [e _]. now inversion e. }
      now constructor.
    - intros * ? ? _ * ? Hconv.
      inversion Hconv ; subst ; refold.
      1: now constructor.
      eapply algo_conv_wh in H2 as [e _].
      now inversion e.
    - intros * ? ? _ * ? hconv.
      inversion hconv ; subst ; clear hconv.
      2:{ apply algo_conv_wh in H2 as [e _]. now inversion e. }
      now constructor.
    - intros * ? [IHA ] ? IHB ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{
        apply algo_conv_wh in H5 as [e _].
        now inversion e.
        }
        econstructor.
        + eapply IHA ; tea.
        + eapply IHB ; tea.
          now econstructor.
    - intros * ? ? _ * ? ???? hconv.
      inversion hconv ; subst ; clear hconv.
      2:{ apply algo_conv_wh in H3 as [e _]. now inversion e. }
      now constructor.
    - intros * ? [IH] ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      1-6: apply algo_conv_wh in H as [_ e] ; now inversion e.
      edestruct IH as [? []]; tea.
      now econstructor.
    - intros * Hin ? _ _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      (** Need to find a generic solution for this case and the following ones *)
      2:{ cbn -[Map.extract] in *.  eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      split.
      + now econstructor.
      + eapply in_ctx_conv_l in Hin as [? [Hin ]]; tea.
        eapply in_ctx_inj in Hin.
        2: clear Hin ; tea.
        now subst.
    - intros * ? IHm ? IHt ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      eapply IHm in H9 as [? []%prod_ty_inj] ; tea.
      split.
      + econstructor ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        1: now eapply IHt.
        now symmetry.
    - intros * ? IHn ? IHP ? IHz ? IHs ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      eapply IHn in H13 as [? _] ; tea.
      split.
      + econstructor ; tea.
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
      + eapply typing_subst1 ; tea.
        1: eapply IHn.
        eapply IHP.
    - intros * ? IHe ? IHP ? ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      eapply IHe in H9 as [? _] ; tea.
      split.
      + econstructor ; tea.
        eapply IHP ; tea.
        econstructor ; tea.
        now do 2 econstructor.
      + eapply typing_subst1 ; tea.
        1: eapply IHe.
        eapply IHP.
    - intros * ? [ih []] ??????? hconv.
      inversion hconv; subst; clear hconv; refold.
      2: cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      edestruct ih as [? []%sig_ty_inj]; tea.
      split; [now econstructor|now symmetry].
    - intros * ? [ih []] ??????? hconv.
      inversion hconv; subst; clear hconv; refold.
      2: cbn in *; eapply algo_conv_trans_map_r; tea; cbn; now econstructor.
      edestruct ih as [? []%sig_ty_inj]; tea.
      split; [now econstructor|].
      eapply typing_subst1; tea.
      eapply TermConv; refold; [now econstructor|now symmetry].
    - admit.
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
      econstructor ; tea.
      eapply IHt ; tea.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; boundary.
      eassumption.
    - intros * ? [IHA HpostA] ? IHB ? ? ? ? A'' ? HΓ Hconvty Hconv.
      replace A'' with U in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_univ_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: eapply algo_conv_wh in H4 as [w _]; inv_whne.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor.
        * now symmetry in HΓ ; boundary.
        * econstructor.
          boundary.
    - intros * ? ? _ ? A' ? ? Hconvty Hconv.
      replace A' with U in *.
        2:{
          eapply algo_conv_wh in Hconv as [].
          symmetry.
          eapply red_whnf.
          2: gen_typing.
          now eapply red_ty_compl_univ_r, redty_red in Hconvty.
        }
      inversion Hconv ; subst ; clear Hconv ; refold.
      + now econstructor.
      + eapply algo_conv_wh in H2 as [w _]; inv_whne.
    - intros * ?? _ ? A' ? ? Hconvty Hconv.
      replace A' with tNat in *.
        2:{
          eapply algo_conv_wh in Hconv as [].
          symmetry.
          eapply red_whnf.
          2: gen_typing.
          now eapply red_ty_compl_nat_r, redty_red in Hconvty.
        }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: eapply algo_conv_wh in H2 as [? _]; inv_whne.
      now econstructor.
    - intros * ? IHt ??? ? A' ? ? Hconvty Hconv.
      replace A' with tNat in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_nat_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: apply algo_conv_wh in H4 as [? _]; inv_whne.
      now econstructor.
    - intros * ? IHt _ ? A' ? ? Hconvty Hconv.
      replace A' with U in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_univ_r, redty_red in Hconvty.
      }  
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: apply algo_conv_wh in H1 as [? _]; inv_whne.
      now econstructor.
    - intros * ? ? ? IH ? ? ? * ? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      all: try match goal with H : isPosType _ |- _ => destruct H end.
      all: try solve [now unshelve eapply ty_conv_inj in h ; [econstructor | econstructor | cbn in *]].
      eapply prod_ty_inj in h as [].
      econstructor ; tea.
      eapply IH ; tea.
      now econstructor.
    - intros * ? [IHA HpostA] ? IHB ? ? ? ? A'' ? HΓ Hconvty Hconv.
      replace A'' with U in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_ty_compl_univ_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: apply algo_conv_wh in H4 as [? _]; inv_whne.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor.
        * now symmetry in HΓ ; boundary.
        * econstructor.
          boundary.
    - intros * ? ? ? [ihFst] ? ihSnd ? ? ????? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
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
        eapply algo_conv_wh in hconv as [_ _ ?%isType_whnf].
        symmetry; eapply red_whnf; tea.
        now eapply red_ty_compl_univ_r, redty_red in hconvty.
      }
      inversion hconv; subst; clear hconv; refold.
      2: apply algo_conv_wh in H4 as [? _]; inv_whne.
      now econstructor.
    - intros * ? ?? ? X ? ? [? [r ?]]%red_ty_compl_list_r hconv.
      pose proof hconv as [_ _ wh%isType_whnf]%algo_conv_wh.
      pose proof (red_whnf _ _ (redty_red r) wh); subst.
      inversion hconv; subst; clear hconv; refold.
      2: apply algo_conv_wh in H3 as [? _]; inv_whne.
      econstructor.
    - intros * ? [ihhd] ? [ihtl] ??? ? X ? ? [? [r ?]]%red_ty_compl_list_r hconv.
      pose proof hconv as [_ _ wh%isType_whnf]%algo_conv_wh.
      pose proof (red_whnf _ _ (redty_red r) wh); subst.
      inversion hconv; subst; clear hconv; refold.
      2: apply algo_conv_wh in H5 as [? _]; inv_whne.
      assert [Γ |-[de] A' ≅ A]. 1:{
        eapply termGen' in H2 as [? [[->] ?%list_ty_inj]].
        eapply termGen' in H3 as [? [[->] ?%list_ty_inj]].
        etransitivity; tea; now symmetry.
      }
      econstructor.
      + eapply ihhd; tea.
      + eapply ihtl; tea; now econstructor.
    - intros * Hnconv IH ? ? ? ? * ? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      all: try solve [apply algo_conv_wh in Hnconv as [_ ?]; inv_whne].
      1,2: destruct H ;
          now unshelve eapply ty_conv_inj in h ; [now econstructor | now econstructor | cbn in *].
      econstructor ; tea.
      now eapply IH.
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