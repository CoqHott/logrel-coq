(** * LogRel.AlgorithmicConvProperties: properties of algorithmic conversion. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping DeclarativeSubst TypeConstructorsInj Normalisation BundledAlgorithmicTyping Fundamental.
From LogRel.LogicalRelation Require Import Escape.
From LogRel.Substitution Require Import Properties Escape.

Import AlgorithmicTypingData BundledTypingData DeclarativeTypingProperties.

(** ** Stability of algorithmic conversion by type/term expansion *)

  Lemma algo_conv_ty_expand Γ A A' B B':
    [A ⤳* A'] -> [B ⤳* B'] -> [Γ |-[al] A' ≅ B'] -> [Γ |-[al] A ≅ B].
  Proof.
    intros ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    econstructor ; [..|eassumption].
    all: now etransitivity.
  Qed.

  Lemma algo_conv_tm_expand Γ A A' t t' u u':
    [A ⤳* A'] -> [t ⤳* t'] -> [u ⤳* u'] -> [Γ |-[al] t' ≅ u' : A'] -> [Γ |-[al] t ≅ u : A].
  Proof.
    intros ??? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    econstructor ; [..|eassumption].
    all: now etransitivity.
  Qed.

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
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], isType A' & [Γ' |-[de] A' ≅ A]].
  Let PTmEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] ->  isType A' -> [Γ' |-[de] A ≅ A'] ->
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
    - intros * ? ihA ? ihx ? ihy ? h **.
      econstructor; [now eapply ihA| eapply ihx | eapply ihy]; tea.
      1,2: eapply stability; tea; now eapply lrefl.
    - intros * ? IHM **.
      edestruct IHM as [[? []]] ; tea.
      now econstructor.
    - intros * HΓ **.
      eapply in_ctx_conv_r in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      eassumption.
    - intros * ? IHm Ht [IHt []%boundary] **.
      edestruct IHm as [[? [?? (?&?&[->])%red_ty_compl_prod_r']] ?] ; tea.
      2: gen_typing.
      eexists ; split.
      + econstructor ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply stability.
    - intros * ? IHn ? IHP ? IHz ? IHs **.
      edestruct IHn as [[? [?? ->%red_ty_compl_nat_r']][]] ; tea.
      2: gen_typing.
      eexists ; split.
      1: econstructor.
      + eauto.
      + eapply IHP.
        econstructor ; tea ; do 2 econstructor ; boundary.
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
      edestruct IHe as [[? [?? ->%red_ty_compl_empty_r']][]] ; tea.
      2: gen_typing.
      eexists ; split.
      1: econstructor.
      + eauto.
      + eapply IHP.
        econstructor ; tea ; do 2 econstructor ; boundary.
      + econstructor.
        destruct IHP.
        eapply stability ; tea.
        eapply typing_subst1.
        all: now boundary.
    - intros * ? [ih [? ihm ihn]] ? hm hn ??.
      edestruct ih as [?[?? [?[? [->] ]]%red_ty_compl_sig_r']]; tea.
      2: gen_typing.
      eexists; split; tea; now econstructor.
    - intros * ? [ih [? ihm ihn]] **.
      edestruct ih as [?[?? [?[? [->] ]]%red_ty_compl_sig_r']]; tea.
      2: gen_typing.
      eexists; split.
      1: now econstructor.
      eapply typing_subst1 ; tea.
      do 3 econstructor.
      1: eapply stability ; boundary.
      symmetry.
      econstructor ; tea.
      boundary.
    - intros * ? [ih [? ihm ihn]] ? [ihP] ? [ihhr] ? hm hn **.
      assert (well_typed Γ' (tIdElim A x P hr y e)) as hm'
        by (edestruct hm ; eexists ; now eapply stability).
      assert (well_typed Γ' (tIdElim A' x' P' hr' y' e')) as hn'
        by (edestruct hn ; eexists ; now eapply stability).
      edestruct ih as (?&[[? ihe]%dup]) ; tea.
      pose proof hm' as [? [? [[] ]]%termGen'].
      pose proof hn' as [? [? [[] ]]%termGen'].
      eapply algo_conv_sound in ihe as [].
      2-3: now eexists.
      epose proof (idElimConv hm' hn') as (?&?&?&[]) ; tea ; subst.
      1: gen_typing.
      eexists; split.
      1: econstructor; tea; eauto.
      + eapply ihP.
        symmetry.
        eapply idElimMotiveCtxConv ; tea.
        * econstructor. boundary.
        * now econstructor.
        * boundary.
        * eapply idElimMotiveCtx.
          all: eapply stability ; [boundary|now symmetry]. 
      + eapply ihhr ; tea.
        econstructor.
        eapply typing_subst2 ; tea.
        1: boundary.
        eapply typing_meta_conv.
        1: econstructor ; boundary.
        cbn.
        now bsimpl.
      + eapply TypeRefl; refold; now boundary.
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
      + eassumption.
      + symmetry ; etransitivity ; tea.
        now eapply RedConvTyC.
    - intros * ? ? ? []%algo_conv_wh IH ? ? ? ? A'' **.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'
        by now eapply conv_red_l.
      pose proof HconvA' as [? []]%red_ty_complete ; tea.
      econstructor ; tea.
      1: now eapply redty_red.
      eapply IH ; tea.
      etransitivity ; tea.
      now eapply RedConvTyC.
    - intros * ? [IHA HconvA] ? IHB ? ? ? * ? ? ->%red_ty_compl_univ_l' ; tea.
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
    - intros * ??? * ?? ->%red_ty_compl_univ_l'.
      2: gen_typing.
      now econstructor.
    - intros * ??? * ?? ->%red_ty_compl_nat_l'.
      2: gen_typing.
      now econstructor.
    - intros * ? IH ? * ?? * ?? ->%red_ty_compl_nat_l'.
      2: gen_typing.
      econstructor.
      eapply IH ; tea.
      do 2 econstructor ; boundary.
    - intros * ??? * ?? ->%red_ty_compl_univ_l'.
      2: gen_typing.
      now econstructor.
    - intros * ? ? ? IHf ? ? ? * ? ? (?&?&[->])%red_ty_compl_prod_l'.
      2: gen_typing.
      econstructor ; tea.
      eapply IHf ; tea.
      now econstructor. 
    - intros * ? [ihA] ? [ihB] ?????? ? ->%red_ty_compl_univ_l'.
      2: gen_typing.
      econstructor.
      + eapply ihA ; tea.
        do 2 econstructor ; boundary.
      + assert [ |-[ de ] Γ',, A ≅ Γ,, A].
        {
          econstructor; tea; eapply stability; tea. 
          eapply lrefl; now econstructor. 
        }
      eapply ihB; tea.
      do 2 constructor; boundary.
    - intros * ??? [ihA] ? [ihB] ??????? [?[?[->]]]%red_ty_compl_sig_l'.
      2: gen_typing.
      econstructor; tea.
      1: eapply ihA; tea; now symmetry.
      eapply ihB; tea. 
      eapply typing_subst1; tea.
      do 2 econstructor.
      now eapply stability.
    - intros * ? [ihA] ? [ihx] ? [ihy] ? hm ? * ? ? ->%red_ty_compl_univ_l'.
      2: gen_typing.
      assert [Γ' |-[de] A ≅ A] by (eapply stability; tea; eapply lrefl; now econstructor).
      econstructor; tea.
      + eapply ihA; tea; constructor; eapply stability; tea; now boundary.
      + eapply ihx; tea.
      + eapply ihy; tea.
    - intros * ??? * ? ? [?[?[? [->]]]]%red_ty_compl_id_l'.
      2: gen_typing.
      now econstructor.
    - intros * ? IHm HtyP ? ? ? * ? HtyA' HconvN.
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
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], isType A' & [Γ' |-[de] A' ≅ A]].
  Let PTmEq (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ |-[de] t : A] -> [Γ |-[de] u : A ] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> isType A' -> [Γ' |-[de] A ≅ A'] ->
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
      [A ⤳* U] ->
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
    - intros; congruence.
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
    - intros * ? ihA ? [ihx] ? [ihy] ? [? []]%id_ty_inv [? []]%id_ty_inv * ?.
      econstructor.
      + now eapply ihA.
      + eapply algo_conv_conv.
        * eapply ihx; tea.
        * now eapply conv_ctx_refl_r.
        * pose proof H as ?%algo_conv_sound;try boundary.
          now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          now symmetry.
        * now eapply stability.
      + eapply algo_conv_conv.
        * eapply ihy; tea.
        * now eapply conv_ctx_refl_r.
        * pose proof H as ?%algo_conv_sound;try boundary.
          now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          now symmetry.
        * now eapply stability.
    - intros * ? IHM  **.
      edestruct IHM as [[U' [IHM' HconvM]] []] ; tea.
      now econstructor.
    - intros * HΓ **.
      eapply in_ctx_conv_l in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      now eapply stability.
    - intros * ? IHm ? [IHt Hwft]  **.
      edestruct IHm as [[? [IHm' (?&?&[->])%red_ty_compl_prod_l']] []] ; tea ; clear IHm.
      2: now eapply algo_conv_wh in IHm' as [].
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
      edestruct IHn as [[? [IHn' ->%red_ty_compl_nat_l']] []] ; tea ; clear IHn.
      2: now eapply algo_conv_wh in IHn' as [].
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
      edestruct IHe as [[? [IHe' ->%red_ty_compl_empty_l']] []] ; tea ; clear IHe.
      2: now eapply algo_conv_wh in IHe' as [].
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
      edestruct ih as [? [hconv (?&?&[])%red_ty_compl_sig_l']]; tea; subst.
      2: now apply algo_conv_wh in hconv as [].
      eexists; split.
      1: now econstructor.
      now symmetry.
    - intros * ? [ih []] ?????.
      edestruct ih as [? [hconv (?&?&[])%red_ty_compl_sig_l']]; tea; subst.
      2: now apply algo_conv_wh in hconv as [].
      eexists; split.
      1: now econstructor.
      eapply typing_subst1; tea.
      econstructor.
      now eapply stability.
    - intros * ? [ihe [? ihme]] ? [ihP] ? [ihhr] ? hm hn * ?.
      edestruct ihe as [? [[hconv hconv']%dup]] ; tea; subst.
      destruct hm as [? [? [? [[->] ]]%termGen']%dup].
      destruct hn as [? [? [? [[->] ]]%termGen']%dup].
      eapply algo_conv_sound in hconv' as [].
      2-3: now eexists ; eapply stability.
      epose proof (idElimConv (e := e) (e' := e')) as (?&?&?&[]) ; tea.
      1-2: eexists ; eapply stability ; tea ; now symmetry.
      1: now symmetry.
      now eapply algo_conv_wh in hconv as [].
      subst.
      eassert [(Δ,, A'),, tId A'⟨wk1 A'⟩ x'⟨wk1 A'⟩ (tRel 0) |-[ al ] P' ≅ P].
      {
        eapply ihP.
        eapply idElimMotiveCtxConv; tea.
        * now symmetry.
        * now symmetry.
        * symmetry ; now econstructor.
        * eapply idElimMotiveCtx.
          2: econstructor ; tea.
          all: boundary.
        * eapply idElimMotiveCtx.
          all: boundary.
      }
      eexists; split.
      1: econstructor; tea.
      + eapply algo_conv_conv.
        * now eapply ihhr.
        * now eapply conv_ctx_refl_r.
        * eapply typing_subst2; tea.
          1: boundary.
          all: cycle -1.
          -- eapply stability ; tea.
             eapply idElimMotiveCtxConv ; tea.
             3: boundary.
             3: eapply idElimMotiveCtx.
             1-2: econstructor.
             all: boundary.
          -- eapply convtm_meta_conv.
             1: econstructor.
             4: reflexivity.
             1-2: eassumption.
             cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq; now econstructor.
        * eapply stability; [| now symmetry]; now boundary.
        * eapply stability; [| now symmetry]; now boundary.
      + eapply stability; tea;[| now symmetry].
        eapply typing_subst2; tea.
        1: now eapply stability.
        cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq; tea.
        econstructor; tea.
        symmetry.
        now econstructor.
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
    - intros * ? [ihA] ? [ihx] ? [ihy] ? [? [[->]]]%termGen' [? [[->]]]%termGen' * ?.
      econstructor.
      + now eapply ihA.
      + eapply algo_conv_conv.
        * eapply ihx; tea.
        * now eapply conv_ctx_refl_r.
        * constructor.
          pose proof H as ?%algo_conv_sound;try boundary.
          now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          symmetry; now econstructor.
        * now eapply stability.
      + eapply algo_conv_conv.
        * eapply ihy; tea.
        * now eapply conv_ctx_refl_r.
        * pose proof H as ?%algo_conv_sound;try boundary.
          econstructor; now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          econstructor; now symmetry.
        * now eapply stability.
    - econstructor.
    - intros * ? IH  **.
      edestruct IH as [[? []] []] ; tea.
      now econstructor.
  Qed.
  
End Symmetry.

(** ** Transitivity *)

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
    - intros * ? ? _ * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
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
    - intros * ? [ihA] ? [ihx] ? [ihy] ??? * ? hconv.
      inversion hconv; subst; clear hconv; refold.
      2: apply algo_conv_wh in H6 as [e _]; now inversion e.
      econstructor.
      + now eapply ihA.
      + eapply ihx; tea; now symmetry.
      + eapply ihy; tea; now symmetry.
    - intros * ? IH ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold; cycle -1.
      1:econstructor; now eapply IH.
      all: apply algo_conv_wh in H as [_ e] ; now inversion e.
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
      + econstructor ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        1: now eapply IHt.
        now symmetry.
    - intros * ? IHn ? IHP ? IHz ? IHs ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
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
      edestruct ih as [? []%sig_ty_inj]; tea.
      split; [now econstructor|now symmetry].
    - intros * ? [ih []] ??????? hconv.
      inversion hconv; subst; clear hconv; refold.
      edestruct ih as [? []%sig_ty_inj]; tea.
      split; [now econstructor|].
      eapply typing_subst1; tea.
      now econstructor.
    - intros * hconve [ihe [? ihme]] ? [ihP] ? [ihhr] ? hm hn * ? hconv.
      inversion hconv; subst; clear hconv; refold.
      edestruct ihe as [? []%id_ty_inj]; tea.
      eapply algo_conv_sound in hconve as [].
      2: edestruct hm as [? [? [[-> ]]]%termGen'] ; now eexists.
      2: edestruct hn as [? [? [[-> ]]]%termGen'] ; now eexists.
      epose proof (idElimConv hm hn) as (?&?&?&[]) ; tea.
      1: eapply TypeRefl ; refold ; boundary.
      now econstructor.
      split.
      + econstructor; tea; eauto.
        * eapply ihP; tea; symmetry.
          eapply idElimMotiveCtxConv ; tea ; eapply idElimMotiveCtx.
          3,4: eapply stability;[|now symmetry].
          4: econstructor; tea.
          all: boundary.
        * eapply ihhr; tea; symmetry.
          eapply typing_subst2; tea.
          cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq.
          now econstructor.
      + eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq.
        econstructor; tea.
        eapply ihme.
        now pose proof hm as [? [? [[]]]%termGen'].
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
      2: inversion H4.
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
      + inversion H2.
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
      2: now inversion H2.
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
      2: now inversion H4.
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
      2: now inversion H1.
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
      2: inversion H4.
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
      symmetry.
      now econstructor.
    - intros * ? [ihA] ? [ihx] ? [ihy] ??? * ? r%red_ty_compl_univ_r hconv.
      inversion hconv; subst; clear hconv.
      1,2: unshelve epose proof (redty_whnf r _); try constructor; congruence.
      2: refold; apply algo_conv_wh in H6 as [? _]; inv_whne.
      econstructor; tea.
      * eapply ihA; tea; do 2 econstructor; boundary.
      * eapply ihx; tea; econstructor; now symmetry.
      * eapply ihy; tea; econstructor; now symmetry.
    - intros * ??? * ? [? [? [? [r]]]]%red_ty_compl_id_r hconv.
      inversion hconv; subst; clear hconv; refold.
      1,2: unshelve epose proof (redty_whnf r _); try constructor; congruence.
      2: refold; apply algo_conv_wh in H3 as [? _]; inv_whne.
      econstructor.
    - intros * Hnconv IH ? ? ? ? * ? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      1-5,7,9,10: now inversion Hnconv.
      1,2: destruct H ;
          now unshelve eapply ty_conv_inj in h ; [now econstructor | now econstructor | cbn in *].
      econstructor ; tea.
      now eapply IH.
Qed.

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
      now eapply algo_conv_ty_expand.
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
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_refl.
        * symmetry.
          now eapply algo_conv_sound in bun_conv_ty0.
      + now do 2 econstructor.
    - intros * convA. 
      pose proof convA as ?%bn_conv_sound.
      revert convA; intros_bn.
      + now econstructor.
      + econstructor; tea; econstructor; tea.
      + econstructor.
        1,2: now reflexivity.
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
      1-2: now eapply inf_conv_decl.
      eapply algo_conv_tm_expand ; tea.
      reflexivity.
    - intros_bn.
      + boundary.
      + eapply algo_conv_sound in bun_conv_ne_conv as [[]%boundary] ; tea.
        gen_typing.
      + eapply algo_conv_sound in bun_conv_ne_conv as [[]%boundary] ; tea.
        gen_typing.
      + econstructor.
        1-3: reflexivity.
        now econstructor.
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
    - intros * [] [] [] ? [] ? []; constructor; tea.
      + boundary.
      + eauto using inf_conv_decl.
      + eauto using inf_conv_decl.
      + econstructor.
        1-3: reflexivity.
        econstructor.
        1-2: eapply isFun_whnf;
          match goal with H : isWfFun _ _ _ ?f |- isFun ?f => destruct H end; constructor;
          match goal with H : [_ |-[bn] ?f ~ ?f : _] |- whne ?f => apply H end.
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
   - intros * [] [] [] ? [] ? [] []; constructor; tea.
      + boundary.
      + eauto using inf_conv_decl.
      + eauto using inf_conv_decl.
      + econstructor.
        1-3: reflexivity.
        econstructor; tea.
        1-2: eapply isPair_whnf;
          match goal with H : isWfPair _ _ _ ?f |- isPair ?f => destruct H end; constructor;
          match goal with H : [_ |-[bn] ?f ~ ?f : _] |- whne ?f => apply H end.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros * convA.
      assert [Γ |-[de] A ≅ A'] by (econstructor; now pose proof convA as ?%bn_conv_sound).
      revert convA; intros_bn.
      + now econstructor.
      + econstructor; tea; now econstructor.
      + econstructor; try reflexivity.
        now econstructor.
    - intros * convA convx.
      pose proof convA as ?%bn_conv_sound.
      pose proof convx as ?%bn_conv_sound.
      revert convA convx; intros_bn.
      + now econstructor.
      + now econstructor.
      + econstructor.
        1: econstructor; tea; now econstructor.
        symmetry; econstructor; tea.
      + econstructor; try reflexivity.
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
    + eapply typing_subst1 ; tea.
      apply algo_conv_sound in bun_conv_ne_conv as []; tea.
      econstructor; eapply lrefl.
      eapply TermConv; tea; refold.
      etransitivity; tea.
      symmetry; econstructor; tea.
      boundary.
  - intros * tyA tyx convA convx convP convhr convy [?????? conve conv].
    pose proof convA as ?%bn_conv_sound.
    pose proof convx as ?%bn_conv_sound.
    pose proof convP as ?%bn_conv_sound.
    pose proof convhr as ?%bn_conv_sound.
    pose proof convy as ?%bn_conv_sound.
    econstructor; tea.
    2,4: now constructor.
    + eexists; econstructor; try boundary.
      apply algo_conv_sound in conve as [? h]; tea.
      econstructor; [boundary|]; tea.
    + eexists; econstructor; try boundary.
      * econstructor; tea; boundary.
      * eapply stability; [boundary|].
        eapply idElimMotiveCtxConv; tea.
        1: now eapply ctx_refl.
        1,2: eapply idElimMotiveCtx.
        4: econstructor; tea.
        all: boundary.
      * econstructor; [now boundary|].
        eapply typing_subst2; tea.
        cbn ; rewrite 2!wk1_ren_on, 2! shift_subst_eq.
        now econstructor.
      * econstructor; tea; boundary.
      * apply algo_conv_sound in conve as [? ]; tea.
        econstructor; [boundary|]; tea.
        etransitivity; tea.
        econstructor; tea.
    + destruct convA, convx, convP, convhr, convy.
      pose proof conv as [?[?[?[[]]]]]%red_ty_compl_id_r.
      econstructor; tea.
      econstructor; constructor + tea.
    + eapply TypeRefl; refold; eapply typing_subst2; tea.
      all: try boundary.
      cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq.
      apply algo_conv_sound in conve as [? ]; tea.
      econstructor; [boundary|]; tea.
  Qed.

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
      now eapply algo_conv_ty_expand.
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
    - intros. gen_typing.
  Qed.

  #[export, refine] Instance ConvTermIntProperties : ConvTermProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros.
      apply (convtm_wk (ta := bn)) ; tea.
      now econstructor.
    - intros * [] [] _ _ _ _ [].
      econstructor ; tea.
      eapply algo_conv_tm_expand ; tea.
      reflexivity.
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
      + do 2 econstructor ; [| |gen_typing].
        all: eapply isFun_whnf;
          match goal with H : isWfFun _ _ _ ?f |- isFun ?f => destruct H end; constructor;
          match goal with H : [_ |-[bni] ?f ~ ?f : _] |- whne ?f => apply H end.
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
        econstructor; [| |gen_typing|gen_typing].
        all: eapply isPair_whnf;
          match goal with H : isWfPair _ _ _ ?f |- isPair ?f => destruct H end; constructor;
          match goal with H : [_ |-[bni] ?f ~ ?f : _] |- whne ?f => apply H end.
    - intros ? HΓ.
      eapply (convtm_empty (ta := bn)).
      now econstructor.
    - intros; gen_typing.
    - intros. gen_typing.
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
    - (* Copy-paste of the proof above in ConvNeuAlgProperties but gen_typing fails (why ?) *)
      intros * tyA tyx convA convx convP convhr convy [?????? conve conv].
      pose proof convA as ?%bn_conv_sound.
      pose proof convx as ?%bn_conv_sound.
      pose proof convP as ?%bn_conv_sound.
      pose proof convhr as ?%bn_conv_sound.
      pose proof convy as ?%bn_conv_sound.
      econstructor; tea.
      2,4: now constructor.
      + eexists; econstructor; try boundary.
        apply algo_conv_sound in conve as [? h]; tea.
        econstructor; [boundary|]; tea.
      + eexists; econstructor; try boundary.
        * econstructor; tea; boundary.
        * eapply stability; [boundary|].
          eapply idElimMotiveCtxConv; tea.
          1: now eapply ctx_refl.
          1,2: eapply idElimMotiveCtx.
          4: econstructor; tea.
          all: boundary.
        * econstructor; [now boundary|].
          eapply typing_subst2; tea.
          cbn ; rewrite 2!wk1_ren_on, 2! shift_subst_eq.
          now econstructor.
        * econstructor; tea; boundary.
        * apply algo_conv_sound in conve as [? ]; tea.
          econstructor; [boundary|]; tea.
          etransitivity; tea.
          econstructor; tea.
      + destruct convA, convx, convP, convhr, convy.
        pose proof conv as [?[?[?[[]]]]]%red_ty_compl_id_r.
        econstructor; tea.
        econstructor; constructor + tea.
      + eapply TypeRefl; refold; eapply typing_subst2; tea.
        all: try boundary.
        cbn; rewrite 2!wk1_ren_on, 2!shift_subst_eq.
        apply algo_conv_sound in conve as [? ]; tea.
        econstructor; [boundary|]; tea.
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
    - intros * ??????? convA convxy convxz.
      pose proof convA as ?%bn_conv_sound.
      pose proof convxy as ?%bn_conv_sound.
      pose proof convxz as ?%bn_conv_sound.
      destruct convA, convxy, convxz.
      econstructor; tea.
      2: eapply redalg_one_step; constructor.
      econstructor; tea.
      econstructor.
      1: econstructor; tea; now econstructor.
      symmetry; econstructor; tea.
      etransitivity; tea; now symmetry.
    - intros * ????? []. 
      econstructor; tea.
      2: now eapply redalg_idElim.
      now econstructor.
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

Lemma algo_conv_tm_complete Γ A t u :
  [Γ |-[de] t ≅ u : A] ->
  [Γ |-[al] t ≅ u : A].
Proof.
  now intros [HΓ ? _ _ []%(escapeTmEq (ta := bni))]%Fundamental.
Qed.