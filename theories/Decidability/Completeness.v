(** * LogRel.Decidability.Completeness: the inductive predicates imply the implementation answer positively. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms Stacks.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicTypingProperties.
From LogRel.Decidability Require Import Functions Soundness.
From PartialFun Require Import Monad PartialFun.

Set Universe Polymorphism.

Import DeclarativeTypingProperties.
Import IndexedDefinitions.

Equations Derive NoConfusion Subterm for term.


Section RedImplemComplete.

  #[local]Definition R_aux := lexprod term term cored term_subterm.

  #[local]Definition R (t u : term × stack) :=
    R_aux (Datatypes.pair (zip (fst t) (snd t)) (fst t)) (Datatypes.pair (zip (fst u) (snd u)) (fst u)).

  #[local]Lemma R_acc t π :
    Acc cored (zip t π) ->
    Acc R (t, π).
  Proof.
  intros h.
  eapply acc_A_B_lexprod with (leA := cored) (leB := term_subterm) (y := t) in h.
  - remember (Datatypes.pair (zip t π) t) as z eqn:e.
    induction h as [z h ih] in t, π, e |- *. subst.
    constructor. intros [v ρ] hr.
    unfold R, R_aux in hr ; cbn in *.
    eapply ih. 2: reflexivity.
    assumption.
  - eapply well_founded_term_subterm.
  - eapply well_founded_term_subterm.
  Qed.

  #[local] Lemma well_typed_acc Γ t π :
    well_formed Γ (zip t π) ->
    Acc R (t,π).
  Proof.
    intros.
    now eapply R_acc, typing_SN.
  Qed.

  Lemma well_typed_zip Γ t π :
    well_typed Γ (zip t π) ->
    ∑ T', [Γ |- t : T'] × (forall u, [Γ |- t ≅ u : T'] -> well_typed Γ (zip u π)).
  Proof.
    intros H.
    induction π as [|[]] in t, H |- * ; cbn.
    - destruct H as [T Hty].
      exists T ; split.
      1: eassumption.
      intros *.
      eexists.
      boundary.
    - cbn in H.
      eapply IHπ in H as (T&(?&[]&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u Htyu.
      eapply Hsubst.
      econstructor.
      1: eapply TermEmptyElimCong ; tea ; refold.
      2: eassumption.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as (T&(?&[]&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u Htyu.
      eapply Hsubst.
      econstructor.
      1: eapply TermNatElimCong ; tea ; refold.
      + now econstructor.
      + now econstructor.
      + now eapply TermRefl.
      + eassumption.
    - cbn in H.
      eapply IHπ in H as (T&(?&(?&?&[])&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u' Htyu.
      eapply Hsubst.
      econstructor.
      1: econstructor ; tea.
      2: eassumption.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as [T [[?[[?[?[->]]]]]%termGen' Hsubst]].
      eexists; split; tea.
      intros; eapply Hsubst.
      eapply TermConv; refold; tea.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as [T [[?[[?[?[->]]]]]%termGen' Hsubst]].
      eexists; split; tea.
      intros; eapply Hsubst.
      eapply TermConv; refold; tea.
      now econstructor.
  Qed.

  Lemma isType_ty Γ T t :
    [Γ |- t : T] ->
    ty_entry t ->
    [Γ |- U ≅ T].
  Proof.
    intros Hty HisT.
    all: inversion HisT ; subst ; clear HisT.
    all: eapply termGen' in Hty as (?&[]&?); subst.
    all: eassumption.
  Qed.

  Lemma zip1_notType Γ T t π :
    ty_entry t ->
    [Γ |- zip1 t π : T] ->
    False.
  Proof.
    intros Ht Hty.
    destruct π ; cbn in * ;
      eapply termGen' in Hty as (?&[]&?) ; subst ; prod_hyp_splitter ;
      match goal with H : [_ |-[de] t : _] |- _ => (unshelve eapply isType_ty, ty_conv_inj in H) end ; tea.
    all: try solve [now econstructor].
    all: now easy.
  Qed.

  Ltac termInvContradiction Hty := 
    eapply termGen' in Hty; cbn in Hty; prod_hyp_splitter; subst;
    now match goal with 
    | [H : [_ |-[de] _ : _] |- _] =>
      eapply termGen' in H; cbn in H; prod_hyp_splitter; subst;
      now match goal with
      | [H : [_ |-[de] _ ≅ _] |- _] => unshelve eapply ty_conv_inj in H; first [constructor | easy]
      end
    end.

  Lemma wh_red_stack_complete Γ t π :
    well_typed Γ (zip t π) ->
    domain wh_red_stack (t,π).
  Proof.
    intros Hty.
    pose proof (Hacc := well_typed_acc _ _ _ Hty).
    change (zip t π) with (zip (fst (t,π)) (snd (t,π))) in *.
    set (z := (t, π)) in *. clearbody z.
    induction Hacc as [z H IH] in Hty |- *.
    apply compute_domain. funelim (wh_red_stack z).
    all: simpl.
    all: try easy.
    all: try solve [ cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *; termInvContradiction Hty].
    - cbn in * ; eapply well_typed_zip in Hty as [? [? _]] ; cbn in *.
      eapply zip1_notType ; tea.
      all: now eapply isType_entry.
    - split ; [|easy].
      eapply IH.
      + red. red. cbn.
        left.
        constructor.
        eapply zip_ored.
        now econstructor.
      + cbn in *.
        eapply well_typed_zip in Hty as (?&[??Hu]).
        eapply Hu, RedConvTeC, subject_reduction ; tea.
        now do 2 econstructor.
  - split ; [|easy].
    eapply IH.
    + red. red. cbn.
      left.
      constructor.
      eapply zip_ored.
      now econstructor.
    + cbn in *.
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *.
    split ; [|easy].
    eapply IH ; cbn in *.
    + red. red. cbn.
      left.
      constructor.
      eapply zip_ored.
      now econstructor.
    + cbn in *.
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *; split; [|easy].
    eapply IH.
    + do 2 red; cbn.
      left; constructor; eapply zip_ored; constructor.
    + cbn. 
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *; split; [|easy].
    eapply IH.
    + do 2 red; cbn.
      left; constructor; eapply zip_ored; constructor.
    + cbn. 
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *.
    split ; [|easy].
    eapply IH ; cbn in *.
    2: eassumption.
    red. red. cbn.
    right.
    econstructor.
    destruct s ; cbn ; now constructor.
  Qed.

  Corollary wh_red_complete Γ t :
    well_formed Γ t ->
    domain wh_red t.
  Proof.
    intros [|w]%well_formed_well_typed.
    all: eapply compute_domain.
    Fail rewrite wh_red_equation_1.
      (* weird, should work? probably the reason why simp also fails? *)
    all: rewrite (wh_red_equation_1 t) ; cbn.
    all: split ; [|easy].
    - eapply wh_red_stack_complete ; tea.
    - inversion w ; subst ; clear w.
      6: eapply wh_red_stack_complete ; now econstructor.
      all: econstructor ; cbn ; red.
      all: simp wh_red_stack ; cbn.
      all: now econstructor.
  Qed.

  Corollary wh_red_complete_whnf_class Γ K t t' :
  [Γ |- t ⇒* t' ∈ K] ->
  whnf t' ->
  graph wh_red t t'.
  Proof.
    intros [] ? ; refold.
    assert (domain wh_red t) as h.
    {
      eapply (wh_red_complete Γ).
      destruct K as [|A] ; unshelve econstructor ; [left|right|..] ; cbn.
      2-3: eassumption.
    }
    replace t' with (def wh_red t h).
    1: eapply def_graph_sound.
    eapply whred_det ; tea.
    all: now eapply red_sound, def_graph_sound.
  Qed.
  
  Corollary wh_red_complete_whnf_ty Γ A A' :
  [Γ |-[de] A] ->
  [A ⇒* A'] ->
  whnf A' ->
  graph wh_red A A'.
  Proof.
    intros ? Hred ?.
    eapply subject_reduction_type in Hred ; tea.
    now eapply wh_red_complete_whnf_class.
  Qed.
  
  Corollary wh_red_complete_whnf_tm Γ A t t' :
  [Γ |-[de] t : A] ->
  [t ⇒* t'] ->
  whnf t' ->
  graph wh_red t t'.
  Proof.
    intros ? Hred ?.
    eapply subject_reduction in Hred ; tea.
    now eapply wh_red_complete_whnf_class.
  Qed.

End RedImplemComplete.

Section ConversionComplete.

Let PTyEq (Γ : context) (A B : term) :=
  forall v, graph conv (ty_state;Γ;v;A;B) (ok tt).
Let PTyRedEq (Γ : context) (A B : term) :=
  forall v, graph conv (ty_red_state;Γ;v;A;B) (ok tt).
Let PNeEq (Γ : context) (A t u : term) :=
  forall v, graph conv (ne_state;Γ;v;t;u) (ok A).
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall v, graph conv (ne_red_state;Γ;v;t;u) (ok A).
Let PTmEq (Γ : context) (A t u : term) := 
  graph conv (tm_state;Γ;A;t;u) (ok tt).
Let PTmRedEq (Γ : context) (A t u : term) :=
  graph conv (tm_red_state;Γ;A;t;u) (ok tt).

Lemma whne_ty_view1 {N} (w : whne N) :
  ∑ w, build_ty_view1 N = ty_view1_small w.
Proof.
  destruct w.
  all: eexists ; cbn.
  all: reflexivity.
Qed.

Lemma whne_nf_view1 {N} (w : whne N) :
  ∑ w, build_nf_view1 N = nf_view1_ne w.
Proof.
  destruct w.
  all: eexists ; cbn.
  all: reflexivity.
Qed.

Lemma whne_ty_view2 {M N} (wM : whne M) (wN : whne N) :
  build_nf_ty_view2 M N = ty_neutrals M N.
Proof.
  simp build_nf_ty_view2.
  apply whne_ty_view1 in wM as [? ->], wN as [? ->] ; cbn.
  now reflexivity.
Qed.

Lemma whne_nf_view3 P m n (wP : isPosType P) (wm : whne m) (wn : whne n) :
  build_nf_view3 P m n =
    (match wP with
    | UnivPos => types _ (ty_neutrals m n)
    | _ => neutrals _ m n
    end).
Proof.
  simp build_nf_view3.
  destruct wP ; cbn.
  - rewrite whne_ty_view2 ; cbn ; tea.
    reflexivity.
  - apply whne_nf_view1 in wm as [? ->] ; cbn.
    apply whne_nf_view1 in wn as [? ->] ; cbn.
    easy.
  - apply whne_nf_view1 in wm as [? ->] ; cbn.
    apply whne_nf_view1 in wn as [? ->] ; cbn.
    easy.
  - apply whne_ty_view1 in w as [? ->] ; cbn.
    easy.
Qed.

Arguments PFun_instance_1 : simpl never.


(* The combinator rec throws in a return branch with a type 
  necessarily convertible to the result type, but the syntactic 
  mismatch between the 2 types prevents `rec_graph` from `apply`ing.
  This tactic fixes the type in the return branch to what's expected
  syntactically. *)
Ltac patch_rec_ret :=
  try (unfold rec;
  match goal with 
  | |- orec_graph _ (_rec _ (fun _ : ?Bx => _)) ?hBa => 
    let Ba := type of hBa in change Bx with Ba
  end).

Lemma implem_conv_complete :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  apply BundledConvInduction.
  - intros * ?? Hconv [IH] **.
    unfold graph.
    simp conv conv_ty ; cbn.
    repeat (match goal with |- orec_graph _ _ _ => econstructor end) ; cbn.
    + eapply wh_red_complete_whnf_ty ; tea.
      eapply algo_conv_wh in Hconv as [].
      gen_typing.
    + eapply wh_red_complete_whnf_ty ; tea.
      eapply algo_conv_wh in Hconv as [].
      gen_typing.
    + exact (IH tt). (* eapply fails with universe issues? *)
    + cbn; econstructor.
  - intros * HA [IHA] HB [IHB] ** ; cbn in *.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.  1: exact (IHA tt).
    cbn; patch_rec_ret; econstructor.
    1: exact (IHB tt).
    now econstructor.
  - intros ; cbn in *.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
  - intros.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
  - intros.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
  - intros * HA [IHA] HB [IHB] **; cbn in *.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
    1: exact (IHA tt).
    cbn; patch_rec_ret; econstructor.
    1: exact (IHB tt).
    now econstructor.
  - intros * HM [IHM []] **.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    rewrite whne_ty_view2.
    2-3: now eapply algo_conv_wh in HM as [].
    cbn.
    econstructor.
    1: now exact (IHM tt).
    now constructor.
  - intros **.
    unfold graph.
    simp conv conv_ne.
    rewrite Nat.eqb_refl ; cbn.
    erewrite ctx_access_complete ; tea ; cbn.
    now econstructor.
  - intros * Hm [IHm []] Ht [IHt] **.
    unfold graph.
    simp conv conv_ne ; cbn.
    econstructor.
    1: exact (IHm tt).
    cbn.
    econstructor.
    1: exact IHt.
    now constructor.
  - intros * ? [IHn []] ? [IHP] ? [IHz] ? [IHs] **.
    unfold graph.
    simp conv conv_ne ; cbn.
    econstructor.
    1: exact (IHn tt).
    econstructor.
    1: exact (IHP tt).
    econstructor.
    1: exact IHz.
    econstructor.
    1: exact IHs.
    now econstructor.
  - intros * ? [IHe []] ? [IHP] **.
    unfold graph.
    simp conv conv_ne ; cbn.
    econstructor.
    1: exact (IHe tt).
    econstructor.
    1: exact (IHP tt).
    now econstructor.
  - intros * ? [IH []] **.
    unfold graph.
    simp conv conv_ne; cbn.
    econstructor.
    1: exact (IH tt).
    econstructor.
  - intros * ? [IH []] **.
    unfold graph.
    simp conv conv_ne; cbn.
    econstructor.
    1: exact (IH tt).
    econstructor.
  - intros * ? [IHm []] **.
    unfold graph.
    simp conv conv_ne_red ; cbn.
    econstructor.
    1: exact (IHm tt).
    econstructor.
    2: now econstructor.
    eapply wh_red_complete_whnf_ty ; tea.
    boundary.
  - intros * ??? []%algo_conv_wh [IHt'] **.
    unfold graph.
    simp conv conv_tm ; cbn -[PFun_instance_1].
    repeat (match goal with |- orec_graph _ _ _ => econstructor end) ; cbn -[PFun_instance_1].
    + eapply wh_red_complete_whnf_ty ; tea.
      1: boundary.
      now gen_typing.
    + now eapply wh_red_complete_whnf_tm.
    + now eapply wh_red_complete_whnf_tm.
    + exact IHt'.
    + cbn; econstructor.
  - intros * ? [IHA] ? [IHB] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    econstructor.
    1: exact IHA.
    cbn; patch_rec_ret; econstructor.
    1: exact IHB.
    now constructor.
  - intros.
    unfold graph.
    simp conv conv_tm_red.
    constructor.
  - intros.
    unfold graph.
    simp conv conv_tm_red.
    constructor.
  - intros * ? [IHt] **.
    unfold graph.
    simp conv conv_tm_red; cbn.
    patch_rec_ret; econstructor.
    1: exact IHt.
    now constructor.
  - intros.
    unfold graph.
    simp conv conv_tm_red.
    now constructor.
  - intros * ?? ? [IHf] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    patch_rec_ret; econstructor.
    1: exact IHf.
    now constructor.
  - intros * ? [IHA] ? [IHB] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    econstructor.
    1: exact IHA.
    cbn; patch_rec_ret; econstructor.
    1: exact IHB.
    now constructor.
  - intros * ??? [ihFst] ? [ihSnd] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    econstructor.
    1: exact ihFst.
    cbn; patch_rec_ret; econstructor.
    1: exact ihSnd.
    now constructor.
  - intros * ? [IHm []] wP **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    unshelve erewrite whne_nf_view3 ; tea.
    2-3: now eapply algo_conv_wh in H as [].
    destruct wP ; cbn.
    all: now econstructor ; [exact (IHm tt)|constructor].
Qed.

End ConversionComplete.

Section TypingComplete.
(* 
Definition isCanonical_ty_view1 t (c : ~ isCanonical t) : ne_view1 t.
Proof.
revert c.
case t ; intros.
all: try solve [case c ; constructor].
- constructor.
- eapply (ne_view1_dest _ (eApp _)).
- eapply (ne_view1_dest _ (eNatElim _ _ _)).
- eapply (ne_view1_dest _ (eEmptyElim _)).
- eapply (ne_view1_dest _ eFst).
- eapply (ne_view1_dest _ eSnd).
Defined. *)

Lemma can_ty_view1_small T (c : ~ isCanonical T) :
  ∑ c', build_ty_view1 T = ty_view1_small c'.
Proof.
  destruct T ; cbn.
  all: try solve [case c ; constructor].
  all: eexists ; reflexivity.
Qed.

Let PTy Γ A := forall v, graph typing (wf_ty_state;Γ;v;A) (ok tt).
Let PInf Γ A t := forall v, graph typing (inf_state;Γ;v;t) (ok A).
Let PInfRed Γ A t := forall v, whnf A -> graph typing (inf_red_state;Γ;v;t) (ok A).
Let PCheck Γ A t := graph typing (check_state;Γ;A;t) (ok tt).

Theorem typing_complete : BundledTypingInductionConcl PTy PInf PInfRed PCheck.
Proof.
  subst PTy PInf PInfRed PCheck.
  apply BundledTypingInduction.
  all: intros.
  all: prod_hyp_splitter.
  all: unfold graph in *.
  all: simp typing typing_inf typing_wf_ty typing_inf_red typing_check ; cbn.
  (* Well formed types *)
  1-5:repeat match goal with | |- orec_graph typing _ _ => econstructor ; try eauto ; cbn end.
  - destruct (can_ty_view1_small _ H) as [? ->].
    cbn.
    econstructor.
    1: exact (g tt whnf_tSort).
    now econstructor.
  (* Infer *)
  - repeat match goal with | |- orec_graph typing _ _ => econstructor ; try eauto ; cbn end.
    erewrite ctx_access_complete ; tea ; cbn.
    now econstructor.
  - econstructor.
    1: exact (g0 tt whnf_tSort).
    econstructor.
    1: exact (g tt whnf_tSort).
    cbn.
    now econstructor.
  - econstructor.
    1: exact (g0 tt).
    cbn.
    econstructor.
    1: exact (g tt).
    now constructor.
  - econstructor.
    1: exact (g0 tt whnf_tProd).
    cbn.
    econstructor.
    1: exact g.
    now constructor.
  - now constructor.
  - now constructor.
  - econstructor.
    1: exact (g tt whnf_tNat).
    now constructor.
  - econstructor.
    1: exact (g2 tt whnf_tNat).
    econstructor.
    1: exact (g1 tt).
    econstructor.
    1: exact g0.
    econstructor.
    1: exact g.
    now constructor.
  - now constructor.
  - econstructor.
    1: exact (g0 tt whnf_tEmpty).
    econstructor.
    1: exact (g tt).
    now constructor.
  - econstructor.
    1: exact (g0 tt whnf_tSort).
    cbn; econstructor.
    1: exact (g tt whnf_tSort).
    cbn; econstructor.
  - econstructor.
    1: exact (g2 tt).
    cbn; econstructor.
    1: exact (g1 tt).
    cbn; econstructor.
    1: exact g0.
    cbn; econstructor.
    1: exact g.
    cbn ; econstructor.
  - econstructor.
    1: exact (g tt whnf_tSig).
    econstructor.
  - econstructor.
    1: exact (g tt whnf_tSig).
    econstructor.
  - econstructor.
    1: exact (g v).
    cbn.
    econstructor.
    2: econstructor.
    eapply wh_red_complete_whnf_ty ; tea.
    boundary.
  - econstructor.
    1: exact (g tt).
    cbn.
    econstructor.
    2: econstructor.
    eapply implem_conv_complete.
    split ; tea.
    now boundary.
Qed.

End TypingComplete.