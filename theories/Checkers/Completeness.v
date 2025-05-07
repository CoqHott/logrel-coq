(** * LogRel.Checkers.Completeness: the inductive predicates imply their implementations answer positively. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel Require Import Syntax.All DeclarativeTyping GenericTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import NormalisationDefinition DeclarativeProperties PropertiesDefinition SubstConsequences TypeInjectivityConsequences NeutralConvProperties.
From LogRel.Algorithmic Require Import Bundled TypedConvProperties AlgorithmicTypingProperties.
From LogRel Require Import Utils.

From LogRel.Checkers Require Import Functions Views CtxAccessCorrectness ReductionCorrectness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.
#[global] Unset Asymmetric Patterns.

Import DeclarativeTypingProperties.


(** Completeness of typed conversion *)

Section ConversionComplete.

Import AlgorithmicTypedConvData.

Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

Let PTyEq (Γ : context) (A B : term) :=
  forall v, graph _conv (ty_state;Γ;v;A;B) ok.
Let PTyRedEq (Γ : context) (A B : term) :=
  forall v, graph _conv (ty_red_state;Γ;v;A;B) ok. 
Let PNeEq (Γ : context) (A t u : term) :=
  forall v, graph _conv (ne_state;Γ;v;t;u) (success A).
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall v, graph _conv (ne_red_state;Γ;v;t;u) (success A).
Let PTmEq (Γ : context) (A t u : term) := 
  graph _conv (tm_state;Γ;A;t;u) ok.
Let PTmRedEq (Γ : context) (A t u : term) :=
  graph _conv (tm_red_state;Γ;A;t;u) ok.

Arguments PFun_instance_1 : simpl never.

Lemma implem_conv_complete :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  apply BundledConvInduction.
  - intros * ?? Hconv [IH] [] **.
    unfold graph.
    simp _conv conv_ty ; cbn.
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
    simp _conv conv_ty_red ; cbn.
    econstructor.  1: exact (IHA tt).
    cbn; patch_rec_ret; econstructor.
    1: exact (IHB tt).
    now econstructor.
  - intros ; cbn in *.
    unfold graph.
    simp _conv conv_ty_red ; cbn.
    econstructor.
  - intros.
    unfold graph.
    simp _conv conv_ty_red ; cbn.
    econstructor.
  - intros.
    unfold graph.
    simp _conv conv_ty_red ; cbn.
    econstructor.
  - intros * HA [IHA] HB [IHB] **; cbn in *.
    unfold graph.
    simp _conv conv_ty_red ; cbn.
    econstructor.
    1: exact (IHA tt).
    cbn; patch_rec_ret; econstructor.
    1: exact (IHB tt).
    now econstructor.
  - intros * hA [ihA] hx [ihx] hy [ihy] **; cbn in *.
    unfold graph.
    simp _conv conv_ty_red.
    econstructor.
    1: exact (ihA tt).
    econstructor.
    1: exact ihx.
    cbn; patch_rec_ret; econstructor.
    1: exact ihy.
    now econstructor.
  - intros * ?? HM [IHM ?] **.
    unfold graph.
    simp _conv conv_ty_red ; cbn.
    rewrite whne_ty_view2.
    2-3: now eapply algo_conv_wh in HM as [].
    cbn.
    econstructor.
    1: now exact (IHM tt).
    now constructor.
  - intros **.
    unfold graph.
    simp _conv conv_ne.
    rewrite Nat.eqb_refl ; cbn.
    erewrite ctx_access_complete ; tea ; cbn.
    now econstructor.
  - intros * Hm [IHm ?] Ht [IHt] **.
    unfold graph.
    simp _conv conv_ne ; cbn.
    econstructor.
    1: exact (IHm tt).
    cbn.
    econstructor.
    1: exact IHt.
    now constructor.
  - intros * ? [IHn ?] ? [IHP] ? [IHz] ? [IHs] **.
    unfold graph.
    simp _conv conv_ne ; cbn.
    econstructor.
    1: exact (IHn tt).
    econstructor.
    1: exact (IHP tt).
    econstructor.
    1: exact IHz.
    econstructor.
    1: exact IHs.
    now econstructor.
  - intros * ? [IHe ?] ? [IHP] **.
    unfold graph.
    simp _conv conv_ne ; cbn.
    econstructor.
    1: exact (IHe tt).
    econstructor.
    1: exact (IHP tt).
    now econstructor.
  - intros * ? [IH ?] **.
    unfold graph.
    simp _conv conv_ne; cbn.
    econstructor.
    1: exact (IH tt).
    econstructor.
  - intros * ? [IH ?] **.
    unfold graph.
    simp _conv conv_ne; cbn.
    econstructor.
    1: exact (IH tt).
    econstructor.
  - intros * ? [ihe ?] ? [ihP] ? [ihhr] **.
    unfold graph.
    simp _conv conv_ne; cbn.
    econstructor.
    1: exact (ihe tt).
    econstructor.
    1: do 2 erewrite <- Weakening.wk1_ren_on; exact (ihP tt).
    econstructor.
    1: exact ihhr.
    cbn; patch_rec_ret; econstructor.
  - intros * ? [IHm ?] **.
    unfold graph.
    simp _conv conv_ne_red ; cbn.
    econstructor.
    1: exact (IHm tt).
    econstructor.
    2: now econstructor.
    eapply wh_red_complete_whnf_ty ; tea.
    boundary.
  - intros * ??? []%algo_conv_wh [IHt'] [] **.
    unfold graph.
    simp _conv conv_tm ; cbn -[PFun_instance_1].
    repeat (match goal with |- orec_graph _ _ _ => econstructor end) ; cbn -[PFun_instance_1].
    + eapply wh_red_complete_whnf_ty ; tea.
      1: boundary.
      now gen_typing.
    + eapply wh_red_complete_whnf_tm ; eassumption.
    + eapply wh_red_complete_whnf_tm ; eassumption.
    + exact IHt'.
    + cbn; econstructor.
  - intros * ? [IHA] ? [IHB] **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    econstructor.
    1: exact IHA.
    cbn; patch_rec_ret; econstructor.
    1: exact IHB.
    now constructor.
  - intros.
    unfold graph.
    simp _conv conv_tm_red.
    constructor.
  - intros.
    unfold graph.
    simp _conv conv_tm_red.
    constructor.
  - intros * ? [IHt] **.
    unfold graph.
    simp _conv conv_tm_red; cbn.
    patch_rec_ret; econstructor.
    1: exact IHt.
    now constructor.
  - intros.
    unfold graph.
    simp _conv conv_tm_red.
    now constructor.
  - intros * ?? ? [IHf] **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    patch_rec_ret; econstructor.
    1: exact IHf.
    now constructor.
  - intros * ? [IHA] ? [IHB] **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    econstructor.
    1: exact IHA.
    cbn; patch_rec_ret; econstructor.
    1: exact IHB.
    now constructor.
  - intros * ??? [ihFst] ? [ihSnd] **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    econstructor.
    1: exact ihFst.
    cbn; patch_rec_ret; econstructor.
    1: exact ihSnd.
    now constructor.
  - intros * ? [ihA] ? [ihx] ? [ihy] **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    econstructor.
    1: exact ihA.
    econstructor.
    1:exact ihx.
    cbn; patch_rec_ret; econstructor.
    1: exact ihy.
    now econstructor.
  - intros **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    now econstructor.
  - intros * ? [IHm ?] wP **.
    unfold graph.
    simp _conv conv_tm_red ; cbn.
    unshelve erewrite whne_nf_view3 ; tea.
    2-3: now eapply algo_conv_wh in H as [].
    destruct wP ; cbn.
    all: now econstructor ; [exact (IHm tt)|constructor].
Qed.

Import BundledTypingData.

Corollary implem_conv_complete_ty Γ A B :
  [Γ |-[bn] A ≅ B] ->
  graph tconv (Γ,A,B) ok.
Proof.
  intros.
  unfold graph.
  simp tconv ; cbn.
  econstructor ; cbn.
  - now apply implem_conv_complete.
  - econstructor.
Qed.

End ConversionComplete.

Section TypingImplies.
Import AlgorithmicTypingData.

Context `{ta : tag} `{! ConvType ta}.
Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

Context (conv : (context × term × term) ⇀ exn errors unit).

Hypothesis conv_complete : forall Γ T V,
  [Γ |-[de] T ≅ V] ->
  graph conv (Γ,T,V) ok.

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
- eapply (ne_view1_dest _ (eIdElim _ _ _ _ _)).
Defined.

Lemma can_ty_view1_small T (c : ~ isCanonical T) :
  build_ty_view1 T = ty_view1_small (isCanonical_ty_view1 T c).
Proof.
  destruct T ; cbn.
  all: try solve [case c ; constructor].
  all: reflexivity.
Qed.

Let PTy Γ A := forall v, graph (typing conv) (wf_ty_state;Γ;v;A) ok.
Let PInf Γ A t := forall v, graph (typing conv) (inf_state;Γ;v;t) (success A).
Let PInfRed Γ A t := forall v, whnf A -> graph (typing conv) (inf_red_state;Γ;v;t) (success A).
Let PCheck Γ A t := graph (typing conv) (check_state;Γ;A;t) ok.

Arguments _bind : simpl nomatch.

Theorem typing_complete : BundledTypingInductionConcl PTy PInf PInfRed PCheck.
Proof.
  subst PTy PInf PInfRed PCheck.
  apply BundledTypingInduction.
  all: intros.
  all: prod_hyp_splitter.
  all: unfold graph in *.
  all: simp typing typing_inf typing_wf_ty typing_inf_red typing_check.
  (* Well formed types *)
  1-5:repeat match goal with | |- orec_graph (typing conv) _ _ => patch_rec_ret ; econstructor ; try eauto ; cbn end.
  - cbn in *.
    econstructor.
    1: exact (g1 tt).
    econstructor.
    1: exact g0.
    cbn; patch_rec_ret; econstructor.
    1: exact g.
    now econstructor.
  - unshelve erewrite can_ty_view1_small ; tea.
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
    1: exact (g1 tt whnf_tSort).
    econstructor.
    1: exact g0.
    econstructor.
    1: exact g.
    now econstructor.
  - econstructor.
    1: exact (g0 tt).
    econstructor.
    1: exact g.
    now econstructor.
  - econstructor.
    1: exact (g4 tt).
    econstructor.
    1: exact g3.
    econstructor.
    1: erewrite <- 2!(Weakening.wk1_ren_on) ; exact (g2 tt).
    econstructor.
    1: exact g1.
    econstructor.
    1: exact g0.
    econstructor.
    1: exact g.
    now econstructor.
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
    cbn.
    eapply conv_complete.
    eapply algo_conv_sound in H0.
    all: now boundary.
Qed.

End TypingImplies.