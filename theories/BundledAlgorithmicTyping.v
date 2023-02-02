From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction GenericTyping DeclarativeTyping Generation Reduction AlgorithmicTyping LogRelConsequences.

Import DeclarativeTypingProperties AlgorithmicTypingData.

Record WfContextBun Γ :=
{
  bn_wf_ctx : [|-[de] Γ] ;
}.

Record WfTypeBun Γ A :=
{
  bun_wf_ty_ctx : [|-[de] Γ] ;
  bun_wf_ty : [Γ |-[al] A] ;
}.

Record InferBun Γ A t :=
{
  bun_inf_ctx : [|-[de] Γ] ;
  bun_inf : [Γ |-[al] t ▹ A]
}.

Record InferRedBun Γ A t :=
{
  bun_inf_red_ctx : [|-[de] Γ] ;
  bun_inf_red : [Γ |-[al] t ▹h A]
}.

Record CheckBun Γ A t :=
{
  bun_chk_ctx : [|-[de] Γ] ;
  bun_chk_ty : [Γ |-[de] A] ;
  bun_chk : [Γ |-[al] t : A]
}.

Record ConvTypeBun Γ A B :=
{
  bun_conv_ty_ctx : [|-[de] Γ] ;
  bun_conv_ty_l : [Γ |-[de] A] ;
  bun_conv_ty_r : [Γ |-[de] B] ;
  bun_conv_ty : [Γ |-[al] A ≅ B]
}.

Record ConvTypeRedBun Γ A B :=
{
  bun_conv_ty_red_ctx : [|-[de] Γ] ;
  bun_conv_ty_red_l : [Γ |-[de] A] ;
  bun_conv_ty_red_wh_l : isType A ;
  bun_conv_ty_red_r : [Γ |-[de] B] ;
  bun_conv_ty_red_wh_r : isType B ;
  bun_conv_ty_red : [Γ |-[al] A ≅h B]
}.

Record ConvTermBun Γ A t u :=
{
  bun_conv_tm_ctx : [|-[de] Γ] ;
  bun_conv_tm_ty : [Γ |-[de] A] ;
  bun_conv_tm_l : [Γ |-[de] t : A] ;
  bun_conv_tm_r : [Γ |-[de] u : A] ;
  bun_conv_tm : [Γ |-[al] t ≅ u : A]
}.

Record ConvTermRedBun Γ A t u :=
{
  bun_conv_tm_red_ctx : [|-[de] Γ] ;
  bun_conv_tm_red_ty : [Γ |-[de] A] ;
  bun_conv_tm_red_wh_ty : isType A ;
  bun_conv_tm_red_l : [Γ |-[de] t : A] ;
  bun_conv_tm_red_wh_l : whnf t ;
  bun_conv_tm_red_r : [Γ |-[de] u : A] ;
  bun_conv_tm_red_wh_r : whnf u ;
  bun_conv_tm_red : [Γ |-[al] t ≅h u : A]
}.

Record ConvNeuBun Γ A m n :=
{
  bun_conv_ne_ctx : [|-[de] Γ] ;
  bun_conv_ne_l : ∑ T, [Γ |-[de] m : T] ;
  bun_conv_ne_wh_l : whne m ;
  bun_conv_ne_r : ∑ T, [Γ |-[de] n : T] ;
  bun_conv_ne_wh_r : whne n ;
  bun_conv_ne : [Γ |-[al] m ~ n ▹ A]
}.

Record ConvNeuRedBun Γ A m n :=
{
  bun_conv_ne_red_ctx : [|-[de] Γ] ;
  bun_conv_ne_red_l : ∑ T, [Γ |-[de] m : T] ;
  bun_conv_ne_red_wh_l : whne m ;
  bun_conv_ne_red_r : ∑ T, [Γ |-[de] n : T] ;
  bun_conv_ne_red_wh_r : whne n ;
  bun_conv_ne_red : [Γ |-[al] m ~h n ▹ A]
}.

Record ConvNeuConvBun Γ A m n :=
{
  bun_conv_ne_conv_ctx : [|-[de] Γ] ;
  bun_conv_ne_conv_l : ∑ T, [Γ |-[de] m : T] ;
  bun_conv_ne_conv_wh_l : whne m ;
  bun_conv_ne_conv_r : ∑ T, [Γ |-[de] n : T] ;
  bun_conv_ne_conv_wh_r : whne n ;
  bun_conv_ne_conv_ty : term ;
  bun_conv_ne_conv : [Γ |-[al] m ~ n ▹ bun_conv_ne_conv_ty] ;
  bun_conv_ne_conv_conv : [Γ |-[de] bun_conv_ne_conv_ty ≅ A]
}.

Record RedTypeBun Γ A B :=
{
  bun_red_ty_ctx : [|-[de] Γ] ;
  bun_red_ty_ty : [Γ |-[de] A] ;
  bun_red_ty : [A ⇒* B] ;
}.

Record RedTermBun Γ A t u :=
{
  bun_red_tm_ctx : [|-[de] Γ] ;
  bun_red_tm_tm : [Γ |-[de] t : A] ;
  bun_red_tm : [t ⇒* u] ;
}.

Module BundledTypingData.

  #[export] Instance WfContext_Bundle : WfContext bn := WfContextBun.
  #[export] Instance WfType_Bundle : WfType bn := WfTypeBun.
  #[export] Instance Inferring_Bundle : Inferring bn := InferBun. 
  #[export] Instance InferringRed_Bundle : InferringRed bn := InferRedBun.
  #[export] Instance Checking_Bundle : Typing bn := CheckBun.
  #[export] Instance ConvType_Bundle : ConvType bn := ConvTypeBun.
  #[export] Instance ConvTypeRed_Bundle : ConvTypeRed bn :=  ConvTypeRedBun.
  #[export] Instance ConvTerm_Bundle : ConvTerm bn := ConvTermBun.
  #[export] Instance ConvTermRed_Bundle : ConvTermRed bn := ConvTermRedBun.
  #[export] Instance ConvNeu_Bundle : ConvNeu bn := ConvNeuBun.
  #[export] Instance ConvNeuRed_Bundle : ConvNeuRed bn := ConvNeuRedBun.
  #[export] Instance ConvNeuConv_Bundle : ConvNeuConv bn := ConvNeuConvBun.
  #[export] Instance RedType_Bundle : RedType bn := RedTypeBun.
  #[export] Instance RedTerm_Bundle : RedTerm bn := RedTermBun.

  Ltac fold_bun :=
    change WfContextBun with (wf_context (ta := bn)) in *;
    change WfTypeBun with (wf_type (ta := bn)) in *;
    change InferBun with (inferring (ta := bn)) in * ;
    change InferRedBun with (infer_red (ta := bn)) in * ;
    change CheckBun with (typing (ta := bn)) in * ;
    change ConvTypeBun with (conv_type (ta := bn)) in * ;
    change ConvTermBun with (conv_term (ta := bn)) in * ;
    change ConvNeuBun with (conv_neu (ta := bn)) in * ;
    change ConvTypeRedBun with (conv_type_red (ta := bn)) in * ;
    change ConvTermRedBun with (conv_term_red (ta := bn)) in * ;
    change ConvNeuRedBun with (conv_neu_red (ta := bn)) in *;
    change ConvNeuConvBun with (conv_neu_conv (ta := bn)) in *;
    change RedTypeBun with (red_ty (ta := bn)) in * ;
    change RedTermBun with (red_tm (ta := bn)) in *.

End BundledTypingData.

Import BundledTypingData.

Set Universe Polymorphism.

Section BundledConv.
  Universe u.

  Context (PTyEq PTyRedEq : context -> term -> term -> Type@{u})
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type@{u}).

  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTyEq ?Γ ?A ?B] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> [Γ |-[de] B] -> Hyp)
    | context [PTyRedEq ?Γ ?A ?B] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> [Γ |-[de] B] -> Hyp)
    | context [PNeEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> (∑ T, [Γ |-[de] t : T]) -> (∑ T, [Γ |-[de] u : T]) -> Hyp)
    | context [PNeRedEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> (∑ T, [Γ |-[de] t : T]) -> (∑ T, [Γ |-[de] u : T]) -> Hyp)
    | context [PTmEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> ([Γ |-[de] t : A]) -> ([Γ |-[de] u : A]) -> Hyp)
    | context [PTmRedEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> ([Γ |-[de] t : A]) -> ([Γ |-[de] u : A]) -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTyEq ?Γ ?A ?B] =>
        context C [PTyEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PTyRedEq ?Γ ?A ?B] =>
        context C [PTyRedEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PNeEq ?Γ ?A ?m ?n] =>
        context C [PNeEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PNeRedEq ?Γ ?A ?m ?n] =>
        context C [PNeRedEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PTmEq ?Γ ?A ?t ?u] =>
        context C [PTmEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | context C [PTmRedEq ?Γ ?A ?t ?u] =>
        context C [PTmRedEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A ≅ ?B] => constr:([Γ |-[bn] A ≅ B])
      | [?Γ |-[al] ?A ≅h ?B] => constr:([Γ |-[bn] A ≅h B])
      | [?Γ |-[al] ?t ≅ ?u : ?A] => constr:([Γ |-[bn] t ≅ u : A])
      | [?Γ |-[al] ?t ≅h ?u : ?A] => constr:([Γ |-[bn] t ≅h u : A])
      | [?Γ |-[al] ?m ~ ?n ▹ ?A] => constr:([Γ |-[bn] m ~ n ▹ A])
      | [?Γ |-[al] ?m ~h ?n ▹ ?A] => constr:([Γ |-[bn] m ~h n ▹ A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  (* Eval cbn beta in ltac:(let T := strong_step (forall (Γ : context) (na na' : aname) (A B A' B' : term),
    [Γ |-[ al ] A ≅ A'] ->
    PTyEq Γ A A' ->
    [Γ,, vass na A |-[ al ] B ≅ B'] ->
    PTyEq (Γ,, vass na A) B B' -> PTyRedEq Γ (tProd na A B) (tProd na' A' B')) in exact T).
  *)

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      (* | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl') *)
      | (?Chd * ?Ctl)%type => let Chd' := strong_concl Chd in (* constr:(Chd') *) let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | (?Chd * ?Ctl)%type => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  Definition t0 := ltac:(let t := type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) in exact t).

  Definition algo_conv_discipline_stmt := 
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq)) in
      let ind := strong_statement t in
      exact ind).

  Let PTyEq'  (c : context) (t t1 : term) :=
    [ |-[ de ] c] ->
    [c |-[ de ] t] -> [c |-[ de ] t1] -> PTyEq c t t1 × [c |-[ de ] t ≅ t1].

  Let PTyRedEq' (c : context) (t t1 : term) :=
    [ |-[ de ] c] ->
    [c |-[ de ] t] -> [c |-[ de ] t1] -> PTyRedEq c t t1 × [c |-[ de ] t ≅ t1].
 
 Let PNeEq' (c : context) (t t1 t2 : term) :=
   [ |-[ de ] c] ->
   (∑ T : term, [c |-[ de ] t1 : T]) ->
   (∑ T : term, [c |-[ de ] t2 : T]) ->
   PNeEq c t t1 t2
   × [× [c |-[ de ] t1 ≅ t2 : t],
        forall T : term, [c |-[ de ] t1 : T] -> [c |-[ de ] t ≅ T]
       & forall T : term, [c |-[ de ] t2 : T] -> [c |-[ de ] t ≅ T]].

  Let PNeRedEq' (c : context) (t t1 t2 : term) :=
     [ |-[ de ] c] ->
     (∑ T : term, [c |-[ de ] t1 : T]) ->
     (∑ T : term, [c |-[ de ] t2 : T]) ->
     PNeRedEq c t t1 t2
     × [× [c |-[ de ] t1 ≅ t2 : t],
          forall T : term, [c |-[ de ] t1 : T] -> [c |-[ de ] t ≅ T]
         & forall T : term, [c |-[ de ] t2 : T] -> [c |-[ de ] t ≅ T]].

  Let PTmEq' (c : context) (t t1 t2 : term) :=
       [ |-[ de ] c] ->
       [c |-[ de ] t1 : t] ->
       [c |-[ de ] t2 : t] -> PTmEq c t t1 t2 × [c |-[ de ] t1 ≅ t2 : t].

  Let PTmRedEq' (c : context) (t t1 t2 : term) :=
         [ |-[ de ] c] ->
         [c |-[ de ] t1 : t] ->
         [c |-[ de ] t2 : t] -> PTmRedEq c t t1 t2 × [c |-[ de ] t1 ≅ t2 : t].

  Theorem algo_conv_discipline : algo_conv_discipline_stmt.
  Proof.
    unfold algo_conv_discipline_stmt; intros.
    destruct (AlgoConvInduction PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq') as [?[?[?[?[?]]]]].
    all: subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'; cbn in *.
    12:{ cbn in *. repeat (split; [assumption|]); assumption. }
    - intros * HA HB ? IHA' ? ? ?.
      pose proof (HA' := HA).
      pose proof (HB' := HB).
      eapply subject_reduction_type, RedConvTyC in HA', HB' ; tea.
      pose proof (HA'' := HA').
      pose proof (HB'' := HB').
      eapply validity in HA'' as [].
      eapply validity in HB'' as [].
      destruct IHA' ; tea.
      split ; [now eauto|..].
      symmetry in HB'.
      do 2 etransitivity ; tea.
      now econstructor.
    - intros * ? IHA ? IHB ? HP HP'.
      eapply prod_ty_inv in HP as [], HP' as [? HB'].
      assert [Γ,, vass na A |-[de] B'].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_conv_refl.
        now eapply IHA.
      }
      split ; [|gen_typing|..].
      destruct IHB as [].
      1-3: gen_typing.
      now econstructor.
    - intros.
      split ; [now eauto|..].
      now gen_typing.
    - intros * Hconv IH ? HM HN.
      assert [Γ |-[de] M : U].
      {
        eapply algo_conv_wh in Hconv as [neM neN].
        inversion HM ; subst ; clear HM.
        1-2: now inversion neM.
        assumption.
      }
      assert [Γ |-[de] N : U].
      {
        eapply algo_conv_wh in Hconv as [neM neN].
        inversion HN ; subst ; clear HN.
        1-2: now inversion neN.
        assumption.
      }
      split ; [now eauto|..].
      eapply convUniv ; fold_decl.
      now eapply IH.
    - intros * Hin ? [] _.
      split ; [now eauto|..].
      split.
      + do 2 constructor ; fold_decl ; gen_typing.
      + intros T Hty.
        eapply termGen' in Hty as [? [[? [->]] ?]].
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
      + intros T Hty.
        eapply termGen' in Hty as [? [[? [->]] ?]].
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
    - intros * ? IHm ? IHt ? Htym Htyn.
      pose proof Htym as [? Htym'].
      pose proof Htyn as [? Htyn'].
      eapply termGen' in Htym' as [? [(?&?&?&[-> Htym' ]) ?]].
      eapply termGen' in Htyn' as [? [(?&?&?&[-> Htyn' ]) ?]].
      edestruct IHm as [? [IHmc IHm' IHn']].
      1: easy.
      1-2: now econstructor.
      unshelve eapply IHm', prod_ty_inj in Htym' as [].
      unshelve eapply IHn', prod_ty_inj in Htyn' as [].
      edestruct IHt.
      1: easy.
      1-2: now gen_typing.
      split ; [now eauto|..].
      split.
      + econstructor ; fold_decl ; gen_typing.
      + intros ? Happ.
        eapply termGen' in Happ as [? [(?&?&?&[-> Htym']) ?]].
        eapply IHm', prod_ty_inj in Htym' as [].
        etransitivity ; [..|eassumption].
        eapply typing_subst1 ; tea.
        now econstructor.
      + intros ? Happ.
        eapply termGen' in Happ as [? [(?&?&?&[-> Htyn']) ?]].
        eapply IHn', prod_ty_inj in Htyn' as [HA ?].
        etransitivity ; [..|eassumption].
        eapply typing_subst1.
        2: eassumption.
        symmetry in HA.
        now gen_typing.
    - intros * ? IHm HA ? ? Htym Htyn.
      pose proof Htym as [? Htym'].
      pose proof Htyn as [? Htyn'].
      edestruct IHm as [_ [IHmc IHm' IHn']].
      1: easy.
      1-2: now eexists.
      pose proof (HA' := HA).
      eapply subject_reduction_type, RedConvTyC in HA'.
      2: now eapply validity in IHmc as [].
      split ; [now eauto|..].
      split.
      + gen_typing.
      + intros.
        symmetry in HA'.
        etransitivity ; gen_typing.
      + intros.
        symmetry in HA'.
        etransitivity ; gen_typing.
    - intros * HA Ht Hu ? IH ? Htyt Htyu.
      pose proof (HA' := HA).
      pose proof (Ht' := Ht).
      pose proof (Hu' := Hu).
      eapply subject_reduction_type, RedConvTyC in HA'.
      2: now eapply validity in Htyt.
      eapply subject_reduction, RedConvTeC in Ht' ; tea.
      eapply subject_reduction, RedConvTeC in Hu' ; tea.
      pose proof (Ht'' := Ht').
      pose proof (Hu'' := Hu').
      eapply validity in Ht'' as [], Hu'' as [].
      split ; [now gen_typing|..].
      etransitivity ; [..|etransitivity].
      1: eassumption.
      2: now symmetry.
      eapply TermConv ; fold_decl.
      2: now symmetry.
      eapply IH.
      all: gen_typing.
    - intros * ? IHA ? IHB ? Hty Hty'.
      pose proof (Htyd := Hty).
      pose proof (Htyd' := Hty').
      eapply termGen' in Htyd as [? [[->] _]].
      eapply termGen' in Htyd' as [? [[->] _]].
      assert [Γ,, vass na A |-[de] B' : U].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_conv_refl.
        now econstructor.
      }
      split ; [now gen_typing|..].
      econstructor ; fold_decl.
      + now econstructor.
      + now eapply IHA.
      + now eapply IHB ; gen_typing.
    - intros * ? ? ? IH ? Hf Hg.
      assert [Γ |-[de] A]
        by (now eapply validity, prod_ty_inv in Hf).
      pose proof (Hf' := Hf).
      pose proof (Hg' := Hg).
      eapply typing_eta' in Hf'.
      eapply typing_eta' in Hg'.
      split ; [now gen_typing|..].
      econstructor ; fold_decl ; tea.
      now eapply IH ; gen_typing.
    - intros * ? IHm ? ? Htym Htyn.
      edestruct IHm as [? [? Hm']].
      1: easy.
      1-2: now eexists.
      split ; [now eauto|..].
      eapply TermConv ; tea ; fold_decl.
      now eapply Hm'.
  Qed.

  Definition BundledConvInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) in
      let t' := weak_statement t in exact t').

  Corollary BundledConvInduction :
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat split.
    all: intros * [].
    all: apply algo_conv_discipline ; assumption.
  Qed.

End BundledConv.

Section ConvSoundness.

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

  Theorem conv_sound : AlgoConvInductionConcl PTyEq PTyEq PNeEq PNeEq PTmEq PTmEq.
  Proof.
    subst PTyEq PTmEq PNeEq.
    red.
    pose proof (algo_conv_discipline 
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)) as [H' H].
    1-11: now constructor.
    repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : sigT _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
    intros ; apply H ; gen_typing.
  Qed.

End ConvSoundness.

Section BundledTyping.

  Context (PTy : context -> term -> Type)
    (PInf PInfRed PCheck : context -> term -> term -> Type).

  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTy ?Γ ?A] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInf ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInfRed ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PCheck ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTy ?Γ ?A] =>
        context C [PTy Γ A × [Γ |-[de] A]]
    | context C [PInf ?Γ ?A ?t] =>
        context C [PInf Γ A t × [Γ |-[de] t : A]]
    | context C [PInfRed ?Γ ?A ?t] =>
        context C [PInfRed Γ A t × [Γ |-[de] t : A]]
    | context C [PCheck ?Γ ?A ?t] =>
        context C [PCheck Γ A t × [Γ |-[de] t : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A] => constr:([Γ |-[bn] A])
      | [?Γ |-[al] ?t ▹ ?A] => constr:([Γ |-[bn] t ▹ A])
      | [?Γ |-[al] ?t ▹h ?A] => constr:([Γ |-[bn] t ▹h A])
      | [?Γ |-[al] ?t : ?A] => constr:([Γ |-[bn] t : A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  Theorem algo_typing_discipline : ltac:(
    let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
    let ind := strong_statement t in
    exact ind).
  Proof.
    intros.
    eapply AlgoTypingInduction.
    1-6: solve [intros ;
      repeat unshelve (
        match reverse goal with
          | IH : context [prod] |- _ => destruct IH ; [..|shelve] ; gen_typing
        end) ;
      now split ; [|econstructor] ; eauto].
    - intros * ? IHI ? IHC ?.
      destruct IHI as [? IHt].
      1: gen_typing.
      destruct IHC ; tea.
      1: now eapply validity, prod_ty_inv in IHt as [].
      split ; [|econstructor] ; eauto.
    - intros * ? IH HA ?.
      destruct IH as [? IH] ; tea.
      split ; [eauto|..].
      econstructor ; tea.
      eapply subject_reduction_type, RedConvTyC in HA.
      1: eassumption.
      now eapply validity in IH.
    - intros * ? IHt HA ?.
      destruct IHt as [? IHt] ; eauto.
      split ; [eauto|].
      econstructor ; tea.
      eapply conv_sound in HA ; tea.
      now eapply validity in IHt.
  Qed.

  Definition BundledTypingInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoTypingInductionConcl PTy PInf PInfRed PCheck) in
      let t' := weak_statement t in exact t').

  Corollary BundledTypingInduction :
    ltac:(
      let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat match goal with |- prod _ _ => split end.
    all: intros * [].
    all: apply algo_typing_discipline ; assumption.
  Qed.

End BundledTyping.

Section TypingSoundness.

  Let PTy (Γ : context) (A : term) :=
    [|-[de] Γ] -> [Γ |-[de] A].
  Let PInf (Γ : context) (A t : term) :=
    [|-[de] Γ] ->
    [Γ |-[de] t : A].
  Let PCheck (Γ : context) (A t : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] t : A].

  Theorem typing_sound : AlgoTypingInductionConcl PTy PInf PInf PCheck.
  Proof.
    subst PTy PInf PCheck.
    red.
    pose proof (algo_typing_discipline 
      (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)) as [H' H].
    1-9: now constructor.
    repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : sigT _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
    intros ; apply H ; gen_typing.
  Qed.

End TypingSoundness.

