(** * LogRel.AlgorithmicTyping: definition of algorithmic conversion and typing. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedContext.
From LogRel Require Import Utils BasicAst Notations NormalForms Weakening UntypedReduction GenericTyping.

Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅h B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |- m ~ n ▹( dn ) T @( dT ) ]" (at level 0, Γ, dn, n, m, T, dT at level 50, only parsing).
Reserved Notation "[ Γ |- m ~h n ▹( dn ) T @( dT ) ]" (at level 0, Γ, dn, n, m, T, dT at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅ t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅h t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).

Section Definitions.

  (** We locally disable typing notations to be able to use them in the definition
  here before declaring the right instance. *)
  Close Scope typing_scope.

(** ** Conversion *)

  (** **** Conversion of types *)
  Inductive ConvTypeAlg : context -> direction -> term -> term  -> Type :=
    | typeConvRed {Γ d A A' B B'} :
      [A ⤳* A'] ->
      [B ⤳* B'] ->
      [Γ |-( d ) A' ≅h B'] ->
      [Γ |-( d ) A ≅ B]
  (** **** Conversion of types reduced to weak-head normal forms *)
  with ConvTypeRedAlg : context -> direction -> term -> term -> Type :=
    | typePiCongAlg {Γ d A B A' B'} :
      [ Γ |-( dir_op d ) A ≅ A'] ->
      [ Γ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B ≅ B'] ->
      [ Γ |-( d ) tProd A B ≅h tProd A' B']
    | typeUnivConvAlg {Γ d} :
      [Γ |-( d ) U ≅h U]
    | typeNeuConvAlg {Γ d M N T dT} :
      [ Γ |- M ~ N ▹( d ) T @( dT ) ] ->
      [ Γ |-( d ) M ≅h N]
  (** **** Conversion of neutral terms *)
  with ConvNeuAlg : context -> direction -> term -> direction -> term -> term -> Type :=
    | neuVarConvAlg {Γ n d T dT} :
      in_ctx Γ n {| ty := T; ty_dir := dT; dir := d |} ->
      [Γ |- tRel n ~ tRel n ▹( d ) T @( dT ) ]
    | neuAppCongAlg {Γ d m n t u A B dA } :
      [ Γ |- m ~h n ▹( d ) tProd A B @( dA ) ] ->
      [ Γ |-( Discr ) t ≅ u : A @( dir_op dA ) ] ->
      [ Γ |- tApp m t ~ tApp n u ▹( d ) B[t..] @( dA ) ]
  (** **** Conversion of neutral terms at a type reduced to weak-head normal form*)
  with ConvNeuRedAlg : context -> direction -> term -> direction -> term -> term -> Type :=
    | neuConvRed {Γ d m n A A' dA } :
      [Γ |- m ~ n ▹( d ) A @( dA ) ] ->
      [A ⤳* A'] ->
      whnf A' ->
      [Γ |- m ~h n ▹( d ) A' @( dA ) ]
  (** **** Conversion of terms *)
  with ConvTermAlg : context -> direction -> term -> direction -> term -> term -> Type :=
    | termConvRed {Γ d t t' u u' A A' dA } :
      [A ⤳* A'] ->
      [t ⤳* t'] ->
      [u ⤳* u' ] ->
      [Γ |-( d ) t' ≅h u' : A' @( dA ) ] ->
      [Γ |-( d ) t ≅ u : A @( dA ) ]
  (** **** Conversion of terms reduced to a weak-head normal form at a reduced type *)
  with ConvTermRedAlg : context -> direction -> term -> direction -> term -> term -> Type :=
    | termPiCongAlg {Γ d A B A' B'} :
      [ Γ |-( dir_op d ) A ≅ A' : U @( Discr )] ->
      [ Γ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B ≅ B' : U @( Discr )] ->
      [ Γ |-( d ) tProd A B ≅h tProd A' B' : U @( Discr )]
    | termFunConvAlg {Γ : context} {d f g A B dT} :
      whnf f ->
      whnf g ->
      [ Γ,, {| ty := A ; ty_dir := dir_op dT ; dir := Discr |} |-( d ) eta_expand f ≅ eta_expand g : B @( dT )] ->
      [ Γ |-( d ) f ≅h g : tProd A B @( dT ) ]
    | termNeuConvAlg {Γ d d' m n T P dT dP } :
      [Γ |- m ~ n ▹( d ) T @( dT )] ->
      isPosType P ->
      dir_leq d d' ->
      dir_leq dT dP -> (* TODO [TL]: is that necessary? don't you have a well-directed hypothesis for T? *)
      [ Γ |-( d' ) m ≅h n : P @( dT ) ]

  where "[ Γ |-( d ) A ≅ B ]" := (ConvTypeAlg Γ d A B)
  and "[ Γ |-( d ) A ≅h B ]" := (ConvTypeRedAlg Γ d A B)
  and "[ Γ |- m ~ n ▹( d ) T @( dT ) ]" := (ConvNeuAlg Γ d T dT m n)
  and "[ Γ |- m ~h n ▹( d ) T @( dT ) ]" := (ConvNeuRedAlg Γ d T dT m n)
  and "[ Γ |-( d ) t ≅ u : T @( dT ) ]" := (ConvTermAlg Γ d T dT t u)
  and "[ Γ |-( d ) t ≅h u : T @( dT ) ]" := (ConvTermRedAlg Γ d T dT t u)
  and "[ t ⤳ t' ]" := (OneRedAlg t t')
  and "[ t ⤳* t' ]" := (RedClosureAlg t t').

(** ** Typing *)

  (** **** Type well-formation *)
  Inductive WfTypeAlg : context -> term -> Type :=
    | wfTypeU Γ : [ Γ |- U ]
    | wfTypeProd {Γ A B} :
      [Γ |- A ] ->
      [Γ,, A |- B] ->
      [Γ |- tProd A B]
    | wfTypeNat {Γ} :
      [Γ |- tNat]
    | wfTypeEmpty {Γ} :
        [Γ |- tEmpty]
    | wfTypeSig {Γ A B} :
      [Γ |- A ] ->
      [Γ,, A |- B] ->
      [Γ |- tSig A B]
    | wfTypeId {Γ A x y} :
      [Γ |- A] ->
      [Γ |- x ◃ A] ->
      [Γ |- y ◃ A] ->
      [Γ |- tId A x y]
    | wfTypeUniv {Γ A} :
      ~ isCanonical A ->
      [Γ |- A ▹h U] ->
      [Γ |- A]
  (** **** Type inference *)
  with InferAlg : context -> term -> term -> Type :=
    | infVar {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ▹ decl]
    | infProd {Γ} {A B} :
      [ Γ |- A ▹h U] ->
      [Γ ,, A |- B ▹h U ] ->
      [ Γ |- tProd A B ▹ U ]
    | infLam {Γ} {A B t} :
      [ Γ |- A] ->
      [ Γ ,, A |- t ▹ B ] ->
      [ Γ |- tLambda A t ▹ tProd A B]
    | infApp {Γ} {f a A B} :
      [ Γ |- f ▹h tProd A B ] ->
      [ Γ |- a ◃ A ] ->
      [ Γ |- tApp f a ▹ B[a..] ]
    | infNat {Γ} :
      [Γ |- tNat ▹ U]
    | infZero {Γ} :
      [Γ |- tZero ▹ tNat]
    | infSucc {Γ t} :
      [Γ |- t ▹h tNat] ->
      [Γ |- tSucc t ▹ tNat]
    | infNatElim {Γ P hz hs n} :
      [Γ |- n ▹h tNat] ->
      [Γ,, tNat |- P] ->
      [Γ |- hz ◃ P[tZero..]] ->
      [Γ |- hs ◃ elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs n ▹ P[n..]]
    | infEmpty {Γ} :
      [Γ |- tEmpty ▹ U]
    | infEmptyElim {Γ P e} :
      [Γ |- e ▹h tEmpty] ->
      [Γ ,, tEmpty |- P ] ->
      [Γ |- tEmptyElim P e ▹ P[e..]]
    | infSig {Γ} {A B} :
      [ Γ |- A ▹h U] ->
      [Γ ,, A |- B ▹h U ] ->
      [ Γ |- tSig A B ▹ U ]
    | infPair {Γ A B a b} :
      [ Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- a ◃ A] ->
      [Γ |- b ◃ B[a..]] ->
      [Γ |- tPair A B a b ▹ tSig A B]
    | infFst {Γ A B p} :
      [Γ |- p ▹h tSig A B] ->
      [Γ |- tFst p ▹ A]
    | infSnd {Γ A B p} :
      [Γ |- p ▹h tSig A B] ->
      [Γ |- tSnd p ▹ B[(tFst p)..]]
    | infId {Γ A x y} :
      [Γ |- A ▹h U] ->
      [Γ |- x ◃ A] ->
      [Γ |- y ◃ A] ->
      [Γ |- tId A x y ▹ U]
    | infRefl {Γ A x} :
      [Γ |- A] ->
      [Γ |- x ◃ A] ->
      [Γ |- tRefl A x ▹ tId A x x]
    | infIdElim {Γ A x P hr y e} :
      [Γ |- A] ->
      [Γ |- x ◃ A] ->
      [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr ◃ P[tRefl A x .: x..]] ->
      [Γ |- y ◃ A] ->
      [Γ |- e ◃ tId A x y] ->
      [Γ |- tIdElim A x P hr y e ▹ P[e .: y..]]
  (** **** Inference of a type reduced to weak-head normal form*)
  with InferRedAlg : context -> term -> term -> Type :=
    | infRed {Γ t A A'} :
      [Γ |- t ▹ A ] ->
      [ A ⤳* A'] ->
      [Γ |- t ▹h A']
  (** **** Type-checking *)
  with CheckAlg : context -> term -> term -> Type :=
    | checkConv {Γ t A A'} :
      [ Γ |- t ▹ A ] ->
      [ Γ |- A ≅ A'] ->
      [ Γ |- t ◃ A' ]

  where "[ Γ |- A ]" := (WfTypeAlg Γ A)
  and "[ Γ |- t ▹ T ]" := (InferAlg Γ T t)
  and "[ Γ |- t ▹h T ]" := (InferRedAlg Γ T t)
  and "[ Γ |- t ◃ T ]" := (CheckAlg Γ T t).

  (** Context well-formation *)
  Inductive WfContextAlg : context -> Type :=
  | conNilAlg : [|- ε]
  | conConsAlg {Γ A} :
    [|- Γ] ->
    [ Γ |- A] ->
    [|- Γ,, A]
  where "[ |- Γ ]" := (WfContextAlg Γ).

End Definitions.

(** ** Instances *)
Module AlgorithmicTypingData.

  Definition al : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Algo : WfContext al := WfContextAlg.
  #[export] Instance WfType_Algo : WfType al := WfTypeAlg.
  #[export] Instance Inferring_Algo : Inferring al := InferAlg.
  #[export] Instance InferringRed_Algo : InferringRed al := InferRedAlg.
  #[export] Instance Checking_Algo : Checking al := CheckAlg.
  #[export] Instance ConvType_Algo : ConvType al := ConvTypeAlg.
  #[export] Instance ConvTypeRed_Algo : ConvTypeRed al :=  ConvTypeRedAlg.
  #[export] Instance ConvTerm_Algo : ConvTerm al := ConvTermAlg.
  #[export] Instance ConvTermRed_Algo : ConvTermRed al := ConvTermRedAlg.
  #[export] Instance ConvNeu_Algo : ConvNeu al := ConvNeuAlg.
  #[export] Instance ConvNeuRed_Algo : ConvNeuRed al := ConvNeuRedAlg.

  Ltac fold_algo :=
    change WfContextAlg with (wf_context (ta := al)) in * ;
    change WfTypeAlg with (wf_type (ta := al)) in *;
    change InferAlg with (inferring (ta := al)) in * ;
    change InferRedAlg with (infer_red (ta := al)) in * ;
    change CheckAlg with (check (ta := al)) in * ;
    change ConvTypeAlg with (conv_type (ta := al)) in * ;
    change ConvTypeRedAlg with (conv_type_red (ta := al)) in * ;
    change ConvTermAlg with (conv_term (ta := al)) in * ;
    change ConvTermRedAlg with (conv_term_red (ta := al)) in * ;
    change ConvNeuAlg with (conv_neu (ta := al)) in * ;
    change ConvTypeRedAlg with (conv_type_red (ta := al)) in * ;
    change ConvTermRedAlg with (conv_term_red (ta := al)) in * ;
    change ConvNeuRedAlg with (conv_neu_red (ta := al)) in *.

  Smpl Add fold_algo : refold.

End AlgorithmicTypingData.

(** ** Induction principles *)

(** Similarly to declarative typing, we need some massaging to turn the output of
Scheme to something that fits our purpose, and we also define a function that computes
the conclusion of a proof by induction. *)
Section InductionPrinciples.
  Import AlgorithmicTypingData.

Scheme
    Minimality for ConvTypeAlg Sort Type with
    Minimality for ConvTypeRedAlg Sort Type with
    Minimality for ConvNeuAlg Sort Type with
    Minimality for ConvNeuRedAlg Sort Type with
    Minimality for ConvTermAlg Sort Type with
    Minimality for ConvTermRedAlg Sort Type.

Scheme
    Minimality for WfTypeAlg Sort Type with
    Minimality for InferAlg Sort Type with
    Minimality for InferRedAlg Sort Type with
    Minimality for CheckAlg Sort Type.

Combined Scheme _AlgoConvInduction from
    ConvTypeAlg_rect_nodep,
    ConvTypeRedAlg_rect_nodep,
    ConvNeuAlg_rect_nodep,
    ConvNeuRedAlg_rect_nodep,
    ConvTermAlg_rect_nodep,
    ConvTermRedAlg_rect_nodep.

Combined Scheme _AlgoTypingInduction from
    WfTypeAlg_rect_nodep,
    InferAlg_rect_nodep,
    InferRedAlg_rect_nodep,
    CheckAlg_rect_nodep.

Let _AlgoConvInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoConvInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let AlgoConvInductionType :=
  ltac: (let ind := eval cbv delta [_AlgoConvInductionType] zeta
    in _AlgoConvInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma AlgoConvInduction : AlgoConvInductionType.
Proof.
  intros PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq **.
  pose proof (_AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) as H.
  destruct H as [?[?[?[?[?]]]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Qed.

Let _AlgoTypingInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoTypingInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let AlgoTypingInductionType :=
  ltac: (let ind := eval cbv delta [_AlgoTypingInductionType] zeta
    in _AlgoTypingInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma AlgoTypingInduction : AlgoTypingInductionType.
Proof.
  intros PTy PInf PInfRed PCheck **.
  pose proof (_AlgoTypingInduction PTy PInf PInfRed PCheck) as H.
  destruct H as [?[?[?]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Qed.

Definition AlgoConvInductionConcl :=
  ltac:(
    let t := eval cbv delta [AlgoConvInductionType] beta in AlgoConvInductionType in
    let t' := remove_steps t in
    exact t').

Definition AlgoTypingInductionConcl :=
  ltac:(
    let t := eval cbv delta [AlgoTypingInductionType] beta in AlgoTypingInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq : rename.
Arguments AlgoTypingInductionConcl PTy PInf PInfRed PCheck : rename.

(** ** Stability by weakening *)

Section TypingWk.
  Import AlgorithmicTypingData.

  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ),
      [Δ |- A⟨ρ⟩ ≅h B⟨ρ⟩].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ~h u⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
      [Δ |- t⟨ρ⟩ ≅h u⟨ρ⟩ : A⟨ρ⟩].

  Theorem algo_conv_wk :
    AlgoConvInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvInduction.
    - intros.
      econstructor.
      all: eauto using credalg_wk.
    - intros * ? ? ? IHB ? *.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ ρ).
    - econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros * ??? IHB ? *; do 2 rewrite <- wk_sig.
      econstructor.
      1: eauto.
      now eapply IHB.
    - intros; now econstructor.
    - intros.
      now econstructor.
    - intros * ? ? ?.
      eapply convne_meta_conv.
      1: econstructor ; eauto using in_ctx_wk.
      all: reflexivity.
    - intros * ? IHm ? IHt ? ?.
      cbn in *.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + eauto.
      + now asimpl.
      + reflexivity.
    - intros * ? IHn ? IHP ? IHz ? IHs *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tNat ρ)).
      + eapply convtm_meta_conv.
        * eapply IHz.
        * now bsimpl.
        * reflexivity.
      + eapply convtm_meta_conv.
        * eapply IHs.
        * unfold elimSuccHypTy.
          now bsimpl.
        * reflexivity.
      + now bsimpl.
      + now bsimpl.
    - intros * ? IHe ? IHP *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tEmpty ρ)).
      + now bsimpl.
      + now bsimpl.
    - intros * ? IH *; cbn.
      econstructor; now eapply IH.
    - intros ??? A? ? IH *; cbn.
      rewrite (subst_ren_wk_up (A:=A)).
      econstructor; now eapply IH.
    - intros * ? IHe (*?? ?? ??*) ?? ?? ? IHp **; erewrite <-2!wk_idElim, subst_ren_wk_up2.
      econstructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHp; constructor; tea.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
      + gen_typing.
    - intros.
      econstructor.
      1-3: eauto using credalg_wk.
      now eauto.
    - intros * ? ? ? IHB ? ?.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ ρ).
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? ? ? IH ? ?.
      cbn.
      econstructor.
      1-2: gen_typing.
      specialize IH with(ρ := wk_up _ ρ).
      cbn in *.
      assert (eq: forall t, t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨up_ren ρ⟩) by now asimpl.
      do 2 rewrite eq.
      apply IH.
    - intros * ??? IHB *.
      do 2 rewrite <- wk_sig.
      econstructor.
      1: now eauto.
      now eapply IHB.
    - intros * ??? IHfst ? IHsnd *.
      rewrite <- wk_sig.
      econstructor.
      1,2: gen_typing.
      1: eauto.
      rewrite wk_fst, <- subst_ren_wk_up; eauto.
    - intros; econstructor; eauto.
    - intros; econstructor; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using isPosType_ren.
  Qed.

  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [Δ |- A⟨ρ⟩].
  Let PInf (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PInfRed (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |- t⟨ρ⟩ ▹h A⟨ρ⟩].
  Let PCheck (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
  [Δ |- t⟨ρ⟩ ◃ A⟨ρ⟩].

  Theorem algo_typing_wk :
    AlgoTypingInductionConcl PTy PInf PInfRed PCheck.
  Proof.
    subst PTy PInf PInfRed PCheck.
    apply AlgoTypingInduction.
    - constructor.
    - intros * ? ? ? IHB **.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros.
      now econstructor.
    - now constructor.
    - intros * ? ? ? IHB **.
      rewrite <-wk_sig.
      econstructor.
      + now eauto.
      + now eapply IHB.
    - intros; rewrite <- wk_Id; econstructor; eauto.
    - constructor.
      + now intros ?%isCanonical_ren.
      + eauto.
    - intros.
      eapply typing_meta_conv.
      + now econstructor ; eapply in_ctx_wk.
      + reflexivity.
    - intros * ? ? ? IHB.
      cbn.
      econstructor.
      + eauto.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros * ? ? ? IHt ? ?.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHt with(ρ := wk_up _ ρ).
    - intros.
      cbn in *.
      eapply typing_meta_conv.
      + now econstructor.
      + now asimpl.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? IHn ? IHP ? IHz ? IHs *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + eapply typing_meta_conv.
        1: eapply IHz.
        now bsimpl.
      + eapply typing_meta_conv.
        1: eapply IHs.
        unfold elimSuccHypTy.
        now bsimpl.
      + now bsimpl.
    - intros.
      now econstructor.
    - intros * ? IHe ? IHP *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + now bsimpl.
    - intros * ??? IHB *.
      rewrite <- wk_sig.
      econstructor; eauto.
    - intros * ???????? *.
      rewrite <- wk_pair, <-wk_sig.
      econstructor.
      1-3: now eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * ?? *.
      rewrite <- wk_fst; now econstructor.
    - intros ? A ?? ? IH *.
      rewrite <- wk_snd, (subst_ren_wk_up (A:=A)).
      econstructor.
      now eapply IH.
    - intros; rewrite <- wk_Id; econstructor; eauto.
    - intros; rewrite <- wk_refl; econstructor; eauto.
    - intros; erewrite <- wk_idElim, subst_ren_wk_up2; econstructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ); eauto.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
    - intros.
      econstructor.
      + eauto.
      + now eapply algo_conv_wk.
  Qed.

  Corollary algo_conv_shift : AlgoConvInductionConcl
      (fun (Γ : context) (A B : term) => forall T, [Γ,, T |- A⟨↑⟩ ≅ B⟨↑⟩])
      (fun (Γ : context) (A B : term) => forall T, [Γ,, T |- A⟨↑⟩ ≅h B⟨↑⟩])
      (fun (Γ : context) (A m n : term) => forall T, [Γ,, T |- m⟨↑⟩ ~ n⟨↑⟩ ▹ A⟨↑⟩])
      (fun (Γ : context) (A m n : term) => forall T, [Γ,, T |- m⟨↑⟩ ~h n⟨↑⟩ ▹ A⟨↑⟩])
      (fun (Γ : context) (A t u : term) => forall T, [Γ,, T |- t⟨↑⟩ ≅ u⟨↑⟩ : A⟨↑⟩])
      (fun (Γ : context) (A t u : term) => forall T, [Γ,, T |- t⟨↑⟩ ≅h u⟨↑⟩ : A⟨↑⟩]).
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    all: intros Γ * Hty T.
    all: eapply algo_conv_wk in Hty.
    all: specialize (Hty _ (@wk1 Γ T)).
    all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ T)) ; refold.
    all: now eapply Hty.
  Qed.

  Corollary algo_typing_shift : AlgoTypingInductionConcl
  (fun (Γ : context) (A : term) => forall T, [Γ,, T |- A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall T, [Γ,, T |- t⟨↑⟩ ▹ A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall T, [Γ,, T |- t⟨↑⟩ ▹h A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall T, [Γ,, T |- t⟨↑⟩ ◃ A⟨↑⟩]).
  Proof.
  red.
  repeat match goal with |- _ × _ => split end.
  all: intros Γ * Hty T.
  all: eapply algo_typing_wk in Hty.
  all: specialize (Hty _ (@wk1 Γ T)).
  all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ T)) ; refold.
  all: now eapply Hty.
  Qed.

End TypingWk.

(** ** Relation to weak-head normal forms *)

(** We show that the predicates that should apply only to weak-head normal forms/neutrals
indeed imply that the relevant arguments are such weak-head normal forms/neutrals. *)
Section AlgTypingWh.

  Let PTyEq (Γ : context) (A B : term) := True.
  Let PTyRedEq (Γ : context) (A B : term) :=
    isType A × isType B.
  Let PNeEq (Γ : context) (A t u : term) :=
    whne t × whne u.
  Let PNeRedEq (Γ : context) (A t u : term) :=
    [× whne t, whne u & whnf A].
  Let PTmEq (Γ : context) (A t u : term) := True.
  Let PTmRedEq (Γ : context) (A t u : term) :=
    [× whnf t, whnf u & isType A].

  Theorem algo_conv_wh :
    AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
    apply AlgoConvInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter.
    all: try solve [now constructor].
    all: gen_typing.
  Qed.
End AlgTypingWh.


(** ** Determinism: there is at most one inferred type *)

Section AlgoTypingDet.

Import AlgorithmicTypingData.

Let PTyEq (Γ : context) (A B : term) := True.
Let PTyRedEq (Γ : context) (A B : term) := True.
Let PNeEq (Γ : context) (A t u : term) :=
  forall A' u', [Γ |-[al] t ~ u' ▹ A'] -> A' = A.
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall A' u', [Γ |-[al] t ~h u' ▹ A'] -> A' = A.
Let PTmEq (Γ : context) (A t u : term) := True.
Let PTmRedEq (Γ : context) (A t u : term) := True.

Theorem algo_conv_det :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
  apply AlgoConvInduction.
  all: try easy.
  - intros * ? * Hconv.
    inversion Hconv ; subst ; clear Hconv.
    now eapply in_ctx_inj.
  - intros * ? IH ? ? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    apply IH in H6.
    now inversion H6.
  - intros * ? IH ?????? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    apply IH in H3.
    now inversion H3.
  - intros * ? IH ?? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    apply IH in H3.
    now inversion H3.
  - intros * ? IH (*? _ ? _ ? _*) ? _ ? _ ? _ ? _ ? _ * Hconv.
    inversion Hconv; now subst.
  - intros * ? IH ???? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H2 as ->.
    now eapply whred_det.
Qed.

Theorem algo_typing_det :
  AlgoTypingInductionConcl
    (fun _ _ => True)
    (fun Γ A t => forall A', [Γ |-[al] t ▹ A'] -> A' = A)
    (fun Γ A t => whnf A -> forall A', whnf A' -> [Γ |-[al] t ▹h A'] -> A' = A)
    (fun _ _ _ => True).
Proof.
  apply AlgoTypingInduction.
  all: try easy.
  - intros * ? ? Hinf.
    inversion Hinf ; subst ; clear Hinf.
    now eapply in_ctx_inj.
  - intros * ? IHA ? IHB ? Hconv.
    now inversion Hconv.
  - intros * ?? ? IHt ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IHt in H7 ; subst.
    now reflexivity.
  - intros * ? IHf ?? ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IHf in H6.
    2-3:gen_typing.
    now inversion H6.
  - intros * Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ?? ? Hconv.
    now inversion Hconv.
  - intros * ? IH ?????? ? Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ? IH ?? ? Hconv.
    now inversion Hconv.
  - intros * ? IH ??? Hconv.
    now inversion Hconv.
  - intros * ????????? Hconv.
    now inversion Hconv.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; refold.
    apply IH in H3; try constructor.
    now inversion H3.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; refold.
    apply IH in H3; try constructor.
    now inversion H3.
  - intros * ?????? * Hconv; inversion Hconv; now subst.
  - intros * ???? * Hconv; now inversion Hconv.
  - intros * ???????????? * Hconv; now inversion Hconv.
  - intros * ? IH ?? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H3 ; subst.
    now eapply whred_det.
Qed.

End AlgoTypingDet.
