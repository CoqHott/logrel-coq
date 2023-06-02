(** * LogRel.AlgorithmicTyping: definition of algorithmic conversion and typing. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction GenericTyping DeclarativeTyping.

#[global]
Instance ren_map_data {Γ Δ} : Ren1 (Δ ≤ Γ) Map.data Map.data :=
  fun ρ r => Map.mk (Map.srcTy r)⟨ρ⟩ (Map.tgtTy r)⟨ρ⟩ (Map.fn r)⟨ρ⟩ (Map.lst r)⟨ρ⟩.

#[global]
Instance ren_map_opt {Γ Δ} : Ren1 (Δ ≤ Γ) Map.opt Map.opt :=
  fun ρ o => match o with | Map.IsMap r => Map.IsMap r⟨ρ⟩ | Map.IsNotMap r => Map.IsNotMap r⟨ρ⟩ end.

Section Definitions.

  (** We locally disable typing notations to be able to use them in the definition
  here before declaring the right instance. *)
  Close Scope typing_scope.


  Lemma wk_is_map t {Γ Δ} (ρ : Δ ≤ Γ) : is_map t⟨ρ⟩ = is_map t.
  Proof. now destruct t. Qed.

  Lemma wk_compact_map t: 
    forall A {Γ Δ} (ρ : Δ ≤ Γ) 
    (r := compact_map A t) 
    (r' := compact_map A⟨ρ⟩ t⟨ρ⟩),
    (Map.srcTy r)⟨ρ⟩ = Map.srcTy r' ×
    (Map.tgtTy r)⟨ρ⟩ = Map.tgtTy r' ×
    (Map.fn r)⟨ρ⟩ = Map.fn r' ×
    (Map.lst r)⟨ρ⟩ = Map.lst r'.
  Proof.
    induction t; intros; repeat split; try reflexivity.
    1,3: eapply IHt4.
    subst r r'; cbn; f_equal.  1: eapply IHt4.
    f_equal. 1: now bsimpl.
    assert (forall x, x⟨↑⟩⟨upRen_term_term ρ⟩ = x⟨ρ⟩⟨↑⟩) as -> by (intros; now bsimpl).
    do 2 f_equal. eapply IHt4.
  Qed.

  Lemma compact_map_whne A l :
    whne (Map.lst (compact_map A l)) -> whne l.
  Proof.
    induction l in A |- *; cbn; try easy.
    intros; constructor; eauto.
  Qed.

  Lemma wk_map_compact t : forall {Γ Δ} (ρ : Δ ≤ Γ), (Map.compact t)⟨ρ⟩ = Map.compact t⟨ρ⟩.
  Proof.
    induction t; intros; try reflexivity; cbn.
    refold; rewrite <- IHt4.
    destruct (Map.compact t4); cbn; refold.
    2: reflexivity.
    do 2 f_equal. now bsimpl.
  Qed.

  Lemma wk_map_combine t u : forall {Γ Δ} (ρ : Δ ≤ Γ), 
    let r := Map.combine t u in let wkr := Map.combine t⟨ρ⟩ u⟨ρ⟩ in 
    (fst r)⟨ρ⟩ = fst wkr /\ (snd r)⟨ρ⟩ = snd wkr.
  Proof.
    unfold Map.combine; intros; destruct t, u; split; reflexivity.
  Qed.

  Lemma wk_map_extract t u : forall {Γ Δ} (ρ : Δ ≤ Γ), 
    let r := Map.extract t u in let wkr := Map.extract t⟨ρ⟩ u⟨ρ⟩ in 
    (fst r)⟨ρ⟩ = fst wkr /\ (snd r)⟨ρ⟩ = snd wkr.
  Proof.
    unfold Map.extract; intros.
    rewrite <- !wk_map_compact.
    apply wk_map_combine.
  Qed.


  Lemma compact_is_map_whne l r :
    Map.compact l = Map.IsMap r -> 
    whne (Map.lst r) -> whne l.
  Proof.
    induction l in r |- *; cbn; try (easy + discriminate).
    destruct (Map.compact l4) eqn:Eq.
    all:intros [= <-] ?; cbn in *; constructor; tea.
    eapply IHl4; tea; reflexivity.
  Qed.

  Lemma compact_is_not_map_whne l r :
    Map.compact l = Map.IsNotMap r -> 
    whne r -> whne l.
  Proof.
    destruct l; try (cbn; intros [= <-]; easy).
  Qed.

  Lemma map_extract_whne l l' : 
    let r := Map.extract l l' in
    (whne (Map.lst (fst r)) -> whne l) ×
    (whne (Map.lst (snd r)) -> whne l').
  Proof.
    unfold Map.extract.
    destruct (Map.compact l) eqn:E, (Map.compact l') eqn:E'; cbn.
    all: try (split; now (apply compact_is_map_whne + apply compact_is_not_map_whne)).
    split; intros h; inversion h.
  Qed.


(** ** Conversion *)

  (** **** Conversion of types *)
  Inductive ConvTypeAlg : context -> term -> term  -> Type :=
    | typeConvRed {Γ A A' B B'} :
      [A ⇒* A'] ->
      [B ⇒* B'] ->
      [Γ |- A' ≅h B'] ->
      [Γ |- A ≅ B]
  (** **** Conversion of types reduced to weak-head normal forms *)
  with ConvTypeRedAlg : context -> term -> term -> Type :=
    | typePiCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A'] ->
      [ Γ ,, A |- B ≅ B'] ->
      [ Γ |- tProd A B ≅h tProd A' B']
    | typeUnivConvAlg {Γ} :
      [Γ |- U ≅h U]
    | typeNatConvAlg {Γ} :
      [Γ |- tNat ≅h tNat]
    | typeEmptyConvAlg {Γ} :
      [Γ |- tEmpty ≅h tEmpty]
    | typeSigCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A'] ->
      [ Γ ,, A |- B ≅ B'] ->
      [ Γ |- tSig A B ≅h tSig A' B']
    | typeListCongAlg {Γ A A'} :
      [Γ |- A ≅ A'] ->
      [ Γ |- tList A ≅h tList A' ]
    | typeNeuConvAlg {Γ M N T} :
      [ Γ |- M ~ N ▹ T] ->
      [ Γ |- M ≅h N]
  (** **** Conversion of neutral terms *)
  with ConvNeuAlg : context -> term -> term  -> term -> Type :=
    | neuVarConvAlg {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ~ tRel n ▹ decl]
    | neuAppCongAlg {Γ m n t u A B} :
      [ Γ |- m ~h n ▹ tProd A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp m t ~ tApp n u ▹ B[t..] ]
    | neuNatElimCong {Γ n n' P P' hz hz' hs hs'} :
    (** Here, we know by invariant that the inferred type has to be tNat,
    so there should be no need to check that, but with parameterized/indexed
    inductive we need to recover informations from the neutrals to construct
    the context for the predicate and the type of the branches. *)
      [Γ |- n ~h n' ▹ tNat] ->
      [Γ,, tNat |- P ≅ P'] ->
      [Γ |- hz ≅ hz' : P[tZero..]] ->
      [Γ |- hs ≅ hs' : elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' ▹ P[n..]]
    | neuEmptyElimCong {Γ P P' e e'} :
      [Γ |- e ~h e' ▹ tEmpty] ->
      [Γ ,, tEmpty |- P ≅ P'] ->
      [Γ |- tEmptyElim P e ~ tEmptyElim P' e' ▹ P[e..]]
    | neuFstCongAlg {Γ m n A B} :
      [ Γ |- m ~h n ▹ tSig A B ] ->
      [ Γ |- tFst m ~ tFst n ▹ A ]
    | neuSndCongAlg {Γ m n A B} :
      [ Γ |- m ~h n ▹ tSig A B ] ->
      [ Γ |- tSnd m ~ tSnd n ▹ B[(tFst m)..] ]
    | neuMapCompact {Γ A l l'} :
      let rx := Map.extract l l' in
      let r := fst rx in
      let r' := snd rx in
      is_map l || is_map l' ->
      [Γ |- r.(Map.lst) ~h r'.(Map.lst) ▹ tList A ] ->
      [Γ |- r.(Map.tgtTy) ≅ r'.(Map.tgtTy)] ->
      [Γ |- r.(Map.fn) ≅ r'.(Map.fn) : arr r.(Map.srcTy) r.(Map.tgtTy)] ->
      [Γ |- l ~ l' ▹ tList r.(Map.tgtTy)]
  (** **** Conversion of neutral terms at a type reduced to weak-head normal form*)
  with ConvNeuRedAlg : context -> term -> term -> term -> Type :=
    | neuConvRed {Γ m n A A'} :
      [Γ |- m ~ n ▹ A] ->
      [A ⇒* A'] ->
      whnf A' ->
      [Γ |- m ~h n ▹ A']
  (** **** Conversion of terms *)
  with ConvTermAlg : context -> term -> term -> term -> Type :=
    | termConvRed {Γ t t' u u' A A'} :
      [A ⇒* A'] ->
      [t ⇒* t'] ->
      [u ⇒* u' ] ->
      [Γ |- t' ≅h u' : A'] ->
      [Γ |- t ≅ u : A]
  (** **** Conversion of terms reduced to a weak-head normal form at a reduced type *)
  with ConvTermRedAlg : context -> term -> term -> term -> Type :=
    | termPiCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A' : U] ->
      [ Γ ,, A |- B ≅ B' : U] ->
      [ Γ |- tProd A B ≅h tProd A' B' : U]
    | termNatReflAlg {Γ} :
      [Γ |- tNat ≅h tNat : U]
    | termZeroReflAlg {Γ} :
      [Γ |- tZero ≅h tZero : tNat]
    | termSuccCongAlg {Γ t t'} :
      [Γ |- t ≅ t' : tNat] ->
      [Γ |- tSucc t ≅h tSucc t' : tNat]
    | termEmptyReflAlg {Γ} :
      [Γ |- tEmpty ≅h tEmpty : U]
    | termFunConvAlg {Γ : context} {f g A B} :
      whnf f ->
      whnf g ->
      [ Γ,, A |- eta_expand f ≅ eta_expand g : B] -> 
      [ Γ |- f ≅h g : tProd A B]
    | termSigCongAlg {Γ A B A' B'} :
      [ Γ |- A ≅ A' : U] ->
      [ Γ ,, A |- B ≅ B' : U] ->
      [ Γ |- tSig A B ≅h tSig A' B' : U]
    | termPairConvAlg {Γ : context} {p q A B} :
      whnf p ->
      whnf q ->
      [ Γ |- tFst p ≅ tFst q : A] -> 
      [ Γ |- tSnd p ≅ tSnd q : B[(tFst p)..]] -> 
      [ Γ |- p ≅h q : tSig A B]
    | termListCongAlg {Γ A A'} :
      [Γ |- A ≅ A' : U] ->
      [Γ |- tList A ≅h tList A' : U]
    | termNilConvAlg {Γ A A' AT} :
      [Γ |- tNil A ≅h tNil A' : tList AT]
    | termConsCongAlg {Γ A} A' AT {hd hd' tl tl'} :
      [Γ |- hd ≅ hd' : A] ->
      [Γ |- tl ≅ tl' : tList A] ->
      [Γ |- tCons A hd tl ≅h tCons A' hd' tl' : tList AT]
    | termNeuConvAlg {Γ m n T P} :
      [Γ |- m ~ n ▹ T] ->
      isPosType P ->
      [Γ |- m ≅h n : P]

  where "[ Γ |- A ≅ B ]" := (ConvTypeAlg Γ A B)
  and "[ Γ |- A ≅h B ]" := (ConvTypeRedAlg Γ A B)
  and "[ Γ |- m ~ n ▹ T ]" := (ConvNeuAlg Γ T m n)
  and "[ Γ |- m ~h n ▹ T ]" := (ConvNeuRedAlg Γ T m n)
  and "[ Γ |- t ≅ u : T ]" := (ConvTermAlg Γ T t u)
  and "[ Γ |- t ≅h u : T ]" := (ConvTermRedAlg Γ T t u)
  and "[ t ⇒ t' ]" := (OneRedAlg t t')
  and "[ t ⇒* t' ]" := (RedClosureAlg t t').

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
    | wfTypeList {Γ A} :
      [Γ |- A] ->
      [Γ |- tList A]
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
    | infList {Γ A} :
      [Γ |- A ▹h U] ->
      [Γ |- tList A ▹ U]
    | infNil {Γ A} :
      [Γ |- A] ->
      [Γ |- tNil A ▹ tList A]
    | infCons {Γ A hd tl} :
      [Γ |- A] ->
      [Γ |- hd ◃ A] ->
      [Γ |- tl ◃ tList A] ->
      [Γ |- tCons A hd tl ▹ tList A]
    | infMap {Γ A B f l} :
      [Γ |- A] ->
      [Γ |- B] ->
      [Γ |- f ◃ arr A B] ->
      [Γ |- l ◃ tList A] ->
      [Γ |- tMap A B f l ▹ tList B]
  (** **** Inference of a type reduced to weak-head normal form*)
  with InferRedAlg : context -> term -> term -> Type :=
    | infRed {Γ t A A'} :
      [Γ |- t ▹ A ] ->
      [ A ⇒* A'] ->
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

Lemma AlgoConvDefInduction : AlgoConvInductionType.
Proof.
  intros PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq **.
  pose proof (_AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) as H.
  destruct H as [?[?[?[?[?]]]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Defined.

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

Definition _AlgoConvInductionConcl :=
  ltac:(
    let t := eval unfold _AlgoConvInductionType in _AlgoConvInductionType in
    let t' := remove_steps t in
    exact t').


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

Scheme 
    ConvTypeAlg_rect_dep := Induction for ConvTypeAlg Sort Type with
    ConvTypeRedAlg_rect_dep := Induction for ConvTypeRedAlg Sort Type with
    ConvNeuAlg_rect_dep := Induction for ConvNeuAlg Sort Type with
    ConvNeuRedAlg_rect_dep := Induction for ConvNeuRedAlg Sort Type with
    ConvTermAlg_rect_dep := Induction for ConvTermAlg Sort Type with
    ConvTermRedAlg_rect_dep := Induction for ConvTermRedAlg Sort Type.

Scheme
    WfTypeAlg_rect_dep := Induction for WfTypeAlg Sort Type with
    InferAlg_rect_dep := Induction for InferAlg Sort Type with
    InferRedAlg_rect_dep := Induction for InferRedAlg Sort Type with
    CheckAlg_rect_dep := Induction for CheckAlg Sort Type.

Combined Scheme _AlgoConvDepInduction from
    ConvTypeAlg_rect_dep,
    ConvTypeRedAlg_rect_dep,
    ConvNeuAlg_rect_dep,
    ConvNeuRedAlg_rect_dep,
    ConvTermAlg_rect_dep,
    ConvTermRedAlg_rect_dep.

Combined Scheme _AlgoTypingDepInduction from
    WfTypeAlg_rect_dep,
    InferAlg_rect_dep,
    InferRedAlg_rect_dep,
    CheckAlg_rect_dep.

Let _AlgoConvDepInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoConvDepInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let AlgoConvDepInductionType :=
  ltac: (let ind := eval cbv delta [_AlgoConvDepInductionType] zeta
    in _AlgoConvDepInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma AlgoConvDepInduction : AlgoConvDepInductionType.
Proof.
  intros PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq **.
  pose proof (_AlgoConvDepInduction PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq) as H.
  destruct H as [?[?[?[?[?]]]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Qed.

Let _AlgoTypingDepInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoTypingDepInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let AlgoTypingDepInductionType :=
  ltac: (let ind := eval cbv delta [_AlgoTypingDepInductionType] zeta
    in _AlgoTypingDepInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma AlgoTypingDepInduction : AlgoTypingDepInductionType.
Proof.
  intros PTy PInf PInfRed PCheck **.
  pose proof (_AlgoTypingDepInduction PTy PInf PInfRed PCheck) as H.
  destruct H as [?[?[?]]] ; cycle -1.
  1: by_prod_splitter.
  all: assumption.
Qed.

Definition AlgoConvDepInductionConcl :=
  ltac:(
    let t := eval cbv delta [AlgoConvDepInductionType] beta in AlgoConvDepInductionType in
    let t' := remove_steps t in
    exact t').

Definition AlgoTypingDepInductionConcl :=
  ltac:(
    let t := eval cbv delta [AlgoTypingDepInductionType] beta in AlgoTypingDepInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq : rename.
Arguments AlgoTypingInductionConcl PTy PInf PInfRed PCheck : rename.
Arguments AlgoConvDepInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq : rename.
Arguments AlgoTypingDepInductionConcl PTy PInf PInfRed PCheck : rename.

(** ** Size of a derivation for well-founded inductions *)

Class Sized A := size : A -> nat.
Notation "#| x |" := (size x).

Section Size.
  Import AlgorithmicTypingData.
  
  Let PTyEq (Γ : context) (A B : term) := nat.
  Let PTyRedEq (Γ : context) (A B : term) := nat.
  Let PNeEq (Γ : context) (A t u : term) := nat.
  Let PNeRedEq (Γ : context) (A t u : term) := nat.
  Let PTmEq (Γ : context) (A t u : term) := nat.
  Let PTmRedEq (Γ : context) (A t u : term) := nat.

  #[local]
  Ltac sum :=
    match goal with
    | |- nat => refine (S _)
    | |- nat -> _ => let n := fresh "n" in intro n; sum; refine (n + _)
    end.

  Theorem algo_conv_size :
    _AlgoConvInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply _AlgoConvInduction; intros;
      repeat match goal with
      | [H : nat |- _] => revert H
      | [H : _ |- _] => clear H
      end; sum; exact 0.
  Defined.
    
End Size.

#[global] Instance ConvTypeAlgSized Γ A B : Sized (ConvTypeAlg Γ A B). Proof. unfold Sized; apply algo_conv_size. Defined.
#[global] Instance ConvTypeRedAlgSized Γ A B : Sized (ConvTypeRedAlg Γ A B). Proof. unfold Sized; apply algo_conv_size. Defined.
#[global] Instance ConvNeuAlgSized Γ A t u : Sized (ConvNeuAlg Γ A t u). Proof. unfold Sized; apply algo_conv_size. Defined.
#[global] Instance ConvNeuRedAlgSized Γ A t u : Sized (ConvNeuRedAlg Γ A t u). Proof. unfold Sized; apply algo_conv_size. Defined.
#[global] Instance ConvTermAlgSized Γ A t u : Sized (ConvTermAlg Γ A t u). Proof. unfold Sized; apply algo_conv_size. Defined.
#[global] Instance ConvTermRedAlgSized Γ A t u: Sized (ConvTermRedAlg Γ A t u). Proof. unfold Sized; apply algo_conv_size. Defined.

Section SizeLemmas.
  Import AlgorithmicTypingData.
  
  Lemma typeConvRed_size Γ A A' B B'
    (redA : [A ⇒* A'])
    (redB : [B ⇒* B'])
    (conv : [Γ |- A' ≅h B']) :
    #|typeConvRed redA redB conv| = S (#|conv| + 0).
  Proof. reflexivity. Qed.

  
  Lemma typePiCongAlg_size  Γ A B A' B'
    (convA : [ Γ |- A ≅ A'])
    (convB : [ Γ ,, A |- B ≅ B']) :
    #|typePiCongAlg convA convB| = S (#|convB| + (#|convA| + 0)).
  Proof. reflexivity. Qed. 
  
  Lemma typeUnivConvAlg_size  Γ :
    #|@typeUnivConvAlg Γ| = 1.
  Proof. reflexivity. Qed.

  Lemma typeNatConvAlg_size  Γ :
    #|@typeNatConvAlg Γ| = 1.
  Proof. reflexivity. Qed.

  Lemma typeEmptyConvAlg_size  Γ :
    #|@typeEmptyConvAlg Γ| = 1.
  Proof. reflexivity. Qed.

  Lemma typeSigCongAlg_size  Γ A B A' B'
    (convA : [ Γ |- A ≅ A'])
    (convB : [ Γ ,, A |- B ≅ B']) :
    #|typeSigCongAlg convA convB| = S(#|convB| + (#|convA| + 0)).
  Proof. reflexivity. Qed.

  Lemma typeListCongAlg_size  Γ A A'
    (convA :[Γ |- A ≅ A']) :
    #|typeListCongAlg convA| = S (#|convA| + 0).
  Proof. reflexivity. Qed.

  Lemma typeNeuConvAlg_size  Γ M N T
    (inf : [ Γ |- M ~ N ▹ T]) :
    #|typeNeuConvAlg inf| = S (#|inf| + 0).
  Proof. reflexivity. Qed.

Lemma neuVarConvAlg_size  Γ n decl
    (hn : in_ctx Γ n decl) :
    #|neuVarConvAlg hn| = S (n + 0).
Proof. reflexivity. Qed.

Lemma neuAppCongAlg_size  Γ m n t u A B
    (convFun : [ Γ |- m ~h n ▹ tProd A B ])
    (convArg : [ Γ |- t ≅ u : A ]) :
    #|neuAppCongAlg convFun convArg| = S (#|convArg| + (#|convFun| + 0)).
Proof. reflexivity. Qed.

Lemma neuNatElimCong_size  Γ n n' P P' hz hz' hs hs'
  (convn : [Γ |- n ~h n' ▹ tNat])
  (convP : [Γ,, tNat |- P ≅ P'])
  (convhz : [Γ |- hz ≅ hz' : P[tZero..]])
  (convhs : [Γ |- hs ≅ hs' : elimSuccHypTy P]) :
  #|neuNatElimCong convn convP convhz convhs| = S(#|convhs| + (#|convhz| + (#|convP| + (#|convn| + 0)))).
  Proof. reflexivity. Qed.

Lemma neuEmptyElimCong_size  Γ P P' e e'
    (conve : [Γ |- e ~h e' ▹ tEmpty])
    (convP : [Γ ,, tEmpty |- P ≅ P']) :
    #|neuEmptyElimCong conve convP| = S(#|convP| + (#|conve| + 0)).
  Proof. reflexivity. Qed.

Lemma neuFstCongAlg_size  Γ m n A B 
    (convm : [ Γ |- m ~h n ▹ tSig A B ]) :
    #|neuFstCongAlg convm| = S(#|convm| + 0).
  Proof. reflexivity. Qed.

Lemma neuSndCongAlg_size  Γ m n A B 
    (convm : [ Γ |- m ~h n ▹ tSig A B ]) :
    #|neuSndCongAlg convm| = S(#|convm| + 0).
  Proof. reflexivity. Qed.

Lemma neuMapCompact_size  Γ A l l'
    (rx := Map.extract l l') (r := fst rx) (r' := snd rx)
    (hmap : is_map l || is_map l')
    (convlst : [Γ |- r.(Map.lst) ~h r'.(Map.lst) ▹ tList A ])
    (convtgtty : [Γ |- r.(Map.tgtTy) ≅ r'.(Map.tgtTy)])
    (convfn : [Γ |- r.(Map.fn) ≅ r'.(Map.fn) : arr r.(Map.srcTy) r.(Map.tgtTy)]) :
    #|neuMapCompact hmap convlst convtgtty convfn| = S(#|convfn| + (#|convtgtty| + (#|convlst| + 0))).
  Proof. reflexivity. Qed.

Lemma neuConvRed_size  Γ m n A A'
    (conv : [Γ |- m ~ n ▹ A])
    (redA : [A ⇒* A'])
    (whA : whnf A') :
  #|neuConvRed conv redA whA| = S(#|conv| + 0).
  Proof. reflexivity. Qed.

Lemma termConvRed_size  Γ t t' u u' A A'
      (redA : [A ⇒* A'])
      (redt : [t ⇒* t'])
      (redu : [u ⇒* u' ])
      (conv : [Γ |- t' ≅h u' : A']) :
      #|termConvRed redA redt redu conv| = S(#|conv| + 0).
    Proof. reflexivity. Qed.
Lemma termPiCongAlg_size  Γ A B A' B'
      (convA : [ Γ |- A ≅ A' : U])
      (convB : [ Γ ,, A |- B ≅ B' : U]) :
      #|termPiCongAlg convA convB| = S(#|convB| + (#|convA| + 0)).
    Proof. reflexivity. Qed.
Lemma termNatReflAlg_size  Γ :
  #|@termNatReflAlg Γ| = 1.
    Proof. reflexivity. Qed.
Lemma termZeroReflAlg_size  Γ :
      #|@termZeroReflAlg Γ| = 1.
    Proof. reflexivity. Qed.
Lemma termSuccCongAlg_size  Γ t t'
    (convt : [Γ |- t ≅ t' : tNat]) :
    #|termSuccCongAlg convt| = S(#|convt| + 0).
    Proof. reflexivity. Qed.
Lemma termEmptyReflAlg_size  Γ :
#|@termEmptyReflAlg Γ| = 1.
    Proof. reflexivity. Qed.
Lemma termFunConvAlg_size  Γ f g A B
      (whf :whnf f)
      (whg : whnf g)
      (conveta : [ Γ,, A |- eta_expand f ≅ eta_expand g : B]) :
      #|termFunConvAlg whf whg conveta| = S(#|conveta| + 0).
    Proof. reflexivity. Qed.
Lemma termSigCongAlg_size  Γ A B A' B'
    (convA : [ Γ |- A ≅ A' : U])
    (convB : [ Γ ,, A |- B ≅ B' : U]) :
    #|termSigCongAlg convA convB| = S(#|convB| + (#|convA| + 0)).
    Proof. reflexivity. Qed.
Lemma termPairConvAlg_size  Γ p q A B
      (whp : whnf p)
      (whq : whnf q)
      (convfst : [ Γ |- tFst p ≅ tFst q : A])
      (convsnd : [ Γ |- tSnd p ≅ tSnd q : B[(tFst p)..]]) :
      #|termPairConvAlg whp whq convfst convsnd| = S(#|convsnd| + (#|convfst| + 0)).
    Proof. reflexivity. Qed.
Lemma termListCongAlg_size  Γ A A'
      (convA : [Γ |- A ≅ A' : U]) :
      #|termListCongAlg convA| = S(#|convA| + 0).
    Proof. reflexivity. Qed.
Lemma termNilConvAlg_size  Γ A A' AT :
      #|@termNilConvAlg Γ A A' AT| = 1.
    Proof. reflexivity. Qed.
Lemma termConsCongAlg_size  Γ A A' AT hd hd' tl tl'
      (convhd : [Γ |- hd ≅ hd' : A])
      (convtl : [Γ |- tl ≅ tl' : tList A]) :
      #|termConsCongAlg A' AT convhd convtl| = S(#|convtl| + (#|convhd| + 0)).
    Proof. reflexivity. Qed.
Lemma termNeuConvAlg_size  Γ m n T P
      (inf : [Γ |- m ~ n ▹ T])
      (ispos : isPosType P) :
      #|termNeuConvAlg inf ispos| = S(#|inf| + 0).
    Proof. reflexivity. Qed.

End SizeLemmas.

Create HintDb sizeLemmas.
#[global]
Hint Rewrite typeConvRed_size typePiCongAlg_size typeUnivConvAlg_size typeNatConvAlg_size typeEmptyConvAlg_size typeSigCongAlg_size typeListCongAlg_size typeNeuConvAlg_size neuVarConvAlg_size neuAppCongAlg_size neuNatElimCong_size neuEmptyElimCong_size neuFstCongAlg_size neuSndCongAlg_size neuMapCompact_size neuConvRed_size termConvRed_size termPiCongAlg_size termNatReflAlg_size termZeroReflAlg_size termSuccCongAlg_size termEmptyReflAlg_size termFunConvAlg_size termSigCongAlg_size termPairConvAlg_size termListCongAlg_size termNilConvAlg_size termConsCongAlg_size termNeuConvAlg_size : sizeLemmas.

Ltac simpl_size := autorewrite with sizeLemmas; refold.

Arguments algo_conv_size : simpl never.
Arguments size : simpl never.

(* Section Foo.
  Import AlgorithmicTypingData.
  From Coq Require Import Lia.
  Goal forall Γ A B (h : [Γ |-[al] A ≅ B]), True.
  Proof.
      intros.
      pose (h' := h).
      destruct h.
      assert (#|c| < #| h'|).
      unfold h'; cbn.
      unfold h'; simpl_size. lia.


End Foo. *)


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
    - intros.
      now econstructor.  
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
    - intros *.
      intros ? ? ihlst ? ihtgt ? ihfn *.
      pose proof (wk_map_extract l l' ρ) as [fsteq sndeq].
      rewrite <- wk_list.
      change (Map.tgtTy ?x)⟨ρ⟩ with (Map.tgtTy x⟨ρ⟩).
      rewrite fsteq.
      eapply neuMapCompact; refold; rewrite <- ?fsteq, <- ?sndeq.
      + now do 2 rewrite wk_is_map.
      + eapply convne_meta_conv.
        1: eapply ihlst.
        1: reflexivity.
        now symmetry.
      + eapply ihtgt.
      + eapply convtm_meta_conv.
        1: eapply ihfn.
        2: now symmetry.
        now bsimpl.
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
    - intros; cbn.
      econstructor; eauto.
    - intros; cbn.
      econstructor; eauto.
    - intros; cbn.
      econstructor; eauto.
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
    - intros * ? IHA **.
      rewrite <- wk_list.
      econstructor; eauto.
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
    - intros; cbn; econstructor; eauto.
    - intros; cbn; econstructor; eauto.
    - intros; cbn; econstructor; eauto.
    - intros * ????? h **; cbn; econstructor; eauto.
      eapply typing_meta_conv. 1: apply h.
      now bsimpl.
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
    all: try solve [now constructor| now eapply (map_extract_whne l l')].
    all: gen_typing.
  Qed.
End AlgTypingWh.


(** ** Determinism: there is at most one inferred type *)

Section AlgoTypingDet.

Import AlgorithmicTypingData.

Let PTyEq (Γ : context) (A B : term) := True.
Let PTyRedEq (Γ : context) (A B : term) := True.
Let PNeEq (Γ : context) (A t u : term) := 
  forall A', [Γ |-[al] t ~ u ▹ A'] -> A' = A.
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall A', [Γ |-[al] t ~h u ▹ A'] -> A' = A.
Let PTmEq (Γ : context) (A t u : term) := True.
Let PTmRedEq (Γ : context) (A t u : term) := True.

  Ltac no_map :=
    match goal with [H : context c [is_map _] |- _] => cbn in H; inversion H end.


Theorem algo_conv_det :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
  apply AlgoConvInduction.
  all: try easy.
  - intros * ? * Hconv.
    inversion Hconv ; subst ; clear Hconv.
    2: no_map.
    now eapply in_ctx_inj.
  - intros * ? IH ? _ ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    2: no_map.
    apply IH in H6.
    now inversion H6.
  - intros * ? IH ????? _ ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    2: no_map.
    now reflexivity.
  - intros * ? IH ?? ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    2: no_map.
    now reflexivity.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    2: no_map.
    apply IH in H4.
    now inversion H4.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    2: no_map.
    apply IH in H4.
    now inversion H4.
  - intros * hmap ? ih ? _ ? _ ? Hconv.
    inversion Hconv; subst; clear Hconv; refold; try no_map.
    reflexivity.
  - intros * ? IH ??? Hconv.
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
  - intros * ? IH ? Hconv.
    now inversion Hconv.
  - intros * ? _ ? Hconv.
    now inversion Hconv.
  - intros * ? _ ? _ ? _ ? Hconv.
    now inversion Hconv.
  - intros * ? _ ? _ ? _ ? _ ? Hconv.
    now inversion Hconv.
  - intros * ? IH ?? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H3 ; subst.
    now eapply whred_det.
Qed.

End AlgoTypingDet.

(*
From Coq Require Import Lia.
From Equations Require Import Equations.

Derive Signature for ConvTypeAlg.
Derive Signature for ConvTypeRedAlg.
Derive Signature for ConvNeuAlg.
Derive Signature for ConvNeuRedAlg.
Derive Signature for ConvTermAlg.
Derive Signature for ConvTermRedAlg.

Derive NoConfusion for term.
Derive NoConfusion for sort.
Derive NoConfusion for nat.
Derive NoConfusion for list.
Derive NoConfusion for in_ctx.

#[global]
Instance: UIP nat. Proof. typeclasses eauto. Defined.

Section SizeUnicity.
  Import AlgorithmicTypingData.

  (* Definition G := (cons (tList tNat) nil).
  Definition G' := (cons (tList (tApp (idterm U) tNat)) nil).
  Definition t := tRel 0.
  Definition u := tMap tNat tNat (idterm tNat) t.

  Definition f : [G |- t ~ u ▹ tList tNat].
  Proof.
    pose (r := compact_map tNat t).
    pose (r' := compact_map tNat u).
    change tNat with (Map.tgtTy r).
    econstructor; cbn; refold.
    1:easy.
    - econstructor; refold.
      2: reflexivity.
      2: constructor.
      do 2 econstructor.
    - econstructor; refold.
      1,2: reflexivity.
      econstructor.
    - econstructor; refold.
      1-3: reflexivity.
      econstructor; refold.
      1,2: constructor.
      econstructor; refold.
      1: reflexivity.
      1: apply redalg_one_step; constructor.
      + etransitivity.
        1: apply redalg_one_step; constructor.
        refold; cbn.
        etransitivity.
        1: apply redalg_one_step; constructor.
        cbn.
        1: apply redalg_one_step; constructor.
      + refold. cbn.
        econstructor; refold.
        2: constructor.
        econstructor.
        constructor.
  Defined.

  Definition f' : [G' |- t ~ u ▹ tList (tApp (idterm U) tNat)].
  Proof.
    pose (r := compact_map (tApp (idterm U) tNat) t).
    pose (r' := compact_map (tApp (idterm U) tNat) u).
    change (tApp _ _) with (Map.tgtTy r).
    econstructor; cbn; refold.
    1:easy.
    - econstructor; refold.
      2: reflexivity.
      2: constructor.
      econstructor.
      do 2 econstructor.
    - econstructor; refold.
      1: apply redalg_one_step; constructor.
      1: reflexivity.
      cbn; econstructor.
    - econstructor; refold.
      1-3: reflexivity.
      econstructor; refold.
      1,2: constructor.
      econstructor; refold.
      1,2: apply redalg_one_step; constructor.
      + etransitivity.
        1: apply redalg_one_step; constructor.
        refold; cbn.
        etransitivity.
        1: apply redalg_one_step; constructor.
        cbn.
        1: apply redalg_one_step; constructor.
      + refold. cbn.
        econstructor; refold.
        2: constructor.
        econstructor.
        constructor.
  Defined.

  Lemma foo : #|f| = #|f'|.
  Proof. reflexivity. Qed. *)

  
  Let PTyEq (Γ : context) (A B : term) (h1 : [Γ |- A ≅ B]) := 
    forall Δ (h2 : [Δ |- A ≅ B]), #|h1| = #|h2|.
  Let PTyRedEq (Γ : context) (A B : term) (h1 : [Γ |- A ≅h B]) := 
    forall Δ (h2: [Δ |- A ≅h B]), #|h1| = #|h2|.
  Let PNeEq (Γ : context) (A t u : term) (h1: [Γ |- t ~ u ▹ A]) := 
    forall Δ B (h2: [Δ |- t ~ u ▹ B]), #|h1| = #|h2|.
  Let PNeRedEq (Γ : context) (A t u : term) (h1: [Γ |- t ~h u ▹ A]) := 
    forall Δ B (h2: [Δ |- t ~h u ▹ B]), #|h1| = #|h2|.
  Let PTmEq (Γ : context) (A t u : term) (h1: [Γ |- t ≅ u : A]) :=
    forall Δ B (h2: [Δ |- t ≅ u : B]), #|h1| = #|h2|.
  Let PTmRedEq (Γ : context) (A t u : term) (h1: [Γ |- t ≅h u : A]) :=
    forall Δ B (h2: [Δ |- t ≅ u : B]), #|h1| = #|h2|.

  Lemma algo_conv_size_unique : AlgoConvDepInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvDepInduction.
    - intros * ih ? h; destruct h as [?? A'' ? B'']; simpl_size.
      pose proof c as []%algo_conv_wh.
      pose proof c0 as []%algo_conv_wh.
      assert (A' = A'') by (eapply whred_det ; tea; gen_typing).
      assert (B' = B'') by (eapply whred_det ; tea; gen_typing).
      subst. specialize (ih _ c0). lia.
    - intros * ih1 * ih2 ? h2. depind h2; try discriminate.
      2: pose proof c as []%algo_conv_wh; inv_whne.
      refold. specialize (ih1 _ c); specialize (ih2 _ c0).
      simpl_size; lia.
    - intros ?? h; depind h; [reflexivity|].
      refold. pose proof c as []%algo_conv_wh; inv_whne.
    - intros ?? h; depind h; [reflexivity|].
      refold. pose proof c as []%algo_conv_wh; inv_whne.
    - intros ?? h; depind h; [reflexivity|].
      refold. pose proof c as []%algo_conv_wh; inv_whne.
    - intros * ih1 * ih2 ? h; depind h; refold.
      2: pose proof c as []%algo_conv_wh; inv_whne.
      specialize (ih1 _ c); specialize (ih2 _ c0).
      simpl_size; lia.
    - intros * ih ? h ; depind h; refold.
      2: pose proof c as []%algo_conv_wh; inv_whne.
      specialize (ih _ c); simpl_size; lia.
    - intros * ih ? h. 
      pose proof c as []%algo_conv_wh.
      destruct h; try solve [inv_whne]; refold.
      specialize (ih _ _ c0); simpl_size; lia.
    - intros ?????? h; depind h.
      2: cbn in i; inversion i.
      epose (uip H eq_refl); subst.
      cbn in *; subst; simpl_size; reflexivity.
    - intros * ih1 * ih2 ?? h; depind h; refold.
      2: cbn in i; inversion i.
      specialize (ih1 _ _ c); specialize (ih2 _ _ c0); simpl_size; lia.
    - intros * ih1 * ih2 * ih3 * ih4 ?? h; depind h; refold.
      2: cbn in i; inversion i.
      specialize (ih1 _ _ c); specialize (ih2 _ c0); 
      specialize (ih3 _ _ c1); specialize (ih4 _ _ c2); 
       simpl_size; lia.
    - intros * ih1 * ih2 ?? h; depind h; refold. 
      2: cbn in i; inversion i.
      specialize (ih1 _ _ c); specialize (ih2 _ c0); simpl_size; lia.
    - intros * ih ?? h; depind h; refold.
      2: cbn in i; inversion i.
      specialize (ih _ _ c);  simpl_size; lia.
    - intros * ih ?? h; depind h; refold.
      2: cbn in i; inversion i.
      specialize (ih _ _ c);  simpl_size; lia.
    - intros * ih1 * ih2 * ih3 ?? h; depind h; refold.
      (* Uhh !!! *)
      Fail match goal with [ H : (_ || _) |- _ ] => idtac H end.
      all: try (cbn in i; solve [inversion i]).
      1: cbn in i0; solve [inversion i0].
      specialize (ih1 _ _ c). ; specialize (ih2 _ c0); 
      specialize (ih3 _ _ c1);  simpl_size; lia.




  
End SizeUnicity.

*)