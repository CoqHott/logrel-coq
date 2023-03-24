(** * LogRel.AlgorithmicTyping: definition of algorithmic conversion and typing. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction GenericTyping DeclarativeTyping.

Section Definitions.

  (** We locally disable typing notations to be able to use them in the definition
  here before declaring the right instance. *)
  Close Scope typing_scope.

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
    | typePiCongAlg {Γ na na' A B A' B'} :
      [ Γ |- A ≅ A'] ->
      [ Γ ,, vass na A |- B ≅ B'] ->
      [ Γ |- tProd na A B ≅h tProd na' A' B']
    | typeUnivConvAlg {Γ} :
      [Γ |- U ≅h U]
    | typeNatConvAlg {Γ} :
      [Γ |- tNat ≅h tNat]
    | typeNeuConvAlg {Γ M N T} :
      [ Γ |- M ~ N ▹ T] -> 
      [ Γ |- M ≅h N]
  (** **** Conversion of neutral terms *)
  with ConvNeuAlg : context -> term -> term  -> term -> Type :=
    | neuVarConvAlg {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ~ tRel n ▹ decl.(decl_type)]
    | neuAppCongAlg {Γ m n t u na A B} :
      [ Γ |- m ~h n ▹ tProd na A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp m t ~ tApp n u ▹ B[t..] ]
    | neuNatElimCong {Γ n n' P P' hz hz' hs hs'} :
    (** Here, we know by invariant that the inferred type has to be tNat,
    so there should be no need to check that, but with parameterized/indexed
    inductive we need to recover informations from the neutrals to construct
    the context for the predicate and the type of the branches. *)
      [Γ |- n ~h n' ▹ tNat] ->
      [Γ,, vass anDummy tNat |- P ≅ P'] ->
      [Γ |- hz ≅ hz' : P[tZero..]] ->
      [Γ |- hs ≅ hs' : elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' ▹ P[n..]]
  (** **** Conversion of neutral terms at a type reduced to weak-head normal form*)
  with ConvNeuRedAlg : context -> term -> term -> term -> Type :=
    | neuConvRed {Γ m n A A'} :
      [Γ |- m ~ n ▹ A] ->
      [A ⇒* A'] ->
      isType A' ->
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
    | termPiCongAlg {Γ na na' A B A' B'} :
      [ Γ |- A ≅ A' : U] ->
      [ Γ ,, vass na A |- B ≅ B' : U] ->
      [ Γ |- tProd na A B ≅h tProd na' A' B' : U]
    | termNatReflAlg {Γ} :
      [Γ |- tNat ≅h tNat : U]
    | termZeroReflAlg {Γ} :
      [Γ |- tZero ≅h tZero : tNat]
    | termSuccCongAlg {Γ t t'} :
      [Γ |- t ≅ t' : tNat] ->
      [Γ |- tSucc t ≅h tSucc t' : tNat]
    | termFunConvAlg {Γ : context} {f g na A B} :
      isFun f ->
      isFun g ->
      [ Γ,, vass na A |- eta_expand f ≅ eta_expand g : B] -> 
      [ Γ |- f ≅h g : tProd na A B]
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
    | wfTypeProd {Γ na A B} :
      [Γ |- A ] ->
      [Γ,, vass na A |- B] ->
      [Γ |- tProd na A B]
    | wfTypeNat {Γ} :
      [Γ |- tNat]
    | wfTypeUniv {Γ A} :
      [Γ |- A ◃ U] ->
      [Γ |- A]
  (** **** Type inference *)
  with InferAlg : context -> term -> term -> Type :=
    | infVar {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ▹ decl.(decl_type)]
    | infProd {Γ} {na} {A B} :
      [ Γ |- A ▹h U] -> 
      [Γ ,, (vass na A) |- B ▹h U ] ->
      [ Γ |- tProd na A B ▹ U ]
    | infLam {Γ} {na} {A B t} :
      [ Γ |- A] ->
      [ Γ ,, vass na A |- t ▹ B ] -> 
      [ Γ |- tLambda na A t ▹ tProd na A B]
    | infApp {Γ} {na} {f a A B} :
      [ Γ |- f ▹h tProd na A B ] -> 
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
      [Γ,, vass anDummy tNat |- P] ->
      [Γ |- hz ◃ P[tZero..]] ->
      [Γ |- hs ◃ elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs n ▹ P[n..]]
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
  | conConsAlg {Γ na A} :
    [|- Γ] ->
    [ Γ |- A] ->
    [|- Γ,, vass na A]
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
      now eapply IHB with(ρ := wk_up _ _ ρ).
    - econstructor.
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
      + now eapply (IHP _ (wk_up anDummy tNat ρ)).
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
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
      + now eapply isType_ren. 
    - intros.
      econstructor.
      1-3: eauto using credalg_wk.
      now eauto.
    - intros * ? ? ? IHB ? ?.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ _ ρ).
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? ? ? IH ? ?.
      cbn.
      econstructor.
      1-2: now eauto using isFun_ren.
      specialize IH with(ρ := wk_up _ _ ρ).
      cbn in *.
      asimpl.
      repeat (rewrite renRen_term in IH).
      apply IH.
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
      + now eapply IHB with(ρ := wk_up _ _ ρ).
    - intros.
      now econstructor.
    - now constructor. 
    - intros.
      eapply typing_meta_conv.
      + now econstructor ; eapply in_ctx_wk.
      + reflexivity.
    - intros * ? ? ? IHB.
      cbn.
      econstructor.
      + eauto.
      + now eapply IHB with(ρ := wk_up _ _ ρ).
    - intros * ? ? ? IHt ? ?.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHt with(ρ := wk_up _ _ ρ).
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
      + eapply IHP with (ρ := wk_up _ _ ρ).
      + eapply typing_meta_conv.
        1: eapply IHz.
        now bsimpl.
      + eapply typing_meta_conv.
        1: eapply IHs.
        unfold elimSuccHypTy.
        now bsimpl.
      + now bsimpl.    
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
      (fun (Γ : context) (A B : term) => forall nt T, [Γ,, vass nt T |- A⟨↑⟩ ≅ B⟨↑⟩])
      (fun (Γ : context) (A B : term) => forall nt T, [Γ,, vass nt T |- A⟨↑⟩ ≅h B⟨↑⟩])
      (fun (Γ : context) (A m n : term) => forall nt T, [Γ,, vass nt T |- m⟨↑⟩ ~ n⟨↑⟩ ▹ A⟨↑⟩])
      (fun (Γ : context) (A m n : term) => forall nt T, [Γ,, vass nt T |- m⟨↑⟩ ~h n⟨↑⟩ ▹ A⟨↑⟩])
      (fun (Γ : context) (A t u : term) => forall nt T, [Γ,, vass nt T |- t⟨↑⟩ ≅ u⟨↑⟩ : A⟨↑⟩])
      (fun (Γ : context) (A t u : term) => forall nt T, [Γ,, vass nt T |- t⟨↑⟩ ≅h u⟨↑⟩ : A⟨↑⟩]).
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    all: intros Γ * Hty nt T.
    all: eapply algo_conv_wk in Hty.
    all: specialize (Hty _ (@wk1 Γ nt T)).
    all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ nt T)) ; refold.
    all: now eapply Hty.
  Qed.

  Corollary algo_typing_shift : AlgoTypingInductionConcl
  (fun (Γ : context) (A : term) => forall nt T, [Γ,, vass nt T |- A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall nt T, [Γ,, vass nt T |- t⟨↑⟩ ▹ A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall nt T, [Γ,, vass nt T |- t⟨↑⟩ ▹h A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall nt T, [Γ,, vass nt T |- t⟨↑⟩ ◃ A⟨↑⟩]).
  Proof.
  red.
  repeat match goal with |- _ × _ => split end.
  all: intros Γ * Hty nt T.
  all: eapply algo_typing_wk in Hty.
  all: specialize (Hty _ (@wk1 Γ nt T)).
  all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ nt T)) ; refold.
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
    [× whne t, whne u & isType A].
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