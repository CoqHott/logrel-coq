From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction GenericTyping.

Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition here before declaring the right
  instance *)
  Close Scope typing_scope.

  Inductive ConvTypeAlg : context -> term -> term  -> Type :=
    | typeConvRed {Γ A A' B B'} :
      [A ⇒* A'] ->
      [B ⇒* B'] ->
      [Γ |- A' ≅h B'] ->
      [Γ |- A ≅ B]
  with ConvTypeRedAlg : context -> term -> term -> Type :=
    | typePiCongAlg {Γ na na' A B A' B'} :
      [ Γ |- A ≅ A'] ->
      [ Γ ,, vass na A |- B ≅ B'] ->
      [ Γ |- tProd na A B ≅h tProd na' A' B']
    | typeUnivConvAlg {Γ} :
      [Γ |- U ≅h U]
    | typeNeuConvAlg {Γ M N} :
      [ Γ |- M ~h N ▹ U ] -> 
      [ Γ |- M ≅h N]
  with ConvNeuAlg : context -> term -> term  -> term -> Type :=
    | neuVarConvAlg {Γ n decl} :
      in_ctx Γ n decl ->
      [Γ |- tRel n ~ tRel n ▹ decl.(decl_type)]
    | neuAppCongAlg {Γ m n t u na A B} :
      [ Γ |- m ~h n ▹ tProd na A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp m t ~ tApp n u ▹ B[t..] ]
  with ConvNeuRedAlg : context -> term -> term -> term -> Type :=
    | neuConvRed {Γ m n A A'} :
      [Γ |- m ~ n ▹ A] ->
      [A ⇒* A'] ->
      whnf A' ->
      [Γ |- m ~h n ▹ A']
  with ConvTermAlg : context -> term -> term -> term -> Type :=
    | termConvRed {Γ t t' u u' A A'} :
      [A ⇒* A'] ->
      [t ⇒* t'] ->
      [u ⇒* u' ] ->
      [Γ |- t' ≅h u' : A'] ->
      [Γ |- t ≅ u : A]
  with ConvTermRedAlg : context -> term -> term -> term -> Type :=
    | termPiCongAlg {Γ na na' A B A' B'} :
      [ Γ |- A ≅ A' : U] ->
      [ Γ ,, vass na A |- B ≅ B' : U] ->
      [ Γ |- tProd na A B ≅h tProd na' A' B' : U]
    | termFunConvAlg {Γ : context} {f g na A B} :
      isFun f ->
      isFun g ->
      [ Γ,, vass na A |- eta_expand f ≅ eta_expand g : B] -> 
      [ Γ |- f ≅h g : tProd na A B]
    | termNeuConvAlg {Γ m n T N} :
      [Γ |- m ~ n ▹ T] ->
      whne N ->
      [Γ |- m ≅h n : N]

  where "[ Γ |- A ≅ B ]" := (ConvTypeAlg Γ A B)
  and "[ Γ |- A ≅h B ]" := (ConvTypeRedAlg Γ A B)
  and "[ Γ |- m ~ n ▹ T ]" := (ConvNeuAlg Γ T m n)
  and "[ Γ |- m ~h n ▹ T ]" := (ConvNeuRedAlg Γ T m n)
  and "[ Γ |- t ≅ u : T ]" := (ConvTermAlg Γ T t u)
  and "[ Γ |- t ≅h u : T ]" := (ConvTermRedAlg Γ T t u)
  and "[ t ⇒ t' ]" := (OneRedAlg t t')
  and "[ t ⇒* t' ]" := (RedClosureAlg t t').

  Inductive WfTypeAlg : context -> term -> Type :=
    | wfTypeU Γ : [ Γ |- U ]
    | wfTypeProd {Γ na A B} :
      [Γ |- A ] ->
      [Γ,, vass na A |- B] ->
      [Γ |- tProd na A B]
    | wfTypeUniv {Γ A} :
      [Γ |- A : U] ->
      [Γ |- A]
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
      [ Γ |- a : A ] -> 
      [ Γ |- tApp f a ▹ B[a..] ]
  with InferRedAlg : context -> term -> term -> Type :=
    | infRed {Γ t A A'} :
      [Γ |- t ▹ A ] ->
      [ A ⇒* A'] ->
      [Γ |- t ▹h A']
  with CheckAlg : context -> term -> term -> Type :=
    | checkConv {Γ t A A'} :
      [ Γ |- t ▹ A ] -> 
      [ Γ |- A ≅ A'] -> 
      [ Γ |- t : A' ]

  where "[ Γ |- A ]" := (WfTypeAlg Γ A)
  and "[ Γ |- t ▹ T ]" := (InferAlg Γ T t)
  and "[ Γ |- t ▹h T ]" := (InferRedAlg Γ T t)
  and "[ Γ |- t : T ]" := (CheckAlg Γ T t).

  (* Inductive WfContextAlgo : context -> Type :=
  | conNilAlg : [|- ε]
  | conConsAlg {Γ na A} :
    [|- Γ] ->
    [ Γ |- A] ->
    [|- Γ,, vass na A]
  where "[ |- Γ ]" := (WfContextAlgo Γ). *)

End Definitions.

Module AlgorithmicTypingData.

  (* In algorithmic typing, we never check contexts! *)
  #[export] Instance WfContext_Algo : WfContext al := fun _ => True.
  #[export] Instance WfType_Algo : WfType al := WfTypeAlg.
  #[export] Instance Inferring_Algo : Inferring al := InferAlg.
  #[export] Instance Checking_Algo : Typing al := CheckAlg.
  #[export] Instance ConvType_Algo : ConvType al := ConvTypeAlg.
  #[export] Instance ConvTerm_Algo : ConvTerm al := ConvTermAlg.
  #[export] Instance ConvNeu_Algo : ConvNeu al := ConvNeuAlg.
  (* Reduction is untyped *)
  #[export] Instance RedType_Algo : RedType al := fun _ => RedClosureAlg.
  #[export] Instance RedTerm_Algo : RedTerm al :=
  fun _ _ => RedClosureAlg.

  Ltac fold_algo :=
    change WfTypeAlg with (wf_type (ta := al)) in *;
    change InferAlg with (inferring (ta := al)) in * ;
    change CheckAlg with (typing (ta := al)) in * ;
    change ConvTypeAlg with (conv_type (ta := al)) in * ;
    change ConvTermAlg with (conv_term (ta := al)) in * ;
    change ConvNeuAlg with (conv_neu (ta := al)) in *.

End AlgorithmicTypingData.

Notation "[ Γ |- A ≅h B ]" := (ConvTypeRedAlg Γ A B) : typing_scope.
Notation "[ Γ |- m ~h n ▹ T ]" := (ConvNeuRedAlg Γ T m n) : typing_scope.
Notation "[ Γ |- t ≅h u : T ]" := (ConvTermRedAlg Γ T t u) : typing_scope.

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

Definition AlgoConvInductionConcl
  (PTyEq PTyRedEq : context -> term -> term -> Type)
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type) :=
  (forall (Γ : context) (A B : term), [Γ |- A ≅ B] -> PTyEq Γ A B)
  × (forall (Γ : context) (A B : term), [Γ |- A ≅h B] -> PTyRedEq Γ A B)
  × (forall (Γ : context) (A m n : term), [Γ |- m ~ n ▹ A] -> PNeEq Γ A m n)
  × (forall (Γ : context) (A m n : term), [Γ |- m ~h n ▹ A] -> PNeRedEq Γ A m n)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅ u : A] -> PTmEq Γ A t u)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅h u : A] -> PTmRedEq Γ A t u).

Definition AlgoTypingInductionConcl
  (PTy : context -> term -> Type)
  (PInf PInfRed PCheck : context -> term -> term -> Type) :=
  (forall (Γ : context) (A : term), [Γ |- A] -> PTy Γ A)
  × (forall (Γ : context) (A t : term), [Γ |- t ▹ A] -> PInf Γ A t)
  × (forall (Γ : context) (A t : term), InferRedAlg Γ A t -> PInfRed Γ A t)
  × (forall (Γ : context) (A t : term), [Γ |- t : A] -> PCheck Γ A t).

Definition AlgoConvInduction :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoConvInduction);
      fold_algo ;
      let ind_ty := type of ind in
      exact (ind : ind_ty)).

Definition AlgoTypingInduction :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _AlgoTypingInduction);
      fold_algo ;
      let ind_ty := type of ind in
      exact (ind : ind_ty)).
    
(* Definition WfAlgoInductionConcl
  (PTy : context -> term -> Type)
  (PInf PInfRed PCheck PTyEq PTyRedEq : context -> term -> term -> Type)
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type) :=
  (forall (Γ : context) (A : term), [Γ |- A] -> PTy Γ A)
  × (forall (Γ : context) (A t : term), [Γ |- t ▹ A] -> PInf Γ A t)
  × (forall (Γ : context) (A t : term), InferRedAlg Γ A t -> PInfRed Γ A t)
  × (forall (Γ : context) (A t : term), [Γ |- t : A] -> PCheck Γ A t)
	× (forall (Γ : context) (A B : term), [Γ |- A ≅ B] -> PTyEq Γ A B)
  × (forall (Γ : context) (A B : term), [Γ |- A ≅h B] -> PTyRedEq Γ A B)
  × (forall (Γ : context) (A m n : term), [Γ |- m ~ n ▹ A] -> PNeEq Γ A m n)
  × (forall (Γ : context) (A m n : term), [Γ |- m ~h n ▹ A] -> PNeRedEq Γ A m n)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅ u : A] -> PTmEq Γ A t u)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅h u : A] -> PTmRedEq Γ A t u).

Definition WfAlgoInduction :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _WfAlgoInduction);
      fold_algo ;
      let ind_ty := type of ind in
      exact (ind : ind_ty)). *)

End InductionPrinciples.

Section TypingWk.
  Import AlgorithmicTypingData.
  
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PInf (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PInfRed (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    InferRedAlg Δ (A⟨ρ⟩) t⟨ρ⟩.
  Let PCheck (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
      [Δ |- A⟨ρ⟩ ≅h B⟨ρ⟩].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ~h u⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
      [Δ |- t⟨ρ⟩ ≅h u⟨ρ⟩ : A⟨ρ⟩].

  Theorem algo_conv_wk :
    AlgoConvInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    apply AlgoConvInduction.
    - intros * ? ? ? IH.
      econstructor.
      1-2: eauto using credalg_wk.
      now eapply IH.
    - intros * ? IHA ? IHB ? *.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply (IHB _ (wk_up _ _ ρ)).
      all: now econstructor.
    - econstructor.
    - intros * ? IHM.
      econstructor.
      now apply IHM.
    - intros * ? ? ? ?.
      eapply convne_meta_conv.
      1: econstructor ; eauto using in_ctx_wk.
      all: reflexivity.
    - intros * ? IHm ? IHt ? ? ?.
      cbn.
      eapply convne_meta_conv.
      1:{
        econstructor.
        2: now eapply IHt.
        red in IHm ; cbn in IHm.
        now eapply IHm.
      }
      1: asimpl.
      all: reflexivity.
    - intros * ? IHm ? ?.
      econstructor.
      + now apply IHm.
      + eauto using credalg_wk.
      + now eapply whnf_ren. 
    - intros * ? ? ? ? IHt.
      econstructor.
      1-3: eauto using credalg_wk.
      now eapply IHt.
    - intros * ? IHA ? IHB ? ? ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply (IHB _ (wk_up _ _ ρ)).
      all: now econstructor.
    - intros ? f f' * ? ? ? IH ? ? ?.
      cbn.
      econstructor.
      1-2: asimpl ; gen_typing.
      specialize (IH _ (wk_up _ _ ρ)).
      red in IH.
      cbn in *.
      asimpl.
      repeat (erewrite compRenRen_term in IH ; [..|reflexivity]).
      apply IH.
      now econstructor.
    - intros * ? IH ?.
      econstructor.
      2: cbn ; asimpl ; now gen_typing.
      now eapply IH.
  Qed.

  Theorem algo_typing_wk :
    AlgoTypingInductionConcl PTy PInf PInfRed PCheck.
  Proof.
    apply AlgoTypingInduction.
    - constructor.
    - intros Γ na A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply (IHB _ (wk_up _ _ ρ)).
      all: now constructor.
    - intros * _ IHA.
      econstructor.
      now apply IHA.
    - intros * ? Δ ? * ?.
      eapply typing_meta_conv.
      1: now econstructor ; eapply in_ctx_wk.
      reflexivity.
    - intros Γ na A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply (IHB _ (wk_up _ _ ρ)).
      all: now constructor.
    - intros * HA IHA Ht IHt Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply (IHt _ (wk_up _ _ ρ)).
      all: now constructor.
    - intros * Hf IHf Ha IHa Δ ρ HΔ.
      cbn.
      eapply typing_meta_conv.
      red in IHf. cbn in IHf.
      1: cbn ; econstructor.
      1: now eapply IHf.
      1: now eapply IHa.
      now asimpl.
    - intros * ? IHt ?.
      econstructor.
      + now eapply IHt.
      + eauto using credalg_wk.
    - intros * ? IHt.
      econstructor.
      + now eapply IHt.
      + now eapply algo_conv_wk.
  Qed.

End TypingWk.