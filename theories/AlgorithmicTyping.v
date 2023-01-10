From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping.
Set Primitive Projections.

Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition here before declaring the right
  instance *)
  Close Scope typing_scope.

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
      [Γ |- A ⇒* A'] ->
      [Γ |- t ▹h A']
  with CheckAlg : context -> term -> term -> Type :=
    | checkConv {Γ t A A'} :
      [ Γ |- t ▹ A ] -> 
      [ Γ |- A ≅ A'] -> 
      [ Γ |- t : A' ]
  with ConvTypeAlg : context -> term -> term  -> Type :=
    | typeConvRed {Γ A A' B B'} :
      [Γ |- A ⇒* A'] ->
      [Γ |- B ⇒* B'] ->
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
      [Γ |- A ⇒* A'] ->
      [Γ |- m ~h n ▹ A']
  with ConvTermAlg : context -> term -> term -> term -> Type :=
    | termConvRed {Γ t t' u u' A A'} :
      [Γ |- A ⇒* A'] ->
      [Γ |- t ⇒* t'] ->
      [Γ |- u ⇒* u' ] ->
      [Γ |- t' ≅h u' : A'] ->
      [Γ |- t ≅ u : A]
  with ConvTermRedAlg : context -> term -> term -> term -> Type :=
    | termPiCongAlg {Γ na na' A B A' B'} :
      [ Γ |- A ≅ A' : U] ->
      [ Γ ,, vass na A |- B ≅ B' : U] ->
      [ Γ |- tProd na A B ≅h tProd na' A' B' : U]
    | termFunConvAlg {Γ f g na A B} :
      [ Γ,, vass na A |- eta_expand f ≅ eta_expand g : B] -> 
      [ Γ |- f ≅h g : tProd na A B]
    | termNeuConvAlg {Γ m n T N} :
      [Γ |- m ~ n ▹ T] ->
      [Γ |- m ≅h n : N]
  with OneRedAlg : context -> term -> term -> Type :=
    | termBetaAlg {Γ na A t u} :
      [ Γ |- tApp (tLambda na A t) u ⇒ t[u..] ]
    | termRedAppAlg {Γ t t' u} :
      [ Γ |- t ⇒ t' ] ->
      [ Γ |- tApp t u ⇒ tApp t' u ]

  with RedClosureAlg : context -> term -> term -> Type :=
  | redIdAlg {Γ t} :
    [ Γ |- t ⇒* t ]
  | redSuccAlg {Γ t t' u} :
    [ Γ |- t ⇒ t'] ->
    [ Γ |- t' ⇒* u ] ->
    [ Γ |- t ⇒* u ]

  where "[ Γ |- A ]" := (WfTypeAlg Γ A)
  and   "[ Γ |- t ▹ T ]" := (InferAlg Γ T t)
  and   "[ Γ |- t ▹h T ]" := (InferRedAlg Γ T t)
  and   "[ Γ |- t : T ]" := (CheckAlg Γ T t)
  and   "[ Γ |- A ≅ B ]" := (ConvTypeAlg Γ A B)
  and   "[ Γ |- A ≅h B ]" := (ConvTypeRedAlg Γ A B)
  and   "[ Γ |- m ~ n ▹ T ]" := (ConvNeuAlg Γ T m n)
  and   "[ Γ |- m ~h n ▹ T ]" := (ConvNeuRedAlg Γ T m n)
  and   "[ Γ |- t ≅ u : T ]" := (ConvTermAlg Γ T t u)
  and   "[ Γ |- t ≅h u : T ]" := (ConvTermRedAlg Γ T t u)
  and   "[ Γ |- t ⇒ t' ]" := (OneRedAlg Γ t t')
  and   "[ Γ |- t ⇒* t' ]" := (RedClosureAlg Γ t t').

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
  #[export] Instance OneRedType_Algo : OneRedType al := OneRedAlg.
  #[export] Instance OneRedTerm_Algo : OneRedTerm al :=
  fun Γ _ t u => OneRedAlg Γ t u.

  Ltac fold_algo :=
    change WfTypeAlg with wf_type in *;
    change InferAlg with inferring in * ;
    change CheckAlg with typing in * ;
    change ConvTypeAlg with conv_type in * ;
    change ConvTermAlg with conv_term in * ;
    change ConvNeuAlg with conv_neu in *.

End AlgorithmicTypingData.

Notation "[ Γ |- t ▹h T ]" := (InferRedAlg Γ T t) : typing_scope.
Notation "[ Γ |- A ≅h B ]" := (ConvTypeRedAlg Γ A B) : typing_scope.
Notation "[ Γ |- m ~h n ▹ T ]" := (ConvNeuRedAlg Γ m n T) : typing_scope.
Notation "[ Γ |- t ≅h u : T ]" := (ConvTermRedAlg Γ t u T) : typing_scope.
Notation "[ Γ |- t ⇒ t' ]" := (OneRedAlg Γ t t') : typing_scope.
Notation "[ Γ |- t ⇒* t' ]" := (RedClosureAlg Γ t t') : typing_scope.

Section InductionPrinciples.
  Import AlgorithmicTypingData.

Scheme 
    Minimality for WfTypeAlg Sort Type with
    Minimality for InferAlg Sort Type with
    Minimality for InferRedAlg Sort Type with
    Minimality for CheckAlg Sort Type with
    Minimality for ConvTypeAlg Sort Type with
    Minimality for ConvTypeRedAlg Sort Type with
    Minimality for ConvNeuAlg Sort Type with
    Minimality for ConvNeuRedAlg Sort Type with
    Minimality for ConvTermAlg Sort Type with
    Minimality for ConvTermRedAlg Sort Type with
    Minimality for OneRedAlg Sort Type with
    Minimality for RedClosureAlg Sort Type.

Combined Scheme _WfAlgoInduction from
    WfTypeAlg_rect_nodep,
    InferAlg_rect_nodep,
    InferRedAlg_rect_nodep,
    CheckAlg_rect_nodep,
    ConvTypeAlg_rect_nodep,
    ConvTypeRedAlg_rect_nodep,
    ConvNeuAlg_rect_nodep,
    ConvNeuRedAlg_rect_nodep,
    ConvTermAlg_rect_nodep,
    ConvTermRedAlg_rect_nodep,
    OneRedAlg_rect_nodep,
    RedClosureAlg_rect_nodep.
    
Definition WfAlgoInductionConcl
  (PTy : context -> term -> Type)
  (PInf PInfRed PCheck PTyEq PTyRedEq : context -> term -> term -> Type)
  (PNeEq PNeRedEq PTmEq PTmRedEq : context -> term -> term -> term -> Type)
  (PORed PCRed : context -> term -> term -> Type) :=
  (forall (Γ : context) (A : term), [Γ |- A] -> PTy Γ A)
  × (forall (Γ : context) (A t : term), [Γ |- t ▹ A] -> PInf Γ A t)
  × (forall (Γ : context) (A t : term), [Γ |- t ▹h  A] -> PInfRed Γ A t)
  × (forall (Γ : context) (A t : term), [Γ |- t : A] -> PCheck Γ A t)
	× (forall (Γ : context) (A B : term), [Γ |- A ≅ B] -> PTyEq Γ A B)
  × (forall (Γ : context) (A B : term), [Γ |- A ≅h B] -> PTyRedEq Γ A B)
  × (forall (Γ : context) (A m n : term), [Γ |- m ~ n ▹ A] -> PNeEq Γ A m n)
  × (forall (Γ : context) (A m n : term), [Γ |- m ~h n ▹ A] -> PNeRedEq Γ A m n)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅ u : A] -> PTmEq Γ A t u)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅h u : A] -> PTmRedEq Γ A t u)
  × (forall (Γ : context) (t u : term), [Γ |- t ⇒ u] -> PORed Γ t u)
  × (forall (Γ : context) (t u : term), [Γ |- t ⇒* u] -> PCRed Γ t u).

Definition WfAlgoInduction :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _WfAlgoInduction);
      fold_algo ;
      let ind_ty := type of ind in
      exact (ind : ind_ty)).

End InductionPrinciples.