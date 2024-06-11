(** * LogRel.ParallelRed: definition of parallel reduction. *)
From Coq Require Import ssreflect CRelationClasses.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening.
From LogRel Require Import GenericTyping.

Set Primitive Projections.

Class EqType (ta : tag) := eq_type : context -> term -> term -> Set.
Class EqTerm (ta : tag) := eq_term : context -> term -> term -> term -> Set.

Notation "[ Γ |- A = B ]" := (eq_type Γ A B)
  (at level 0, Γ, A, B at level 50, only parsing) : typing_scope.
  Notation "[ Γ |-[ ta  ] A = B ]" := (eq_type (ta := ta) Γ A B)
    (at level 0, Γ, A, B at level 50) : typing_scope.
Notation "[ Γ |- t = u : A ]" := (eq_term Γ A t u)
  (at level 0, Γ, A, t, u at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t = u : A ]" := (eq_term (ta := ta) Γ A t u)
  (at level 0, Γ, A, t, u at level 50) : typing_scope.


Reserved Notation "[ Γ '|-s' σ = τ : Δ ]" (at level 0, Γ, σ, τ, Δ at level 50).
Reserved Notation "[ Γ |-[ ta  ']s' σ = τ : Δ ]" (at level 0, ta, Γ, σ, τ, Δ at level 50).
  

Section SubstDefs.

Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta} `{!OneStepRedType ta}
  `{!OneStepRedTerm ta} `{!EqType ta} `{!EqTerm ta}.


  Inductive ParSubst (Γ : context) : context -> (nat -> term) -> (nat -> term) -> Type :=
  | par_sempty (σ τ : nat -> term) : [Γ |-s σ ⤳ τ : ε ]
  | par_scons (σ τ : nat -> term) (Δ : context) A :
    [Γ |-s ↑ >> σ ⤳ ↑ >> τ : Δ] -> [Γ |- σ var_zero ⤳ τ var_zero: A[↑ >> σ]] ->
    [Γ |-s σ ⤳ τ : Δ,, A]
  where "[ Γ '|-s' σ ⤳ τ : Δ ]" := (ParSubst Γ Δ σ τ).

  Inductive EqSubst (Γ : context) : context -> (nat -> term) -> (nat -> term) -> Type :=
  | eq_sempty (σ τ : nat -> term) : [Γ |-s σ = τ : ε ]
  | eq_scons (σ τ : nat -> term) (Δ : context) A :
    [Γ |-s ↑ >> σ = ↑ >> τ : Δ] -> [Γ |- σ var_zero = τ var_zero: A[↑ >> σ]] ->
    [Γ |-s σ = τ : Δ,, A]
  where "[ Γ '|-s' σ = τ : Δ ]" := (EqSubst Γ Δ σ τ).


  Lemma oredtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ⤳ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ⤳ u' : A'].
  Proof.
  now intros ? -> ->.
  Qed.


  Lemma eqtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t = u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t = u' : A'].
  Proof.
  now intros ? -> ->.
  Qed.

End SubstDefs.

Notation "[ Γ '|-s' σ ⤳ τ : A ]" := (ParSubst Γ A σ τ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ ⤳ τ : A ]" := (ParSubst (ta := ta) Γ A σ τ) : typing_scope.

Notation "[ Γ '|-s' σ = τ : A ]" := (EqSubst Γ A σ τ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ = τ : A ]" := (EqSubst (ta := ta) Γ A σ τ) : typing_scope.

(** ** Definitions *)
Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition
  here before declaring the instance to which abstract notations are bound. *)
  Close Scope typing_scope.


  (** Reduction and conversion are mutually defined inductive relations. Typing is just a
    shortcut for a type reduction to itself. *)

  (** **** Context well-formation *)
  Inductive WfContextPar : context -> Type :=
      | ConParNil : [ |- ε ]
      | ConParCons {Γ A} : 
          [ |- Γ ] -> 
          [ Γ |- A ] -> 
          [ |-  Γ ,, A]
  (** **** Type  *)
  with TypePar  : context -> term -> term -> Type :=
      | TypeParU {Γ} : 
          [ |- Γ ] ->
          [ Γ |- U ⤳ U] 
      | TypeParProd {Γ} {A A' B B'} :
          [ Γ |- A ⤳ A'] -> 
          [Γ ,, A |- B ⤳ B'] -> 
          [ Γ |- tProd A B ⤳ tProd A' B']
      | TypeParUniv {Γ} {A A'} :
          [ Γ |- A ⤳ A' : U ] -> 
          [ Γ |- A ⤳ A']
  (** **** Typing *)
  with TermPar : context -> term -> term -> term -> Type :=
      | TermParVar {Γ} {n decl} :
          [   |- Γ ] ->
          in_ctx Γ n decl ->
          [ Γ |- tRel n ⤳ tRel n : decl ]
      | TermParProd {Γ} {A A' B B'} :
          [ Γ |- A ⤳ A' : U] -> 
          [Γ ,, A |- B ⤳ B' : U] -> 
          [ Γ |- tProd A B ⤳ tProd A' B' : U]
      | TermParLam {Γ} {A A' A'' B t t'} :
          [Γ |- A ≅ A''] ->
          [ Γ |- A ⤳ A' ] ->
          [ Γ ,, A |- t ⤳ t' : B ] -> 
          [ Γ |- tLambda A t ⤳ tLambda A' t' : tProd A'' B]
      | TermParBeta {Γ} {A A' B a a' t t'} :
          [Γ |- A] ->
          [Γ |- A'] ->
          [ Γ |- A' ≅ A] ->
          [Γ ,, A |- B] ->
          [ Γ ,, A' |- t ⤳ t' : B ] ->
          [ Γ |- a ⤳ a' : A ] ->
          [ Γ |- tApp A B (tLambda A' t) a ⤳ t'[a'..] : B[a..] ]
      | TermParApp {Γ} {f f' a a' A A' B B'} :
          [Γ |- A] ->
          [Γ |- A ≅ A' ] ->
          [Γ,, A |- B] ->
          [Γ,, A |- B ≅ B'] ->
          [ Γ |- f ⤳ f' : tProd A B ] -> 
          [ Γ |- a ⤳ a' : A ] -> 
          [ Γ |- tApp A B f a ⤳ tApp A' B' f' a' : B[a..] ]
      | TermParConv {Γ} {A B t t'} :
          [ Γ |- t ⤳ t' : A ] -> 
          [ Γ |- A ≅ B ] -> 
          [ Γ |- t ⤳ t' : B ]

  (** **** Structural equality of types *)
  with TypeEqPar : context -> term -> term  -> Type :=
    | TypeEqParU {Γ} :
        [ |- Γ ] ->
        [ Γ |- U = U]
      | TypeEqParProd {Γ} {A B C D} :
          [Γ |- A] ->
          [ Γ |- A = B] ->
          [ Γ ,, A |- C = D] ->
          [ Γ |- tProd A C = tProd B D]
      | TypeEqParUniv {Γ} {A B} :
        [ Γ |- A = B : U ] -> 
        [ Γ |- A = B ]

  (** **** Structural equality of terms *)
  with TermEqPar : context -> term -> term -> term -> Type :=
      | TermEqParVar {Γ} {n decl} :
        [   |- Γ ] ->
        in_ctx Γ n decl ->
        [ Γ |- tRel n = tRel n : decl ]
      | TermEqParProd {Γ} {A A' B B'} :
        [Γ |- A] ->
        [ Γ |- A = A' : U] -> 
        [Γ ,, A |- B = B' : U] -> 
        [ Γ |- tProd A B = tProd A' B' : U]
      | TermEqParLam {Γ} {A A' A'' B t t'} :
        [Γ |- A] ->
        [ Γ |- A ≅ A' ] ->
        [Γ |- A ≅ A'' ] ->
        [ Γ ,, A |- t = t' : B ] -> 
        [ Γ |- tLambda A t = tLambda A' t' : tProd A'' B]
      | TermEqParApp {Γ} {f f' a a' A A' B B'} :
        [Γ |- A] ->
        [Γ |- A ≅ A' ] ->
        [Γ,, A |- B] ->
        [Γ,, A |- B ≅ B'] ->
        [ Γ |- f = f' : tProd A B ] -> 
        [ Γ |- a = a' : A ] -> 
        [ Γ |- tApp A B f a = tApp A' B' f' a' : B[a..] ]
      | TermEqParConv {Γ} {A B t t'} :
        [ Γ |- t = t' : A ] -> 
        [ Γ |- A ≅ B ] -> 
        [ Γ |- t = t' : B ]

  with TypeConv : context -> term -> term  -> Type :=
      | TypeConvParEq {Γ A B} :
          [ Γ |- A = B] ->
          [ Γ |- A ≅ B]
      | TypeConvParL {Γ} {A A' B} :
          [ Γ |- A ⤳ A' ] ->
          [Γ |- A' ≅ B] ->
          [ Γ |- A ≅ B ]
      (* | TypeConvParR {Γ} {A B B'} :
          [ Γ |- B ⤳ B' ] ->
          [Γ |- A ≅ B'] ->
          [ Γ |- A ≅ B ] *)
      | TypeConvSym {Γ} {A B} :
          [Γ |- A ≅ B] ->
          [Γ |- B ≅ A]
      | TypeConvTrans {Γ} {A B C} :
          [ Γ |- A ≅ B] ->
          [ Γ |- B ≅ C] ->
          [ Γ |- A ≅ C]
      
  where "[   |- Γ ]" := (WfContextPar Γ)
  and   "[ Γ |- A ⤳ A' ]" := (TypePar Γ A A')
  and   "[ Γ |- A ]" := (TypePar Γ A A)
  and   "[ Γ |- t ⤳ t' : A ]" := (TermPar Γ A t t')
  and   "[ Γ |- t : T ]" := (TermPar Γ T t t)
  and   "[ Γ |- A = B ]" := (TypeEqPar Γ A B)
  and   "[ Γ |- t = t' : T ]" := (TermEqPar Γ T t t')
  and   "[ Γ |- A ≅ B ]" := (TypeConv Γ A B).

  Inductive TermParClos (Γ : context) (A : term) : term -> term -> Type :=
    | TermParRedRefl t : [Γ |- t : A] -> [Γ |- t ⤳* t : A]
    | TermParRedTrans t t' t'' : [Γ |- t ⤳ t' : A] -> [Γ |- t' ⤳* t'' : A] -> [Γ |- t ⤳* t'' : A]
  where "[ Γ |- t ⤳* t' : A ]" := (TermParClos Γ A t t').

  Inductive TypeParClos (Γ : context) : term -> term -> Type :=
    | TypeParRedRefl A : [Γ |- A ] -> [Γ |- A ⤳* A]
    | TypeParRedTrans A A' A'' : [Γ |- A ⤳ A'] -> [Γ |- A' ⤳* A''] -> [Γ |- A ⤳* A'']
  where "[ Γ |- A ⤳* A' ]" := (TypeParClos Γ A A').

End Definitions.


(** ** Instances *)
(** Used for printing (see Notations) and as a support for the generic typing
properties used for the logical relation (see GenericTyping). *)
Module ParallelTypingData.

  Definition pa : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Par : WfContext pa := WfContextPar.
  #[export] Instance WfType_Par : WfType pa := fun Γ A => TypePar Γ A A.
  #[export] Instance Typing_Par : Typing pa := fun Γ A t => TermPar Γ A t t.
  #[export] Instance ConvType_Par : ConvType pa := TypeConv.
  (* #[export] Instance ConvTerm_Par : ConvTerm pa := TermConvPar. *)
  #[export] Instance EqType_Par : EqType pa := TypeEqPar.
  #[export] Instance EqTerm_Par : EqTerm pa := TermEqPar.
  #[export] Instance RedType_Par : RedType pa := TypeParClos.
  #[export] Instance RedTerm_Par : RedTerm pa := TermParClos.
  #[export] Instance OSRedType_Par : OneStepRedType pa := TypePar.
  #[export] Instance OSRedTerm_Par : OneStepRedTerm pa := TermPar.

  Ltac fold_pa :=
    change WfContextPar with (wf_context (ta := pa)) in * ;
    change (TypePar ?Γ ?A ?A) with (wf_type (ta := pa) Γ A) in * ;
    change (TermPar ?Γ ?A ?t ?t) with (typing (ta := pa) Γ A t) in * ;
    change TypeEqPar with (eq_type (ta := pa)) in * ;
    change TermEqPar with (eq_term (ta := pa)) in * ;
    change TypeConv with (conv_type (ta := pa)) in * ;
    (* change TermConvPar with (conv_term (ta := pa)) in * ; *)
    change TypeParClos with (red_ty (ta := pa)) in *;
    change TermParClos with (red_tm (ta := pa)) in *;
    change TypePar with (osred_ty (ta := pa)) in *;
    change TermPar with (osred_tm (ta := pa)) in *.

  Smpl Add fold_pa : refold.

  (* #[export] Instance ConvTyTrans Γ : Transitive (conv_type Γ).
  Proof.
    intros ? **.
    now econstructor.
  Qed. *)

End ParallelTypingData.

(** ** Induction principles *)

(** We use Scheme to generate mutual induction principle. Sadly, Scheme uses
the product of the standard library, which is not universe polymorphic, which
causes universe issues, typically in the fundamental lemma. So
we use some Ltac code to generate properly polymorphic versions of the inductive
principle. We also use Ltac to generate the conclusion of the mutual induction
proof, to alleviate the user from the need to write it down every time: they
only need write the predicates to be proven. *)
Section InductionPrinciples.
  Import ParallelTypingData.

Scheme 
    Minimality for WfContextPar Sort Type with
    Minimality for TypePar      Sort Type with
    Minimality for TermPar      Sort Type with
    Minimality for TypeEqPar    Sort Type with
    Minimality for TermEqPar    Sort Type with
    Minimality for TypeConv     Sort Type.

Combined Scheme _ParInduction from
    WfContextPar_rect_nodep,
    TypePar_rect_nodep,
    TermPar_rect_nodep,
    TypeEqPar_rect_nodep,
    TermEqPar_rect_nodep,
    TypeConv_rect_nodep.

Let _ParInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _ParInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let ParInductionType :=
  ltac: (let ind := eval cbv delta [_ParInductionType] zeta
    in _ParInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma ParInduction : ParInductionType.
Proof.
  intros PCon PTy PTm PTyEq PTmEq PTyConv **.
  pose proof (_ParInduction PCon PTy PTm PTyEq PTmEq PTyConv) as H.
  destruct H as (?&?&?&?&?&?).
  all: try (assumption ; fail).
  repeat (split;[assumption|]); assumption.
Qed.

Definition ParInductionConcl :=
  ltac:(
    let t := eval cbv delta [ParInductionType] beta in ParInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv : rename.

Import ParallelTypingData.

Section CtxTypable.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := [|- Γ].
  Let PTm (Γ : context) (A t t' : term) := [|- Γ].
  Let PTyEq (Γ : context) (A B : term) := [|- Γ].
  Let PTmEq (Γ : context) (A t t' : term) := [|- Γ].
  Let PTyConv (Γ : context) (A B : term) := [|- Γ].

  Theorem par_ctx_ty : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: trivial.
  Qed.

End CtxTypable.

Section ConvRefl.

  Let PCon (Γ : context) := [|- Γ ≅ Γ].
  Let PTy (Γ : context) (A A' : term) := [Γ |- A] × [Γ |- A = A].
  Let PTm (Γ : context) (A t t' : term) := [Γ |- t : A] × [Γ |- t = t : A].
  Let PTyEq (Γ : context) (A B : term) := [Γ |- A] × [Γ |- A = A].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- t : A] × [Γ |- t = t : A].
  Let PTyConv (Γ : context) (A B : term) := True.

  Lemma conv_refl : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: try solve
      [ trivial
      | now econstructor
      | split ; now econstructor
      | constructor ; tea ; now constructor
      ].
    
    3: shelve.
    all: solve [intros ; prod_hyp_splitter ; split ; econstructor ; tea ; now econstructor].
    
    Unshelve.
    intros ; prod_hyp_splitter.
    split ; econstructor ; tea.
    1-5: now econstructor.
    econstructor ; tea.
    now econstructor.
  Qed.

End ConvRefl.

Section LeftTypable.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := [Γ |- A].
  Let PTm (Γ : context) (A t t' : term) := [Γ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := [Γ |- A].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- t : A].
  Let PTyConv (Γ : context) (A B : term) := True.

  Theorem par_lty : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    repeat split.
    all: now apply conv_refl.
  Qed.

  Corollary par_clos_lty :
    (forall Γ A A', [Γ |- A ⤳* A'] -> [Γ |- A]) × (forall Γ A t t', [Γ |- t ⤳* t' : A] -> [Γ |- t : A]).
  Proof.
    split.
    - intros * [| ??? ?%par_lty] ; refold.
      all: eassumption.
    - intros * [| ??? ?%par_lty] ; refold.
      all: eassumption.
  Qed.
    
End LeftTypable.

Section TypingWk.
  
  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩ ⤳ A'⟨ρ⟩].
  Let PTm (Γ : context) (A t t' : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ⤳ t'⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ = B⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ = u⟨ρ⟩ : A⟨ρ⟩].
  Let PTyConv (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].

  Theorem par_wk : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: try solve [now econstructor].
    - intros * ? IHA ? IHB * ? ; cbn.
      unshelve epose proof (IHA _ _ _) as IHA' ; tea.
      econstructor ; eauto.
      eapply IHB with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply par_lty in IHA'.
    - intros ; cbn.
      econstructor ; tea.
      now eapply in_ctx_wk.
    - intros * ? IHA ? IHB * ? ; cbn.
      unshelve epose proof (IHA _ _ _) as IHA' ; tea.
      econstructor ; eauto.
      eapply IHB with (ρ := wk_up _ _).
      econstructor ; tea.
      econstructor.
      now eapply par_lty in IHA'.
    - intros * ? IHAconv ? IHAred ? IHt **.
      unshelve epose proof (IHAred _ _ _) as IHA' ; tea.
      cbn ; econstructor.
      1-2: eauto.
      eapply IHt with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply par_lty in IHA'.
    - intros * ? IHAred ? IHA'red ? IHAconv ? IHB ? IHt ? IHa **.
      assert [Δ |- A⟨ρ⟩] by now eapply IHAred.
      assert [Δ |- A'⟨ρ⟩] by now eapply IHA'red.
      cbn.
      evar (B' : term) ; replace (B[_]⟨ρ⟩) with B' ; subst B'.
      evar (t'' : term) ; replace (t'[_]⟨ρ⟩) with t'' ; subst t''.
      1: econstructor ; eauto.
      + now eapply IHB with (ρ := wk_up _ _) ; econstructor.
      + now eapply IHt with (ρ := wk_up _ _) ; econstructor.
      + now bsimpl.
      + now bsimpl.
    - intros * ? IHA ? IHA' ? IHB ? IHB' ? IHf ? IHa **.
      assert [Δ |- A⟨ρ⟩] by now eapply IHA.
      cbn.
      evar (B'' : term) ; replace (B[_]⟨ρ⟩) with B'' ; subst B''.
      1: econstructor ; eauto. 
      + now eapply IHB with (ρ := wk_up _ _) ; econstructor.
      + now eapply IHB' with (ρ := wk_up _ _) ; econstructor.
      + now bsimpl.
    - intros * ? IHA ? IHA' ? IHB **.
      cbn.
      econstructor ; eauto.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply IHA.
    - intros **.
      econstructor ; tea.
      now eapply in_ctx_wk.
    - intros * ? IHA ? IHA' ? IHB **.
      cbn.
      econstructor ; eauto.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply IHA.
    - intros * ? IHA ? IHA'' ?? ? IHt **.
      cbn.
      econstructor ; eauto.
      1: now eapply IHA.
      eapply IHt with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply IHA.
    - intros * ? IHA ? IHA' ? IHB ? IHB' ? IHf ? IHa **.
      cbn.
      evar (B'' : term) ; replace (B[_]⟨ρ⟩) with B'' ; subst B''.
      1: econstructor ; eauto.
      + now eapply IHA. 
      + eapply IHB with (ρ := wk_up _ _) ; econstructor ; tea.
        now eapply par_lty in IHA.
      + eapply IHB' with (ρ := wk_up _ _) ; econstructor ; tea.
        now eapply par_lty in IHA.
      + now bsimpl.
  Qed.

  Let PCon' (Γ : context) := True.
  Let PTy' (Γ : context) (A A' : term) := forall T, [Γ |- T ] -> [Γ,,T |- A⟨↑⟩ ⤳ A'⟨↑⟩].
  Let PTm' (Γ : context) (A t t' : term) := forall T, [Γ |- T ] ->
    [Γ,,T |- t⟨↑⟩ ⤳ t'⟨↑⟩ : A⟨↑⟩].
  Let PTyEq' (Γ : context) (A B : term) := forall T, [Γ |- T ] ->
    [Γ,,T |- A⟨↑⟩ = B⟨↑⟩].
  Let PTmEq' (Γ : context) (A t u : term) := forall T, [Γ |- T ] ->
    [Γ,,T |- t⟨↑⟩ = u⟨↑⟩ : A⟨↑⟩].
  Let PTyConv' (Γ : context) (A B : term) := forall T, [Γ |- T ] ->
    [Γ,,T |- A⟨↑⟩ ≅ B⟨↑⟩].

  Corollary par_wk1 : ParInductionConcl PCon' PTy' PTm' PTyEq' PTmEq' PTyConv'.
  Proof.
    subst PCon' PTy' PTm' PTyEq' PTmEq' PTyConv'.
    repeat split.
    all: intros.
    all: repeat erewrite <- wk1_ren_on.
    all: eapply par_wk ; tea.
    all: solve [econstructor ; tea ; now eapply par_ctx_ty in H].
  Qed.

End TypingWk.

Section CtxConv.

  Lemma ctx_conv_ext Δ Γ A: [|- Δ ≅ Γ] -> [Δ |- A] -> [|- Δ,, A ≅ Γ,,A].
  Proof.
    intros ? HA.
    econstructor ; tea.
    constructor.
    now eapply conv_refl in HA.
  Qed.


  Lemma ctx_conv_tip Γ A A' : [Γ |- A ≅ A'] -> [|- Γ,, A ≅ Γ,,A'].
  Proof.
    intros HA.
    econstructor ; tea.
    eapply conv_refl.
    now eapply par_ctx_ty in HA.
  Qed.

  Let PCon (Γ : context) := forall Δ, [|- Δ ≅ Γ] -> [|- Δ] ->
    forall decl n, in_ctx Γ n decl -> ∑ decl', in_ctx Δ n decl' × [Δ |- decl' ≅ decl].
  Let PTy (Γ : context) (A A' : term) := forall Δ, [|- Δ ≅ Γ] -> [|- Δ] -> [Δ |- A ⤳ A'].
  Let PTm (Γ : context) (A t t' : term) := forall Δ, [|- Δ ≅ Γ] -> [|- Δ] ->
    [Δ |- t ⤳ t' : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ, [|- Δ ≅ Γ] -> [|- Δ] ->
    [Δ |- A = B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ, [|- Δ ≅ Γ] -> [|- Δ] ->
    [Δ |- t = u : A].
  Let PTyConv (Γ : context) (A B : term) := forall Δ, [|- Δ ≅ Γ] -> [|- Δ] ->
    [Δ |- A ≅ B].


  Theorem par_ctx_conv : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: try solve [now econstructor].
    - intros ? Hctx ? * Hin.
      inversion Hctx ; subst.
      inversion Hin.
    - intros * ? IHΓ ? IHA ? Hconv HΔ * Hin.
      inversion Hconv ; subst.
      inversion Hin ; subst.
      + eexists ; split.
        1: now constructor.
        eapply par_wk1 ; tea.
        now inversion HΔ.
      + refold.
        edestruct IHΓ as [? []] ; tea.
        1: now inversion HΔ.
        eexists ; split.
        1: now constructor.
        refold.
        eapply par_wk1 ; tea.
        now inversion HΔ.
    - intros * ? IHA ? IHB **.
      econstructor ; eauto.
      eapply IHB.
      + eapply ctx_conv_ext ; tea.
        now eapply par_lty in IHA.
      + constructor ; tea.
        now eapply par_lty in IHA.
    - intros * ? IHΓ Hin ???.
      edestruct IHΓ as [? []] ; tea.
      eapply TermParConv ; refold ; tea.
      now econstructor.
    - intros * HA IHA ? IHB ??.
      econstructor.
      1: eauto.
      eapply IHB.
      1: eapply ctx_conv_ext ; tea.
      2: econstructor ; tea.
      all: econstructor ; now eapply par_lty in IHA.
    - intros * HA'' IHA'' HA IHA Ht IHt ??.
      econstructor.
      1-2: eauto.
      eapply IHt.
      1: eapply ctx_conv_ext ; tea.
      2: econstructor ; tea.
      all: now eapply par_lty in IHA.
    - intros * HA IHA HA' IHA' ? IHA'' ? IHB ? IHt ? IHa ??.
      econstructor.
      + now eapply IHA.
      + now eapply IHA'.
      + eauto. 
      + eapply IHB.
        1: eapply ctx_conv_ext ; tea.
        2: econstructor ; tea.
        all: now eapply par_lty in IHA.
      + eapply IHt.
        1: eapply ctx_conv_ext ; tea.
        2: econstructor ; tea.
        all: now eapply par_lty in IHA'.
      + eauto.
    - intros * ? IHA ? IHA' ? IHB ? IHB' ? IHf ? IHa ???.
      assert [|- Δ,, A] by (econstructor ; tea ; now eapply IHA).
      assert [|- Δ,,A ≅ Γ,,A] by (eapply ctx_conv_ext ; tea ; now eapply IHA).
      econstructor ; eauto.
      2: eapply IHB.
      2: eapply ctx_conv_ext ; tea.
      3: econstructor ; tea.
      all: now eapply IHA.
    - intros * ? IHA ? IHA' ? IHB ??.
      econstructor ; eauto.
      1: now eapply IHA.
      eapply IHB.
      2: econstructor ; tea.
      1: eapply ctx_conv_ext ; tea.
      all: now eapply IHA.
    - intros * ? IHΓ ? ???.
      edestruct IHΓ as [? []]; tea.
      eapply TermEqParConv ; refold ; tea.
      now econstructor.
    - intros * ? IHA ? IHA' ? IHB **.
      econstructor ; eauto.
      1: now eapply IHA.
      eapply IHB.
      2: econstructor ; tea.
      1: eapply ctx_conv_ext ; tea.
      all: now eapply IHA.
    - intros * HA IHA HA'' IHA'' HA' IHA' Ht IHt ???.
      econstructor.
      1: now eapply IHA.
      1-2: now eauto.
      eapply IHt.
      2: econstructor ; tea.
      1: eapply ctx_conv_ext ; tea.
      all: now eapply IHA.
    - intros * HA IHA HA' IHA' ? IHB ? IHB' ? IHt ? IHa ??.
      econstructor ; eauto.
      + now eapply IHA.
      + eapply IHB.
        2: econstructor ; tea.
        1: eapply ctx_conv_ext ; tea.
        all: now eapply IHA.
      + eapply IHB'.
        2: econstructor ; tea.
        1: eapply ctx_conv_ext ; tea.
        all: now eapply IHA.
  Qed.

  Corollary par_clos_ctx_conv :
    (forall Γ Δ A A', [|- Δ ≅ Γ] -> [|- Δ] -> [Γ |- A ⤳* A'] -> [Δ |- A ⤳* A']) ×
    (forall Γ Δ A t t', [|- Δ ≅ Γ] -> [|- Δ] -> [Γ |- t ⤳* t' : A] -> [Δ |- t ⤳* t' : A]).
  Proof.
    split.
    - intros * ?? HA.
      induction HA ; refold.
      all: now econstructor ; try eapply par_ctx_conv.
    - intros * ?? Ht.
      induction Ht ; refold.
      all: now econstructor ; try eapply par_ctx_conv.
  Qed.
    
End CtxConv.

Section Subst.

  Lemma par_subst_ext Γ Δ (σ σ' τ τ' : nat -> term) :
      σ =1 σ' ->
      τ =1 τ' ->
      [Γ |-s σ ⤳ τ : Δ] ->
      [Γ |-s σ' ⤳ τ' : Δ].
    Proof.
      intros Heq Heq'.
      induction 1 in σ', τ', Heq, Heq' |- *.
      all: constructor.
      - eapply IHParSubst.
        all: now rewrite ?Heq ?Heq'.
      - rewrite <- Heq, <- Heq'.
        now replace A[↑ >> σ'] with A[↑ >> σ]
          by (now rewrite Heq).
    Qed.

  Lemma eq_subst_ext Γ Δ (σ σ' τ τ' : nat -> term) :
  σ =1 σ' ->
  τ =1 τ' ->
  [Γ |-s σ = τ : Δ] ->
  [Γ |-s σ' = τ' : Δ].
Proof.
  intros Heq Heq'.
  induction 1 in σ', τ', Heq, Heq' |- *.
  all: constructor.
  - eapply IHEqSubst.
    all: now rewrite ?Heq ?Heq'.
  - rewrite <- Heq, <- Heq'.
    now replace A[↑ >> σ'] with A[↑ >> σ]
      by (now rewrite Heq).
Qed.

  Lemma par_subst_wk Δ Δ' Γ (ρ : Δ ≤ Δ') σ τ :
    [|- Δ] -> [|- Δ'] ->
    [Δ' |-s σ ⤳ τ : Γ] ->
    [Δ |-s σ⟨ρ⟩ ⤳ τ⟨ρ⟩ : Γ].
  Proof.
    intros HΔ HΔ' Hσ.
    induction Hσ as [|σ τ Γ A].
    1: now constructor.
    econstructor.
    - asimpl ; cbn in * ; asimpl.
      eapply IHHσ.
    - asimpl ; cbn in * ; asimpl.
      cbn.
      eapply oredtm_meta_conv.
      1: eapply par_wk ; eassumption.
      all: now bsimpl.
  Qed.

  Lemma eq_subst_wk Δ Δ' Γ (ρ : Δ ≤ Δ') σ τ :
    [|- Δ] -> [|- Δ'] ->
    [Δ' |-s σ = τ : Γ] ->
    [Δ |-s σ⟨ρ⟩ = τ⟨ρ⟩ : Γ].
  Proof.
    intros HΔ HΔ' Hσ.
    induction Hσ as [|σ τ Γ A].
    1: now constructor.
    econstructor.
    - asimpl ; cbn in * ; asimpl.
      eapply IHHσ.
    - asimpl ; cbn in * ; asimpl.
      cbn.
      eapply eqtm_meta_conv.
      1: eapply par_wk ; eassumption.
      all: now bsimpl.
  Qed.

  Lemma up_par_subst Δ Γ A σ τ :
    [|- Δ] ->
    [Δ |- A[σ]] ->
    [Δ |-s σ ⤳ τ : Γ] ->
    [Δ,, A[σ] |-s up_term_term σ ⤳ up_term_term τ : Γ,, A].
  Proof.
    intros.
    assert [|- Δ ,, A[σ]] by now econstructor.
    econstructor ; cbn.
    - eapply par_subst_ext.
      1-2: shelve.
      unshelve eapply par_subst_wk ; [..|eassumption] ; try assumption.
      now eapply wk1.
      Unshelve.
      all: now bsimpl.
    - eapply oredtm_meta_conv.
      1: econstructor ; tea ; econstructor.
      all: now bsimpl.
  Qed.

  Lemma up_eq_subst Δ Γ A σ τ :
    [|- Δ] ->
    [Δ |- A[σ]] ->
    [Δ |-s σ = τ : Γ] ->
    [Δ,, A[σ] |-s up_term_term σ = up_term_term τ : Γ,, A].
  Proof.
    intros.
    assert [|- Δ ,, A[σ]] by now econstructor.
    econstructor ; cbn.
    - eapply eq_subst_ext.
      1-2: shelve.
      unshelve eapply eq_subst_wk ; [..|eassumption] ; try assumption.
      now eapply wk1.
      Unshelve.
      all: now bsimpl.
    - eapply eqtm_meta_conv.
      1: econstructor ; tea ; econstructor.
      all: now bsimpl.
  Qed.

  Lemma subst_par_lty Δ Γ σ τ :
    [Δ |-s σ ⤳ τ : Γ] ->
    [Δ |-s σ ⤳ σ : Γ].
  Proof.
    induction 1.
    all: constructor ; tea.
    now apply par_lty in o.
  Qed.

  Lemma subst_eq_lty Δ Γ σ τ :
    [Δ |-s σ = τ : Γ] ->
    [Δ |-s σ ⤳ σ : Γ].
  Proof.
    induction 1.
    all: constructor ; tea.
    now apply par_lty, conv_refl in e.
  Qed.

  Lemma subst_conv_refl Δ Γ σ τ :
    [Δ |-s σ ⤳ τ : Γ] ->
    [Δ |-s σ = σ : Γ].
  Proof.
    induction 1.
    all: constructor ; tea.
    now apply par_lty, conv_refl in o.
  Qed.

  Lemma id_subst_ty Γ Δ (ρ : Γ ≤ Δ) :
    [|- Γ] ->
    [Γ |-s ρ >> tRel : Δ].
  Proof.
    intros HΓ.
    destruct ρ as [ρ wρ] ; cbn.
    induction wρ ; cbn.
    - now constructor.
    - inversion HΓ ; subst ; refold.
      specialize (IHwρ H1).
  Admitted.

  Let PCon (Γ : context) := forall (Δ : context) σ,
    [|- Δ] -> [Δ |-s σ ⤳ σ : Γ] ->
    forall n decl, in_ctx Γ n decl -> [Δ |- σ n ⤳ σ n : decl[σ]].
  Let PTy (Γ : context) (A A' : term) := forall (Δ : context) σ,
    [|- Δ] -> [Δ |-s σ ⤳ σ : Γ] ->
    [Δ |- A[σ] ⤳ A'[σ]].
  Let PTm (Γ : context) (A t u : term) := forall (Δ : context) σ,
    [|- Δ] -> [Δ |-s σ ⤳ σ : Γ] ->
    [Δ |- t[σ] ⤳ u[σ] : A[σ]].
  Let PTyEq (Γ : context) (A A' : term) := forall (Δ : context) σ,
    [|- Δ] -> [Δ |-s σ ⤳ σ : Γ] ->
    [Δ |- A[σ] = A'[σ]].
  Let PTmEq (Γ : context) (A t u : term) := forall (Δ : context) σ,
    [|- Δ] -> [Δ |-s σ ⤳ σ : Γ] ->
    [Δ |- t[σ] = u[σ] : A[σ]].
  Let PTyConv (Γ : context) (A B : term) :=  forall (Δ : context) σ, [|- Δ] -> 
    [Δ |-s σ ⤳ σ : Γ] -> [Δ |- A[σ] ≅ B[σ]].

  Lemma conv_subst : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: try solve [trivial | now econstructor].
    - intros * ??? * Hin.
      inversion Hin.
    - intros * ? IHΓ ? IHA * HΔ Hred Hτ * Hin.
      inversion Hin ; subst.
      + inversion Hred ; subst.
        bsimpl.
        assumption.
      + refold.
        inversion Hred ; subst.
        eapply IHΓ in H5 ; tea.
        now bsimpl.
    - intros * HA IHA HB IHB **.
      cbn.
      econstructor ; eauto.
      eapply IHB ; tea.
      + econstructor ; tea.
        now eapply par_lty in IHA.
      + eapply up_par_subst ; tea.
        now eapply par_lty in IHA.
    - intros * ? IHΓ Hin * ??.
      cbn.
      now eapply IHΓ.
    - intros * HA IHA HB IHB **.
      cbn.
      econstructor ; eauto.
      eapply IHB ; tea.
      1: econstructor ; tea.
      2: eapply up_par_subst ; tea.
      all: constructor ; now eapply par_lty in IHA.
    - intros * HA IHA HA' IHA' Ht IHt **.
      cbn.
      econstructor ; eauto.
      eapply IHt ; tea.
      1: econstructor ; tea.
      2: eapply up_par_subst ; tea.
      all: now eapply par_lty in IHA'.
    - intros * ? IHA ? IHA' ? IHA'' ? IHB ? IHt ? IHa **.
      cbn.
      eapply oredtm_meta_conv.
      1: econstructor ; eauto.
      + now eapply par_lty in IHA.
      + now eapply par_lty in IHA'.
      + eapply par_lty in IHB ; tea.
        1: econstructor ; tea ; now eapply par_lty in IHA.
        eapply up_par_subst ; tea.
        now eapply par_lty in IHA.
      + eapply IHt ; tea.
        1: econstructor ; tea ; now eapply par_lty in IHA'.
        eapply up_par_subst ; tea.
        now eapply par_lty in IHA'.
      + now bsimpl.
      + now bsimpl.
    - intros * ? IHA ? IHA' ? IHB ? IHB' ? IHf ? IHa **.
      cbn.
      eapply oredtm_meta_conv.
      3: reflexivity.
      1: econstructor ; eauto.
      + now eapply par_lty in IHA.
      + eapply par_lty in IHB ; tea.
        1: econstructor ; tea ; now eapply par_lty in IHA.
        eapply up_par_subst ; tea.
        now eapply par_lty in IHA.
      + eapply IHB'.
        1: econstructor ; tea ; now eapply par_lty in IHA.
        eapply up_par_subst ; tea.
        now eapply par_lty in IHA.
      + now bsimpl. 
    - intros * ? IHA ? IHA' ? IHB **.
      cbn.
      econstructor ; eauto.
      1: now eapply IHA.
      eapply IHB.
      1: econstructor ; tea ; now eapply par_lty in IHA.
      eapply up_par_subst ; tea.
      now eapply par_lty in IHA.
    - intros * ? IHΓ Hin **.
      cbn.
      eapply IHΓ in Hin ; tea.
      now eapply par_lty, conv_refl in Hin.
    - intros * ? IHA ? IHA' ? IHB **.
      cbn ; econstructor ; eauto.
      1: now eapply IHA.
      eapply IHB.
      1: econstructor ; tea ; now eapply par_lty in IHA.
      eapply up_par_subst ; tea.
      now eapply par_lty in IHA.
    - intros * ? IHA ? IHA' ? IHA'' ? IHt **.
      cbn ; econstructor ; eauto.
      1: now eapply IHA.
      eapply IHt.
      1: econstructor ; tea ; now eapply par_lty in IHA.
      eapply up_par_subst ; tea.
      now eapply par_lty in IHA.
    - intros * ? IHA ? IHA' ? IHB ? IHB' ? IHf ? IHa **.
      cbn.
      eapply eqtm_meta_conv.
      1: econstructor ; eauto.
      + now eapply IHA.
      + eapply IHB.
        1: econstructor ; tea ; now eapply par_lty in IHA.
        eapply up_par_subst ; tea.
        now eapply par_lty in IHA.
      + eapply IHB'.
        1: econstructor ; tea ; now eapply par_lty in IHA.
        eapply up_par_subst ; tea.
        now eapply par_lty in IHA.
      + now bsimpl.
      + now bsimpl.
  Qed.

End Subst.

Section Boundary.

  Lemma par_conv_l Γ A A' :
    [Γ |- A ⤳ A'] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'].
  Proof.
    intros ? HA'.
    eapply TypeConvParL ; refold ; tea.
    econstructor.
    now eapply conv_refl in HA'.
  Qed.

  Lemma par_conv_r Γ A A' :
    [Γ |- A ⤳ A'] ->
    [Γ |- A'] ->
    [Γ |- A' ≅ A].
  Proof.
    intros ? HA'.
    eapply TypeConvSym ; refold.
    now eapply par_conv_l.
  Qed.

  Let PCon (Γ : context) := forall n decl, in_ctx Γ n decl -> [Γ |- decl].
  Let PTy (Γ : context) (A A' : term) := [Γ |- A'].
  Let PTm (Γ : context) (A t t' : term) := [Γ |- A] × [Γ |- t' : A].
  Let PTyEq (Γ : context) (A B : term) := [Γ |- B].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- A] × [Γ |- u : A].
  Let PTyConv (Γ : context) (A B : term) := [Γ |- A] × [Γ |- B].

  Lemma boundary_right : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: try solve [trivial | now econstructor].
    - intros * Hin.
      inversion Hin.
    - intros * ? HΓ ?? * Hin.
      inversion Hin ; subst.
      + now eapply par_wk1.
      + eapply par_wk1 ; tea.
        now eapply HΓ.
    - intros * ? IHA ? IHB.
      econstructor ; tea.
      eapply par_ctx_conv ; tea.
      2: econstructor ; tea ; now eapply par_ctx_ty in IHA.
      now eapply ctx_conv_tip, par_conv_r.
    - intros * ? HΓ **.
      split ; eauto.
      now econstructor.
    - intros * HA [] ? [].
      split ; eauto.
      econstructor ; tea.
      eapply par_ctx_conv ; tea.
      + eapply ctx_conv_tip, par_conv_r ; now econstructor.
      + econstructor.
        1: now eapply par_ctx_ty in HA.
        now econstructor.
    - intros * ? [? IHA''] ? ? ? [].
      split.
      + econstructor ; tea.
        eapply par_ctx_conv ; tea.
        2: now econstructor ; [eapply par_ctx_ty in IHA'' |..].
        eapply ctx_conv_tip.
        now econstructor.
      + econstructor ; tea.
        * 1: eapply TypeConvTrans ; refold ; tea.
          now eapply par_conv_r. 
        * eapply par_ctx_conv ; tea.
          -- eapply ctx_conv_tip.
             now eapply par_conv_r.
          -- econstructor ; tea.
             now eapply par_ctx_ty in IHA''. 
    - intros * ? _ ? _ ? [] ? _ ? [] ? [].
      split.
      + eapply conv_subst ; tea.
        1: now eapply par_ctx_ty.
        econstructor ; cbn.
        ** asimpl.
           admit.
        ** admit.
      + admit. 
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Abort.

End Boundary.

Section ConvSym.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := True.
  Let PTm (Γ : context) (A t t' : term) := True.
  Let PTyEq (Γ : context) (A B : term) := [Γ |- B = A].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- u = t : A].
  Let PTyConv (Γ : context) (A B : term) := [Γ |- B ≅ A].

  Lemma conv_sym : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv.
    apply ParInduction.
    all: try solve [trivial | now econstructor].
    - intros * ? IHA ? IHA' ? IHB.
      econstructor ; eauto.
      + now eapply par_lty in IHA'.
      + eapply par_ctx_conv ; tea.
        1: eapply ctx_conv_tip ; now constructor.
        eapply par_lty in IHA'.
        constructor ; tea.
        now eapply par_ctx_ty in IHA'.
    - intros * ? IHA ? IHA' ? IHB.
      econstructor ; eauto.
      + constructor.
        now eapply par_lty in IHA'.
      + eapply par_ctx_conv ; tea.
        1: eapply ctx_conv_tip ; now do 2 constructor.
        eapply par_lty in IHA'.
        econstructor.
        2: now constructor.
        now eapply par_ctx_ty in IHA'.
    - intros * HA IHA ? IHA' ? IHB.
      econstructor ; tea.
      + admit. (* boundary *)
      + admit. (* annotations for λ are not related the right way (transitivity) *)
      + eapply par_ctx_conv ; tea.
        1: now eapply ctx_conv_tip.
        econstructor.
        1: now eapply par_ctx_ty in HA.
        admit. (* boundary *)
    - intros * HA _ ? IHA' ? IHB ? IHf ? IHa.
      econstructor.
      1: econstructor ; tea.
      + admit. (* boundary *)
      + admit. (* boundary *)
      + eapply par_ctx_conv ; tea.
        1: now eapply ctx_conv_tip.
        econstructor.
        1: now eapply par_ctx_ty in HA.
        admit. (* boundary *)
      + econstructor ; tea.
        admit. (* product congruence for ≅ *)
      + now econstructor.
  Admitted.

Section Congruences.

  Lemma type_par_red_prod Γ A A' B B' :
    [Γ |- A ⤳* A'] ->
    [Γ,, A |- B ⤳* B'] ->
    [Γ |- tProd A B ⤳* tProd A' B'].
  Proof.
    intros HA HB.
    induction HB ; refold.
    - induction HA.
      + now do 2 constructor.
      + econstructor 2 ; refold.
        1: now econstructor.
        apply IHHA.
        eapply par_clos_lty in HA.
        eapply par_ctx_conv ; tea.
        * now eapply ctx_conv_tip, par_conv_r.
        * constructor ; tea.
          now eapply par_ctx_ty in HA.
    - econstructor ; tea.
      econstructor ; tea.
      now eapply par_clos_lty in HA.
  Qed.

  Lemma type_conv_inv Γ A B :
    [Γ |- A ≅ B ] ->
    (∑ A' B', [× [Γ |- A ⤳* A'], [Γ |- B ⤳* B'] & [Γ |- A' = B']]).
  Proof.
    induction 1 ; refold.
    - exists A, B.
      split ; tea.
      all: econstructor.
      + now eapply par_lty.
      + admit. (* left bias *)
    - destruct IHTypeConv as (?&?&[]).
      do 2 eexists ; split.
      3: eassumption.
      all: tea.
      now econstructor.
    - destruct IHTypeConv as (?&?&[]).
      do 2 eexists ; split.
      3: eassumption.
      all: tea.
      now econstructor.
  Admitted.

  Lemma type_conv_par_clos Γ A A' B B' :
    [Γ |- A ⤳* A'] -> [Γ |- B ⤳* B'] -> [Γ |- A' = B'] ->
    [Γ |- A ≅ B ].
  Proof.
    intros HA HB He.
    induction HA ; refold.
    1: induction HB ; refold.
    all: now econstructor.
  Qed.

  Lemma par_clos_conv_l Γ A A' :
    [Γ |- A ⤳* A'] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'].
  Proof.
    intros HA HA'.
    eapply type_conv_par_clos ; tea.
    2: now eapply conv_refl in HA'.
    eapply conv_refl in HA'.
    now constructor.
  Qed.

  Lemma par_clos_conv_r Γ A A' :
    [Γ |- A ⤳* A'] ->
    [Γ |- A'] ->
    [Γ |- A' ≅ A].
  Proof.
    intros HA HA'.
    eapply type_conv_par_clos ; tea.
    2: now eapply conv_refl in HA'.
    eapply conv_refl in HA'.
    now constructor.
  Qed.

  Lemma TypeConvParProd Γ A A' B B' :
    [Γ |- A] ->
    [Γ |- A ≅ A'] ->
    [Γ ,, A |- B ≅ B'] -> 
    [ Γ |- tProd A B ≅ tProd A' B'].
  Proof.
    intros HAt HA HB.
    assert [|- Γ] by now eapply par_ctx_ty in HAt.
    eapply type_conv_inv in HA as (Ar&Ar'&[]).
    eapply type_conv_inv in HB as (Br&Br'&[]).
    eapply type_conv_par_clos.
    - now eapply type_par_red_prod.
    - eapply type_par_red_prod ; tea.
      eapply par_clos_ctx_conv ; tea.
      + eapply ctx_conv_tip, type_conv_par_clos ; tea.
        admit.
        (* symmetry! *)
      + econstructor ; tea.
        now eapply par_clos_lty.
    - econstructor ; tea.
      1: now eapply par_lty in e.
      eapply par_ctx_conv ; tea.
      2: econstructor ; tea.
      2: now eapply par_lty.
      eapply ctx_conv_tip.
      eapply par_clos_conv_r ; tea.
      now eapply par_lty in e.
  Admitted.