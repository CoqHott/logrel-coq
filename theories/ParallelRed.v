(** * LogRel.ParallelRed: definition of parallel reduction. *)
From Coq Require Import ssreflect.
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
          [ Γ |- A' ≅ A] ->
          [Γ ,, A |- B] ->
          [ Γ ,, A' |- t ⤳ t' : B ] ->
          [ Γ |- a ⤳ a' : A ] ->
          [ Γ |- tApp A B (tLambda A' t) a ⤳ t'[a'..] : B[a..] ]
      | TermParApp {Γ} {f f' a a' A A' B B'} :
          [Γ |- A] ->
          [Γ |- A ⤳ A' ] ->
          [Γ,, A |- B] ->
          [Γ,, A |- B ⤳ B'] ->
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
        [ Γ |- A = A' : U] -> 
        [Γ ,, A |- B = B' : U] -> 
        [ Γ |- tProd A B = tProd A' B' : U]
      | TermEqParLam {Γ} {A A' A'' B t t'} :
        [ Γ |- A ≅ A' ] ->
        [Γ |- A ≅ A'' ] ->
        [ Γ ,, A |- t = t' : B ] -> 
        [ Γ |- tLambda A t = tLambda A' t' : tProd A'' B]
      | TermEqParApp {Γ} {f f' a a' A A' B B'} :
        [Γ |- A ≅ A' ] ->
        [Γ,, A |- B ≅ B'] ->
        [ Γ |- f = f' : tProd A B ] -> 
        [ Γ |- a = a' : A ] -> 
        [ Γ |- tApp A B f a = tApp A' B' f' a' : B[a..] ]
      | TermEqParConv {Γ} {A B t t'} :
        [ Γ |- t = t' : A ] -> 
        [ Γ |- A ≅ B ] -> 
        [ Γ |- t = t' : B ]

  with TypeConvPar : context -> term -> term  -> Type :=
      | TypeConvParEq {Γ A B} :
          [ Γ |- A = B] ->
          [ Γ |- A ≅ B]
      | TypeConvParL {Γ} {A A' B} :
          [ Γ |- A ⤳ A' ] ->
          [ Γ |- A' ≅ B] ->
          [ Γ |- A ≅ B ]
      | TypeConvParR {Γ} {A B B'} :
          [ Γ |- B ⤳ B' ] ->
          [ Γ |- A ≅ B'] ->
          [ Γ |- A ≅ B ]

  with TermConvPar : context -> term -> term -> term -> Type :=
      | TermConvParEq {Γ A t u} :
          [ Γ |- t = u : A] ->
          [ Γ |- t ≅ u : A]
      | TermConvParL {Γ} {A t t' u} :
          [ Γ |- t ⤳ t' : A] ->
          [ Γ |- t' ≅ u : A] ->
          [ Γ |- t ≅ u : A]
      | TermConvParR {Γ} {A t u u'} :
          [ Γ |- u ⤳ u' : A] ->
          [ Γ |- t ≅ u' : A] ->
          [ Γ |- t ≅ u : A]
      
  where "[   |- Γ ]" := (WfContextPar Γ)
  and   "[ Γ |- A ⤳ A' ]" := (TypePar Γ A A')
  and   "[ Γ |- A ]" := (TypePar Γ A A)
  and   "[ Γ |- t ⤳ t' : A ]" := (TermPar Γ A t t')
  and   "[ Γ |- t : T ]" := (TermPar Γ T t t)
  and   "[ Γ |- A = B ]" := (TypeEqPar Γ A B)
  and   "[ Γ |- t = t' : T ]" := (TermEqPar Γ T t t')
  and   "[ Γ |- A ≅ B ]" := (TypeConvPar Γ A B)
  and   "[ Γ |- t ≅ t' : T ]" := (TermConvPar Γ T t t').

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
  #[export] Instance ConvType_Par : ConvType pa := TypeConvPar.
  #[export] Instance ConvTerm_Par : ConvTerm pa := TermConvPar.
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
    change TypeConvPar with (conv_type (ta := pa)) in * ;
    change TermConvPar with (conv_term (ta := pa)) in * ;
    change TypeParClos with (red_ty (ta := pa)) in *;
    change TermParClos with (red_tm (ta := pa)) in *;
    change TypePar with (osred_ty (ta := pa)) in *;
    change TermPar with (osred_tm (ta := pa)) in *.

  Smpl Add fold_pa : refold.

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
    Minimality for TypeConvPar  Sort Type with
    Minimality for TermConvPar  Sort Type.

Combined Scheme _ParInduction from
    WfContextPar_rect_nodep,
    TypePar_rect_nodep,
    TermPar_rect_nodep,
    TypeEqPar_rect_nodep,
    TermEqPar_rect_nodep,
    TypeConvPar_rect_nodep,
    TermConvPar_rect_nodep.

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
  intros PCon PTy PTm PTyEq PTmEq PTyConv PTmConv **.
  pose proof (_ParInduction PCon PTy PTm PTyEq PTmEq PTyConv PTmConv) as H.
  destruct H as (?&?&?&?&?&?&?).
  all: try (assumption ; fail).
  repeat (split;[assumption|]); assumption.
Qed.

Definition ParInductionConcl :=
  ltac:(
    let t := eval cbv delta [ParInductionType] beta in ParInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv : rename.

Import ParallelTypingData.

Section LeftTypable.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := [Γ |- A].
  Let PTm (Γ : context) (A t t' : term) := [Γ |- t : A].
  Let PTyEq (Γ : context) (A B : term) := [Γ |- A].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- t : A].
  Let PTyConv (Γ : context) (A B : term) := [Γ |- A].
  Let PTmConv (Γ : context) (A t u : term) := [Γ |- t : A].

  Theorem par_lty : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
    apply ParInduction.
    all: try solve [trivial | now econstructor].
    intros.
    eapply TermParApp ; refold ; tea.
    now econstructor.
  Qed.

  Theorem ctx_lty Γ Δ : [|-[pa] Γ ≅ Δ] -> [|-[pa] Γ].
  Proof.
    induction 1.
    all: constructor ; tea.
    now eapply par_lty in c.
  Qed.

End LeftTypable.

Section CtxTypable.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := [|- Γ].
  Let PTm (Γ : context) (A t t' : term) := [|- Γ].
  Let PTyEq (Γ : context) (A B : term) := [|- Γ].
  Let PTmEq (Γ : context) (A t u : term) := [|- Γ].
  Let PTyConv (Γ : context) (A B : term) := [|- Γ].
  Let PTmConv (Γ : context) (A t u : term) := [|- Γ].

  Theorem par_ctx_ty : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
    apply ParInduction.
    all: trivial.
  Qed.

End CtxTypable.

Section ConvRefl.

  Let PCon (Γ : context) := [|- Γ ≅ Γ].
  Let PTy (Γ : context) (A A' : term) := [Γ |- A = A] × [Γ |- A ≅ A].
  Let PTm (Γ : context) (A t t' : term) := [Γ |- t = t : A] × [Γ |- t ≅ t : A].
  Let PTyEq (Γ : context) (A B : term) := [Γ |- A = A] × [Γ |- A ≅ A].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- t = t : A] × [Γ |- t ≅ t : A].
  Let PTyConv (Γ : context) (A B : term) := [Γ |- A = A] × [Γ |- A ≅ A].
  Let PTmConv (Γ : context) (A t u : term) := [Γ |- t = t : A] × [Γ |- t ≅ t : A].

  Lemma conv_refl : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
    apply ParInduction.
    all: try solve [trivial | split ; [..|econstructor] ; now econstructor].
    - constructor.
    - now constructor.  
    - intros * ? [IHA IHA'] ?? ? [IHB IHB'] ? [IHt IHt'] ? [IHa IHa'].
      split.
      2: econstructor.
      all: econstructor ; tea.
      all: now econstructor.
  Qed.

End ConvRefl.

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
  Let PTmConv (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].

  Theorem par_wk : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
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
    - intros * ? IHAred ? IHAconv ? IHB ? IHt ? IHa **.
      assert [Δ |- A⟨ρ⟩] by now eapply IHAred.
      assert [Δ |- A'⟨ρ⟩] by (now unshelve epose proof (IHAconv _ _ _) as ?%par_lty).
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
    - intros * ? IHA ? IHB **.
      cbn.
      econstructor ; eauto.
      eapply IHB with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply par_lty in IHA.
    - intros **.
      econstructor ; tea.
      now eapply in_ctx_wk.
    - intros * ? IHA ? IHB **.
      cbn.
      econstructor ; eauto.
      eapply IHB with (ρ := wk_up _ _).
      econstructor ; tea.
      econstructor.
      now eapply par_lty in IHA.
    - intros * ? IHA ?? ? IHt **.
      cbn.
      econstructor ; eauto.
      eapply IHt with (ρ := wk_up _ _).
      econstructor ; tea.
      now eapply par_lty in IHA.
    - intros * ? IHA ? IHB ? IHf ? IHa **.
      cbn.
      evar (B'' : term) ; replace (B[_]⟨ρ⟩) with B'' ; subst B''.
      1: econstructor ; eauto.
      + eapply IHB with (ρ := wk_up _ _) ; econstructor ; tea.
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
  Let PTmConv' (Γ : context) (A t u : term) := forall T, [Γ |- T ] ->
    [Γ,,T |- t⟨↑⟩ ≅ u⟨↑⟩ : A⟨↑⟩].

  Corollary par_wk1 : ParInductionConcl PCon' PTy' PTm' PTyEq' PTmEq' PTyConv' PTmConv'.
  Proof.
    subst PCon' PTy' PTm' PTyEq' PTmEq' PTyConv' PTmConv'.
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
    now eapply conv_refl in HA.
  Qed.


  Lemma ctx_conv_tip Γ A A' : [Γ |- A ≅ A'] -> [|- Γ,, A ≅ Γ,,A'].
  Proof.
    intros HA.
    econstructor ; tea.
    eapply conv_refl.
    now eapply par_ctx_ty in HA.
  Qed.

  Let PCon (Γ : context) := forall Δ, [|- Δ ≅ Γ] ->
    forall decl n, in_ctx Γ n decl -> ∑ decl', in_ctx Δ n decl' × [Δ |- decl' ≅ decl].
  Let PTy (Γ : context) (A A' : term) := forall Δ, [|- Δ ≅ Γ] -> [Δ |- A ⤳ A'].
  Let PTm (Γ : context) (A t t' : term) := forall Δ, [|- Δ ≅ Γ] ->
    [Δ |- t ⤳ t' : A].
  Let PTyEq (Γ : context) (A B : term) := forall Δ, [|- Δ ≅ Γ] ->
    [Δ |- A = B].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ, [|- Δ ≅ Γ] ->
    [Δ |- t = u : A].
  Let PTyConv (Γ : context) (A B : term) := forall Δ, [|- Δ ≅ Γ] ->
    [Δ |- A ≅ B].
  Let PTmConv (Γ : context) (A t u : term) := forall Δ, [|- Δ ≅ Γ] ->
    [Δ |- t ≅ u : A].


  Theorem par_ctx_conv : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
    apply ParInduction.
    all: try solve [now econstructor].
    - intros ? Hctx ? * Hin.
      inversion Hctx ; subst.
      inversion Hin.
    - intros * ? IHΓ ? IHA ? Hconv * Hin.
      inversion Hconv ; subst.
      inversion Hin ; subst.
      + eexists ; split.
        1: now constructor.
        eapply par_wk1 ; tea.
        now eapply par_lty in H5.
      + refold.
        edestruct IHΓ as [? []] ; tea.
        eexists ; split.
        1: now constructor.
        refold.
        eapply par_wk1 ; tea.
        now eapply par_lty in H5.
    - intros.
      econstructor.
      now eapply ctx_lty. 
    - intros * HA IHA ? IHB ??.
      econstructor.
      1: eauto.
      eapply IHB, ctx_conv_ext ; tea.
      now eapply par_lty in IHA.
    - intros * ? IHΓ ? **.
      edestruct IHΓ as [? []]; tea.
      econstructor ; tea ; econstructor ; tea.
      now eapply ctx_lty.
    - intros * HA IHA HB IHB ??. 
      econstructor.
      1: eauto.
      eapply IHB, ctx_conv_ext ; tea.
      eapply par_lty in IHA ; tea.
      now econstructor.
    - intros * HA'' IHA'' HA IHA Ht IHt ??.
      econstructor.
      1-2: eauto.
      eapply IHt, ctx_conv_ext ; tea.
      now eapply par_lty in IHA.
    - intros * HA IHA HA' IHA' ? IHB ? IHt ? IHa ??.
      econstructor.
      + now eapply IHA.
      + eauto.
      + eapply IHB, ctx_conv_ext ; tea.
        now eapply par_lty in IHA.
      + eapply IHt, ctx_conv_ext ; tea.
        now eapply par_lty in IHA'.
      + eauto.
    - intros * ? IHA ? IHA' ? IHB ? IHB' ? IHf ? IHa ??.
      assert [Δ |- A] by now apply IHA.
      econstructor ; eauto.
      + now eapply IHB, ctx_conv_ext.
      + now eapply IHB', ctx_conv_ext.
    - intros.
      econstructor.
      now eapply ctx_lty.
    - intros * ? IHA ? IHB ??.
      econstructor ; eauto.
      eapply IHB, ctx_conv_ext ; tea.
      now eapply par_lty in IHA.
    - intros * ? IHΓ ? ??.
      edestruct IHΓ as [? []]; tea.
      eapply TermEqParConv ; refold ; tea.
      econstructor ; tea.
      now eapply ctx_lty.
    - intros * ? IHA ? IHB ??.
      econstructor.
      1: eauto.
      eapply IHB, ctx_conv_ext ; tea.
      econstructor.
      now eapply par_lty in IHA.
    - intros * HA'' IHA'' HA IHA Ht IHt ??.
      econstructor.
      1-2: eauto.
      eapply IHt, ctx_conv_ext ; tea.
      now eapply par_lty in IHA.
    - intros * HA IHA ? IHB ? IHt ? IHa ??.
      econstructor ; eauto.
      eapply IHB, ctx_conv_ext ; tea.
      now eapply par_lty in IHA.
  Qed. 

End CtxConv.


(* Section RightTypable.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := True.
  Let PTm (Γ : context) (A t t' : term) := True.
  Let PTyEq (Γ : context) (A B : term) := [Γ |- B].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- u : A].
  Let PTyConv (Γ : context) (A B : term) := [Γ |- B].
  Let PTmConv (Γ : context) (A t u : term) := [Γ |- u : A].

  Theorem par_rty : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
    apply ParInduction.
    all: try solve [trivial | now econstructor].
    - intros * ? IHA ? IHB.
      econstructor ; tea.
      eapply par_ctx_conv ; tea.
    eapply TermParApp ; refold ; tea.
    now econstructor.
  Qed.

End RightTypable. *)

Section ConvSym.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A A' : term) := True.
  Let PTm (Γ : context) (A t t' : term) := True.
  Let PTyEq (Γ : context) (A B : term) := [Γ |- B = A].
  Let PTmEq (Γ : context) (A t u : term) := [Γ |- u = t : A].
  Let PTyConv (Γ : context) (A B : term) := [Γ |- B ≅ A].
  Let PTmConv (Γ : context) (A t u : term) := [Γ |- u ≅ t : A].

  Lemma conv_sym : ParInductionConcl PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq PTyConv PTmConv.
    apply ParInduction.
    all: try solve [trivial | now econstructor].
    - intros * ? IHA ? IHB.
      econstructor ; tea.
      eapply par_ctx_conv, ctx_conv_tip ; tea.
      now econstructor.
    - intros * ? IHA ? IHB.
      econstructor ; tea.
      eapply par_ctx_conv, ctx_conv_tip ; tea.
      now do 2 econstructor.
    - intros * ? IHA ? IHA' ? IHB.
      econstructor ; tea.
      + admit. (* annotations for λ are not related the right way (transitivity) *)
      + eapply par_ctx_conv, ctx_conv_tip ; tea.
    - intros * ? IHA ? IHB ? IHf ? IHa.
      econstructor.
      1: econstructor ; tea.
      + now eapply par_ctx_conv, ctx_conv_tip.
      + econstructor ; tea.
        admit. (* product congruence for ≅ *)
      + now econstructor.
      + admit. (* substitution *)
  Admitted.

Section Congruences.

  Lemma TermConvParVar Γ n n' decl :
    [   |- Γ ] ->
    in_ctx Γ n decl ->
    n = n' ->
    [ Γ |- tRel n ≅ tRel n' : decl ].
  Proof.
    intros ; subst.
    now do 2 econstructor.
  Qed.

  Lemma TypeConvParProd Γ A A' B B' :
    [Γ |- A ≅ A' ] ->
    [Γ ,, A |- B ≅ B'] -> 
    [ Γ |- tProd A B ≅ tProd A' B'].
  Proof.
    intros HA HB.
    induction HA in B, B', HB |- * ; refold.
    - remember (Γ,,A) as Δ in HB.
      induction HB ; refold.
      + subst.
        now do 2 econstructor.
      + subst.
        eapply TypeConvParL ; refold.
        1: econstructor ; tea.
        2: now eapply IHHB.
        now eapply par_lty in t.
      + subst.
        eapply TypeConvParR ; refold.
        2: now eapply IHHB.
        econstructor.
  Abort.