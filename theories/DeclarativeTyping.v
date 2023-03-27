(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction.

Set Primitive Projections.

(** Definitions in this file should be understood as the _specification_ of conversion
or typing, done in a declarative fashion. For instance, we _demand_ that conversion
be transitive by adding a corresponding rule. *)

(** ** Definitions *)
Definition elimSuccHypTy P :=
  tProd tNat (arr P P[tSucc (tRel 0)]⇑).

Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition
  here before declaring the instance to which abstract notations are bound. *)
  Close Scope typing_scope.


  (** Typing and conversion are mutually defined inductive relations. To avoid having
  to bother with elimination of propositions, we put them in the Type sort. *)

  (** **** Context well-formation *)
  Inductive WfContextDecl : context -> Type :=
      | connil : [ |- ε ]
      | concons {Γ A} : 
          [ |- Γ ] -> 
          [ Γ |- A ] -> 
          [ |-  Γ ,, A]
  (** **** Type well-formation *)
  with WfTypeDecl  : context -> term -> Type :=
      | wfTypeU {Γ} : 
          [ |- Γ ] -> 
          [ Γ |- U ] 
      | wfTypeProd {Γ} {A B} : 
          [ Γ |- A ] -> 
          [Γ ,, (A) |- B ] -> 
          [ Γ |- tProd A B ]
      | wfTypeNat {Γ} : 
          [|- Γ] ->
          [Γ |- tNat]
      | wfTypeEmpty {Γ} : 
          [|- Γ] ->
          [Γ |- tEmpty]
      | wfTypeUniv {Γ} {A} :
          [ Γ |- A : U ] -> 
          [ Γ |- A ]
  (** **** Typing *)
  with TypingDecl : context -> term -> term -> Type :=
      | wfVar {Γ} {n decl} :
          [   |- Γ ] ->
          in_ctx Γ n decl ->
          [ Γ |- tRel n : decl ]
      | wfTermProd {Γ} {A B} :
          [ Γ |- A : U] -> 
          [Γ ,, (A) |- B : U ] ->
          [ Γ |- tProd A B : U ]
      | wfTermLam {Γ} {A B t} :
          [ Γ |- A ] ->        
          [ Γ ,, A |- t : B ] -> 
          [ Γ |- tLambda A t : tProd A B]
      | wfTermApp {Γ} {f a A B} :
          [ Γ |- f : tProd A B ] -> 
          [ Γ |- a : A ] -> 
          [ Γ |- tApp f a : B[a..] ]
      | wfTermNat {Γ} :
          [|-Γ] ->
          [Γ |- tNat : U]
      | wfTermZero {Γ} :
          [|-Γ] ->
          [Γ |- tZero : tNat]
      | wfTermSucc {Γ n} :
          [Γ |- n : tNat] ->
          [Γ |- tSucc n : tNat]
      | wfTermNatElim {Γ P hz hs n} :
        [Γ ,, tNat |- P ] ->
        [Γ |- hz : P[tZero..]] ->
        [Γ |- hs : elimSuccHypTy P] ->
        [Γ |- n : tNat] ->
        [Γ |- tNatElim P hz hs n : P[n..]]
      | wfTermEmpty {Γ} :
          [|-Γ] ->
          [Γ |- tEmpty : U]
      | wfTermEmptyElim {Γ P e} :
        [Γ ,, tEmpty |- P ] ->
        [Γ |- e : tEmpty] ->
        [Γ |- tEmptyElim P e : P[e..]]
      | wfTermConv {Γ} {t A B} :
          [ Γ |- t : A ] -> 
          [ Γ |- A ≅ B ] -> 
          [ Γ |- t : B ]
  (** **** Conversion of types *)
  with ConvTypeDecl : context -> term -> term  -> Type :=  
      | TypePiCong {Γ} {A B C D} :
          [ Γ |- A] ->
          [ Γ |- A ≅ B] ->
          [ Γ ,, A |- C ≅ D] ->
          [ Γ |- tProd A C ≅ tProd B D]
      | TypeRefl {Γ} {A} : 
          [ Γ |- A ] ->
          [ Γ |- A ≅ A]
      | convUniv {Γ} {A B} :
        [ Γ |- A ≅ B : U ] -> 
        [ Γ |- A ≅ B ]
      | TypeSym {Γ} {A B} :
          [ Γ |- A ≅ B ] ->
          [ Γ |- B ≅ A ]
      | TypeTrans {Γ} {A B C} :
          [ Γ |- A ≅ B] ->
          [ Γ |- B ≅ C] ->
          [ Γ |- A ≅ C]
  (** **** Conversion of terms *)
  with ConvTermDecl : context -> term -> term -> term -> Type :=
      | TermBRed {Γ} {a t A B} :
              [ Γ |- A ] ->
              [ Γ ,, A |- t : B ] ->
              [ Γ |- a : A ] ->
              [ Γ |- tApp (tLambda A t) a ≅ t[a..] : B[a..] ]
      | TermPiCong {Γ} {A B C D} :
          [ Γ |- A : U] ->
          [ Γ |- A ≅ B : U ] ->
          [ Γ ,, A |- C ≅ D : U ] ->
          [ Γ |- tProd A C ≅ tProd B D : U ]
      | TermAppCong {Γ} {a b f g A B} :
          [ Γ |- f ≅ g : tProd A B ] ->
          [ Γ |- a ≅ b : A ] ->
          [ Γ |- tApp f a ≅ tApp g b : B[a..] ]
      | TermFunExt {Γ} {f g A B} :
          [ Γ |- A ] ->
          [ Γ |- f : tProd A B ] ->
          [ Γ |- g : tProd A B ] ->
          [ Γ ,, A |- eta_expand f ≅ eta_expand g : B ] ->
          [ Γ |- f ≅ g : tProd A B ]
      | TermSuccCong {Γ} {n n'} :
          [Γ |- n ≅ n' : tNat] ->
          [Γ |- tSucc n ≅ tSucc n' : tNat]
      | TermNatElimCong {Γ P P' hz hz' hs hs' n n'} :
          [Γ ,, tNat |- P ≅ P'] ->
          [Γ |- hz ≅ hz' : P[tZero..]] ->
          [Γ |- hs ≅ hs' : elimSuccHypTy P] ->
          [Γ |- n ≅ n' : tNat] ->
          [Γ |- tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : P[n..]]        
      | TermNatElimZero {Γ P hz hs} :
          [Γ ,, tNat |- P ] ->
          [Γ |- hz : P[tZero..]] ->
          [Γ |- hs : elimSuccHypTy P] ->
          [Γ |- tNatElim P hz hs tZero ≅ hz : P[tZero..]]
      | TermNatElimSucc {Γ P hz hs n} :
          [Γ ,, tNat |- P ] ->
          [Γ |- hz : P[tZero..]] ->
          [Γ |- hs : elimSuccHypTy P] ->
          [Γ |- n : tNat] ->
          [Γ |- tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]]
      | TermEmptyElimCong {Γ P P' e e'} :
          [Γ ,, tEmpty |- P ≅ P'] ->
          [Γ |- e ≅ e' : tEmpty] ->
          [Γ |- tEmptyElim P e ≅ tEmptyElim P' e' : P[e..]]
      | TermRefl {Γ} {t A} :
          [ Γ |- t : A ] -> 
          [ Γ |- t ≅ t : A ]
      | TermConv {Γ} {t t' A B} :
          [ Γ |- t ≅ t': A ] ->
          [ Γ |- A ≅ B ] ->
          [ Γ |- t ≅ t': B ]
      | TermSym {Γ} {t t' A} :
          [ Γ |- t ≅ t' : A ] ->
          [ Γ |- t' ≅ t : A ]
      | TermTrans {Γ} {t t' t'' A} :
          [ Γ |- t ≅ t' : A ] ->
          [ Γ |- t' ≅ t'' : A ] ->
          [ Γ |- t ≅ t'' : A ]
      
  where "[   |- Γ ]" := (WfContextDecl Γ)
  and   "[ Γ |- T ]" := (WfTypeDecl Γ T)
  and   "[ Γ |- t : T ]" := (TypingDecl Γ T t)
  and   "[ Γ |- A ≅ B ]" := (ConvTypeDecl Γ A B)
  and   "[ Γ |- t ≅ t' : T ]" := (ConvTermDecl Γ T t t').

  (** (Typed) reduction is defined afterwards,
  rather than mutually with the other relations. *)

  Local Coercion isterm : term >-> class.

  Inductive OneRedDecl (Γ : context) : class -> term -> term -> Type :=
  | BRed {A B : term} {a t} :
      [ Γ |- A ] -> 
      [ Γ ,, A |- t : B ] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp (tLambda A t) a ⇒ t[a..] : B[a..] ]
  | appSubst {A B t u a} :
      [ Γ |- t ⇒ u : tProd A B] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp t a ⇒ tApp u a : B[a..] ]
  | natElimSubst {P hz hs n n'} :
      [Γ ,, tNat |- P] ->
      [Γ |- hz : P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy P] ->
      [Γ |- n ⇒ n' : tNat] ->
      [Γ |- tNatElim P hz hs n ⇒ tNatElim P hz hs n' : P[n..]]        
  | natElimZero {P hz hs} :
      [Γ ,, tNat |- P ] ->
      [Γ |- hz : P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs tZero ⇒ hz : P[tZero..]]
  | natElimSucc {P hz hs n} :
      [Γ ,, tNat |- P ] ->
      [Γ |- hz : P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy P] ->
      [Γ |- n : tNat] ->
      [Γ |- tNatElim P hz hs (tSucc n) ⇒ tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]]
  | emptyElimSubst {P e e'} :
      [Γ ,, tEmpty |- P] ->
      [Γ |- e ⇒ e' : tEmpty] ->
      [Γ |- tEmptyElim P e ⇒ tEmptyElim P e' : P[e..]]
  | termRedConv {A B : term} {t u} :
      [ Γ |- t ⇒ u : A ] ->
      [ Γ |- A ≅ B ] ->
      [ Γ |- t ⇒ u : B ]
  | typeRedUniv {A B} :
      [ Γ |- A ⇒ B : U ] ->
      [ Γ |- A ⇒ B ]

  where "[ Γ |- t ⇒ u : A ]" := (OneRedDecl Γ (isterm A) t u)
  and "[ Γ |- A ⇒ B ]" := (OneRedDecl Γ istype A B).

  Local Notation "[ Γ |- t ⇒ u ∈ A ]" := (OneRedDecl Γ A t u).

  Inductive RedClosureDecl (Γ : context) (A : class) : term -> term -> Type :=
      | red_id {t} :
        match A with istype => [ Γ |- t ] | isterm A => [ Γ |- t : A ] end ->
        [ Γ |- t ⇒* t ∈ A ]
      | red_red {t t'} :
        [ Γ |- t ⇒ t' ∈ A] ->
        [Γ |- t ⇒* t' ∈ A]
      | red_trans {t t' u} :
        [ Γ |- t ⇒* t' ∈ A ] ->
        [ Γ |- t' ⇒* u ∈ A ] ->
        [ Γ |- t ⇒* u ∈ A ]
  where "[ Γ |- t ⇒* t' ∈ A ]" := (RedClosureDecl Γ A t t').

End Definitions.

Definition OneRedTermDecl Γ A t u := OneRedDecl Γ (isterm A) t u.
Definition OneRedTypeDecl Γ A B := OneRedDecl Γ istype A B.
Definition TermRedClosure Γ A t u := RedClosureDecl Γ (isterm A) t u.
Definition TypeRedClosure Γ A B := RedClosureDecl Γ istype A B.

Notation "[ Γ |- t ⇒ u ∈ A ]" := (OneRedDecl Γ A t u).
Notation "[ Γ |- t ⇒* u ∈ A ]" := (RedClosureDecl Γ A t u).

Notation "[ Γ |- t ⇒ u : A ]" := (OneRedTermDecl Γ A t u) : declarative_scope.
Notation "[ Γ |- A ⇒ B ]" := (OneRedTypeDecl Γ A B).

(** ** Instances *)
(** Used for printing (see Notations) and as a support for the generic typing
properties used for the logical relation (see GenericTyping). *)
Module DeclarativeTypingData.

  #[export] Instance WfContext_Decl : WfContext de := WfContextDecl.
  #[export] Instance WfType_Decl : WfType de := WfTypeDecl.
  #[export] Instance Typing_Decl : Inferring de := TypingDecl.
  #[export] Instance Inferring_Decl : Typing de := TypingDecl.
  #[export] Instance InferringRed_Decl : InferringRed de := TypingDecl.
  #[export] Instance ConvType_Decl : ConvType de := ConvTypeDecl.
  #[export] Instance ConvTerm_Decl : ConvTerm de := ConvTermDecl.
  #[export] Instance ConvNeuConv_Decl : ConvNeuConv de := ConvTermDecl.
  #[export] Instance RedType_Decl : RedType de := TypeRedClosure.
  #[export] Instance OneStepRedTerm_Decl : OneStepRedTerm de := OneRedTermDecl.
  #[export] Instance RedTerm_Decl : RedTerm de := TermRedClosure.

  Ltac fold_decl :=
    change WfContextDecl with (wf_context (ta := de)) in * ;
    change WfTypeDecl with (wf_type (ta := de)) in *;
    change TypingDecl with (typing (ta := de)) in * ;
    change ConvTypeDecl with (conv_type (ta := de)) in * ;
    change ConvTermDecl with (conv_term (ta := de)) in * ;
    change TypeRedClosure with (red_ty (ta := de)) in *;
    change TermRedClosure with (red_tm (ta := de)) in *.

  Smpl Add fold_decl : refold.

End DeclarativeTypingData.

(** ** Induction principles *)

(** We use Scheme to generate mutual induction principle. Sadly, Scheme uses
the product of the standard library, which is not universe polymorphic, which
causes universe issues, typically in the fundamental lemma. So
we use some Ltac code to generate properly polymorphic versions of the inductive
principle. We also use Ltac to generate the conclusion of the mutual induction
proof, to alleviate the user from the need to write it down every time: they
only need write the predicates to be proven. *)
Section InductionPrinciples.
  Import DeclarativeTypingData.

Scheme 
    Minimality for WfContextDecl Sort Type with
    Minimality for WfTypeDecl   Sort Type with
    Minimality for TypingDecl    Sort Type with
    Minimality for ConvTypeDecl  Sort Type with
    Minimality for ConvTermDecl  Sort Type.

Combined Scheme _WfDeclInduction from
    WfContextDecl_rect_nodep,
    WfTypeDecl_rect_nodep,
    TypingDecl_rect_nodep,
    ConvTypeDecl_rect_nodep,
    ConvTermDecl_rect_nodep.

Let _WfDeclInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _WfDeclInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let WfDeclInductionType :=
  ltac: (let ind := eval cbv delta [_WfDeclInductionType] zeta
    in _WfDeclInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma WfDeclInduction : WfDeclInductionType.
Proof.
  intros PCon PTy PTm PTyEq PTmEq **.
  pose proof (_WfDeclInduction PCon PTy PTm PTyEq PTmEq) as H.
  destruct H as [?[?[? []]]].
  all: try (assumption ; fail).
  repeat (split;[assumption|]); assumption.
Qed.

Definition WfDeclInductionConcl :=
  ltac:(
    let t := eval cbv delta [WfDeclInductionType] beta in WfDeclInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq : rename.

(** Typed reduction implies untyped reduction *)
Section TypeErasure.
  Import DeclarativeTypingData.

Lemma oreddecl_ored Γ t u K :
  [Γ |- t ⇒ u ∈ K] ->
  [t ⇒ u].
Proof.
  induction 1; tea; now econstructor.
Qed.

Lemma oredtmdecl_ored Γ t u A : 
  [Γ |- t ⇒ u : A] ->
  [t ⇒ u].
Proof.
apply oreddecl_ored.
Qed.

Lemma reddecl_red Γ t u A :
  [Γ |- t ⇒* u ∈ A] ->
  [t ⇒* u].
Proof.
  induction 1.
  - now econstructor.
  - econstructor; [now eapply oreddecl_ored|reflexivity].
  - now etransitivity.
Qed.

Lemma redtmdecl_red Γ t u A : 
  [Γ |- t ⇒* u : A] ->
  [t ⇒* u].
Proof.
apply reddecl_red.
Qed.

Lemma oredtydecl_ored Γ A B : 
  [Γ |- A ⇒ B] ->
  [A ⇒ B].
Proof.
apply oreddecl_ored.
Qed.

Lemma redtydecl_red Γ A B : 
  [Γ |- A ⇒* B] ->
  [A ⇒* B].
Proof.
apply reddecl_red.
Qed.

End TypeErasure.
