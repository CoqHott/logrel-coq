From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening.

Set Primitive Projections.

Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition here before declaring the right
  instance *)
  Close Scope typing_scope.

  Inductive WfContextDecl : context -> Type :=
      | connil : [ |- ε ]
      | concons {Γ na A} : 
          [ |- Γ ] -> 
          [ Γ |- A ] -> 
          [ |-  Γ ,, vass na A]
  
  with WfTypeDecl  : context -> term -> Type :=
      | wfTypeU {Γ} : 
          [ |- Γ ] -> 
          [ Γ |- U ] 
      | wfTypeProd {Γ} {na : aname} {A B} : 
          [ Γ |- A ] -> 
          [Γ ,, (vass na A) |- B ] -> 
          [ Γ |- tProd na A B ]
      | wfTypeUniv {Γ} {A} :
          [ Γ |- A : U ] -> 
          [ Γ |- A ]

  with TypingDecl : context -> term -> term -> Type :=
      | wfVar {Γ} {n decl} :
          [   |- Γ ] ->
          in_ctx Γ n decl ->
          [ Γ |- tRel n : decl.(decl_type) ]
      | wfTermProd {Γ} {na} {A B} :
          [ Γ |- A : U] -> 
          [Γ ,, (vass na A) |- B : U ] ->
          [ Γ |- tProd na A B : U ]
      | wfTermLam {Γ} {na} {A B t} :
          [ Γ |- A ] ->        
          [ Γ ,, vass na A |- t : B ] -> 
          [ Γ |- tLambda na A t : tProd na A B]
      | wfTermApp {Γ} {na} {f a A B} :
          [ Γ |- f : tProd na A B ] -> 
          [ Γ |- a : A ] -> 
          [ Γ |- tApp f a : B[a..] ]
      | wfTermConv {Γ} {t A B} :
          [ Γ |- t : A ] -> 
          [ Γ |- A ≅ B ] -> 
          [ Γ |- t : B ]
      
  with ConvTypeDecl : context -> term -> term  -> Type :=  
      | TypePiCong {Γ} {na nb} {A B C D} :
          [ Γ |- A] ->
          [ Γ |- A ≅ B] ->
          [ Γ ,, vass na A |- C ≅ D] ->
          [ Γ |- tProd na A C ≅ tProd nb B D]
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

  with ConvTermDecl : context -> term -> term -> term -> Type :=
      | TermBRed {Γ} {na} {a t A B} :
              [ Γ |- A ] ->
              [ Γ ,, vass na A |- t : B ] ->
              [ Γ |- a : A ] ->
              [ Γ |- tApp (tLambda na A t) a ≅ t[a..] : B[a..] ]
      | TermPiCong {Γ} {na nb } {A B C D} :
          [ Γ |- A : U] ->
          [ Γ |- A ≅ B : U ] ->
          [ Γ ,, vass na A |- C ≅ D : U ] ->
          [ Γ |- tProd na A C ≅ tProd nb B D : U ]
      | TermAppCong {Γ} {na} {a b f g A B} :
          [ Γ |- f ≅ g : tProd na A B ] ->
          [ Γ |- a ≅ b : A ] ->
          [ Γ |- tApp f a ≅ tApp g b : B[a..] ]
      | TermFunExt {Γ} {na nb} {f g A B} :
          [ Γ |- A ] ->
          [ Γ |- f : tProd na A B ] ->
          [ Γ |- g : tProd nb A B ] ->
          [ Γ ,, vass na A |- eta_expand f ≅ eta_expand g : B ] ->
          [ Γ |- f ≅ g : tProd na A B ]
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

  Inductive OneRedTermDecl (Γ : context) : term -> term -> term -> Type :=
  | BRed {na} {A B a t} :
      [ Γ |- A ] -> 
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp (tLambda na A t) a ⇒ t[a..] : B[a..] ]
  | appSubst {na A B t u a} :
      [ Γ |- t ⇒ u : tProd na A B] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp t a ⇒ tApp u a : B[a..] ]
  | termRedConv {A B t u} : 
      [ Γ |- t ⇒ u : A ] ->
      [ Γ |- A ≅ B ] ->
      [ Γ |- t ⇒ u : B ]

  where "[ Γ |- t ⇒ u : A ]" := (OneRedTermDecl Γ A t u).

  Inductive OneRedTypeDecl (Γ : context) : term -> term -> Type :=
  | typeRedUniv {A B} :
      [ Γ |- A ⇒ B : U ] ->
      [ Γ |- A ⇒ B ]

  where "[ Γ |- A ⇒ B ]" := (OneRedTypeDecl Γ A B).

  Inductive TermRedClosure (Γ : context) : term -> term -> term -> Type :=
      | term_red_id {t A} :
        [ Γ |- t : A ] ->
        [ Γ |- t ⇒* t : A ]
      | term_red_red {A t t'} :
        [ Γ |- t ⇒ t' : A] ->
        [Γ |- t ⇒* t' : A]
      | term_red_trans {A t t' u} :
        [ Γ |- t ⇒* t' : A ] ->
        [ Γ |- t' ⇒* u : A ] ->
        [ Γ |- t ⇒* u : A ]
  where "[ Γ |- t ⇒* t' : A ]" := (TermRedClosure Γ A t t').

  Inductive TypeRedClosure (Γ : context) : term -> term -> Type :=
  | type_red_id {A} :
    [ Γ |- A ] ->
    [ Γ |- A ⇒* A]
  | type_red_red {A B} :
    [Γ |- A ⇒ B] ->
    [Γ |- A ⇒* B]
  | type_red_succ {A A' B} :
    [ Γ |- A ⇒* A' ] ->
    [ Γ |- A' ⇒* B ] ->
    [ Γ |- A ⇒* B ]

  where "[ Γ |- A ⇒* B ]" := (TypeRedClosure Γ A B).

End Definitions.


Notation "[ Γ |- t ⇒ u : A ]" := (OneRedTermDecl Γ A t u) : declarative_scope.
Notation "[ Γ |- A ⇒ B ]" := (OneRedTypeDecl Γ A B).

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

(* Type erasure *)
Section TypeErasure.
  Import DeclarativeTypingData.


Lemma oredtmdecl_ored Γ t u A : 
  [Γ |- t ⇒ u : A] ->
  [t ⇒ u].
Proof.
  induction 1.
  1-2: now econstructor.
  eassumption.
Qed.

Lemma redtmdecl_red Γ t u A : 
  [Γ |- t ⇒* u : A] ->
  [t ⇒* u].
Proof.
  induction 1.
  - now econstructor.
  - econstructor ; eauto using oredtmdecl_ored.
    reflexivity.
  - now etransitivity.
Qed.

Lemma oredtydecl_ored Γ A B : 
  [Γ |- A ⇒ B] ->
  [A ⇒ B].
Proof.
  induction 1.
  now eapply oredtmdecl_ored.
Qed.

Lemma redtydecl_red Γ A B : 
  [Γ |- A ⇒* B] ->
  [A ⇒* B].
Proof.
  induction 1.
  - now econstructor.
  - econstructor ; eauto using oredtydecl_ored.
    reflexivity.
  - now etransitivity.
Qed.

End TypeErasure.
 