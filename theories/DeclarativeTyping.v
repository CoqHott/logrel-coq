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
          [Γ ,, A |- B ] -> 
          [ Γ |- tProd A B ]
      | wfTypeNat {Γ} : 
          [|- Γ] ->
          [Γ |- tNat]
      | wfTypeEmpty {Γ} : 
          [|- Γ] ->
          [Γ |- tEmpty]
      | wfTypeSig {Γ} {A B} : 
          [ Γ |- A ] -> 
          [Γ ,, A |- B ] -> 
          [ Γ |- tSig A B ]
      | wfTypeList {Γ} {A} :
          [ Γ |- A ] ->
          [ Γ |- tList A ]
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
          [Γ ,, A |- B : U ] ->
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
      | wfTermSig {Γ} {A B} :
        [ Γ |- A : U] -> 
        [Γ ,, A |- B : U ] ->
        [ Γ |- tSig A B : U ]
      | wfTermPair {Γ} {A B a b} :
        [Γ |- A] ->
        [Γ,, A |- B] ->
        [Γ |- a : A] -> 
        [Γ |- b : B[a..]] ->
        [Γ |- tPair A B a b : tSig A B]
      | wfTermFst {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tFst p : A]
      | wfTermSnd {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tSnd p : B[(tFst p)..]]
      | wfTermList {Γ} {A} :
          [ Γ |- A : U] ->
          [ Γ |- tList A : U ]
      | wfTermNil {Γ} {A} :
          [ Γ |- A ] ->
          [ Γ |- tNil A : tList A ]
      | wfTermCons {Γ} {A a l} :
          [ Γ |- A ] ->
          [ Γ |- a : A ] ->
          [ Γ |- l : tList A ] ->
          [ Γ |- tCons A a l : tList A ]
      | wfTermMap {Γ} {A B f l} :
          [ Γ |- A ] ->
          [ Γ |- B ] ->
          [ Γ |- f : arr A B ] ->
          [ Γ |- l : tList A ] ->
          [ Γ |- tMap A B f l : tList B ]
      | wfTermListElim {Γ A P hnil hcons l} :
        [Γ |- A] ->
        [Γ ,, tList A |- P] ->
        [Γ |- hnil : P[(tNil A)..]] ->
        [Γ |- hcons : elimConsHypTy A P] ->
        [Γ |- l : tList A] ->
        [Γ |- tListElim A P hnil hcons l : P[l..]]
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
      | TypeSigCong {Γ} {A B C D} :
          [ Γ |- A] ->
          [ Γ |- A ≅ B] ->
          [ Γ ,, A |- C ≅ D] ->
          [ Γ |- tSig A C ≅ tSig B D]
      | TypeListCong {Γ} {A B} :
          [ Γ |- A ≅ B] ->
          [ Γ |- tList A ≅ tList B ]
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
      | TermSigCong {Γ} {A A' B B'} :
          [ Γ |- A : U] ->
          [ Γ |- A ≅ A' : U ] ->
          [ Γ ,, A |- B ≅ B' : U ] ->
          [ Γ |- tSig A B ≅ tSig A' B' : U ]
      | TermPairEta {Γ} {A B p q} :
          [Γ |- A] ->
          [Γ ,, A |- B] ->
          [Γ |- p : tSig A B] ->
          [Γ |- q : tSig A B] ->
          [Γ |- tFst p ≅ tFst q : A] ->
          [Γ |- tSnd p ≅ tSnd q : B[(tFst p)..]] ->
          [Γ |- p ≅ q : tSig A B]
      | TermFstCong {Γ A B p p'} :
        [Γ |- p ≅ p' : tSig A B] ->
        [Γ |- tFst p ≅ tFst p' : A]
      | TermFstBeta {Γ A B a b} :
        [Γ |- A] ->
        [Γ ,, A |- B] ->
        [Γ |- a : A] ->
        [Γ |- b : B[a..]] ->
        [Γ |- tFst (tPair A B a b) ≅ a : A]
      | TermSndCong {Γ A B p p'} :
        [Γ |- p ≅ p' : tSig A B] ->
        [Γ |- tSnd p ≅ tSnd p' : B[(tFst p)..]]
      | TermSndBeta {Γ A B a b} :
        [Γ |- A] ->
        [Γ ,, A |- B] ->
        [Γ |- a : A] ->
        [Γ |- b : B[a..]] ->
        [Γ |- tSnd (tPair A B a b) ≅ b : B[(tFst (tPair A B a b))..]]
      | TermListCong {Γ} {A B} :
          [ Γ |- A ≅ B : U ] ->
          [ Γ |- tList A ≅ tList B : U ]
      | TermNilCong {Γ} {A B } :
          [ Γ |- A ≅ B ] ->
          [ Γ |- tNil A ≅ tNil B : tList A ]
      | TermConsCong {Γ} {a b ax bx A B } :
          [ Γ |- A ≅ B ] ->
          [ Γ |- a ≅ b : A ] ->
          [ Γ |- ax ≅ bx : tList A ] ->
          [ Γ |- tCons A a ax ≅ tCons B b bx : tList A ]
      | TermMapCong {Γ} {f g ax bx A B C D} :
          [ Γ |- A ≅ B ] ->
          [ Γ |- C ≅ D ] ->
          [ Γ |- f ≅ g : arr A C ] ->
          [ Γ |- ax ≅ bx : tList A ] ->
          [ Γ |- tMap A C f ax ≅ tMap B D g bx : tList C ]
      | TermRedMapNil {Γ} {f A B} :
          [ Γ |- A ] ->
          [ Γ |- B ] ->
          [ Γ |- f : arr A B ] ->
          [ Γ |- tMap A B f (tNil A) ≅ (tNil B) : tList B ]
      | TermRedMapCons {Γ} {f hd tl A B} :
          [ Γ |- A ] ->
          [ Γ |- B ] ->
          [ Γ |- f : arr A B ] ->
          [ Γ |- hd : A ] ->
          [ Γ |- tl : tList A ] ->
          [ Γ |- tMap A B f (tCons A hd tl) ≅ tCons B (tApp f hd) (tMap A B f tl) : tList B ]
      | TermRedMapComp {Γ} {f g l l' A B C} :
          [ Γ |- A] ->
          [ Γ |- B] ->
          [ Γ |- C] ->
          [ Γ |- f : arr B C ] ->
          [ Γ |- g : arr A B ] ->
          [ Γ |- l ≅ l' : tList A ] ->
          [ Γ |- tMap B C f (tMap A B g l) ≅ tMap A C (comp A f g) l' : tList C ]
      | TermRedMapId {Γ} {l l' A} :
          [ Γ |- A ≅ A ] ->
          [ Γ |- l ≅ l' : tList A ] ->
          [ Γ |- tMap A A (idterm A) l ≅ l' : tList A ]
      | TermRedListElimCong {Γ A A' P P' hnil hnil' hcons hcons' l l'} :
        [Γ |- A] ->
        [Γ |- A ≅ A'] ->
        [Γ,, tList A |- P ≅ P'] ->
        [Γ |- hnil ≅ hnil' : P[(tNil A)..]] ->
        [Γ |- hcons ≅ hcons' : elimConsHypTy A P] ->
        [Γ |- l ≅ l' : tList A] ->
        [Γ |- tListElim A P hnil hcons l ≅ tListElim A' P' hnil' hcons' l' : P[l..]]
      | TermRedListElimNil {Γ A P hnil hcons A'} :
        [Γ |- A] ->
        [Γ,, tList A |- P] ->
        [Γ |- hnil : P[(tNil A)..]] ->
        [Γ |- hcons : elimConsHypTy A P] ->
        (* [Γ |- A'] -> *)
        [Γ |- A ≅ A'] ->
        [Γ |- tListElim A P hnil hcons (tNil A') ≅ hnil : P[(tNil A')..]]
      | TermRedListElimCons {Γ A P hnil hcons A' hd tl} :
        [Γ |- A] ->
        [Γ,, tList A |- P] ->
        [Γ |- hnil : P[(tNil A)..]] ->
        [Γ |- hcons : elimConsHypTy A P] ->
        [Γ |- A ≅ A'] ->
        [Γ |- hd : A'] ->
        [Γ |- tl : tList A'] ->
        [Γ |- tListElim A P hnil hcons (tCons A' hd tl) ≅ tApp (tApp (tApp hcons hd) tl) (tListElim A P hnil hcons tl) : P[(tCons A' hd tl)..]]
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

  Record RedClosureDecl (Γ : context) (A : class) (t u : term) := {
    reddecl_typ : match A with istype => [Γ |- t] | isterm A => [Γ |- t : A] end;
    reddecl_red : RedClosureAlg t u;
    reddecl_conv : match A with istype => [ Γ |- t ≅ u ] | isterm A => [Γ |- t ≅ u : A] end;
  }.

  Notation "[ Γ |- t ⇒* t' ∈ A ]" := (RedClosureDecl Γ A t t').

  Record ConvNeuConvDecl (Γ : context) (A : term) (t u : term) := {
    convnedecl_whne_l : whne t;
    convnedecl_whne_r : whne u;
    convnedecl_conv : [ Γ |- t ≅ u : A ];
  }.

  Record ConvNeuConvListDecl (Γ : context) (A : term) (t u : term) := {
    convnelistdecl_whne_l : whne_list t;
    convnelistdecl_whne_r : whne_list u;
    convnelistdecl_conv : [ Γ |- t ≅ u : tList A ];
  }.

End Definitions.

Definition TermRedClosure Γ A t u := RedClosureDecl Γ (isterm A) t u.
Definition TypeRedClosure Γ A B := RedClosureDecl Γ istype A B.

Notation "[ Γ |- t ⇒* u ∈ A ]" := (RedClosureDecl Γ A t u).

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
  #[export] Instance ConvNeuConv_Decl : ConvNeuConv de := ConvNeuConvDecl.
  #[export] Instance ConvNeuConvList_Decl : ConvNeuList de := ConvNeuConvListDecl.
  #[export] Instance RedType_Decl : RedType de := TypeRedClosure.
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

Lemma redtmdecl_red Γ t u A : 
  [Γ |- t ⇒* u : A] ->
  [t ⇒* u].
Proof.
apply reddecl_red.
Qed.

Lemma redtydecl_red Γ A B : 
  [Γ |- A ⇒* B] ->
  [A ⇒* B].
Proof.
apply reddecl_red.
Qed.

End TypeErasure.
