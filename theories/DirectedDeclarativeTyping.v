(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations DirectedDirections Context DirectedContext NormalForms Weakening UntypedReduction.

Set Primitive Projections.


Reserved Notation "[ |-( ) Γ ]" (at level 0, Γ at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ]" (at level 0, Γ, d, A at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t : A @( dA ) ]" (at level 0, Γ, dt, t, A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅ t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ⤳* u ∈ A @( dA ) ]" (at level 0, Γ, dt, t, u, A, dA at level 50).

Fixpoint is_kind (t: term) : Type :=
  match t with
  | tSort _ => unit
  | tProd _ t => is_kind t
  | _ => False
  end.

(** Definitions in this file should be understood as the _specification_ of conversion
or typing, done in a declarative fashion. For instance, we _demand_ that conversion
be transitive by adding a corresponding rule. *)

(* We locally disable typing notations to be able to use them in the definition
here before declaring the instance to which abstract notations are bound. *)
Close Scope typing_scope.


  (** Typing and conversion are mutually defined inductive relations. To avoid having
  to bother with elimination of propositions, we put them in the Type sort. *)

(** **** Context well-formation *)
Inductive WfContextDecl : context -> Type :=
    | connil : [ |-( ) εᵈ ]
    | conconsDiscr {Γ dA A} :
        [ |-( ) Γ ] ->
        [ Γ |-( dA ) A ] ->
        [ |-( )  Γ ,, Discr \ A @ dA ]
    | conconsFun {Γ dA A} :
        [ |-( ) Γ ] ->
        [ Γ |-( dA ) A ] ->
        is_kind A ->
        [ |-( )  Γ ,, Fun \ A @ dA ]
    | conconsCofun {Γ dA A} :
        [ |-( ) Γ ] ->
        [ Γ |-( dA ) A ] ->
        is_kind A ->
        [ |-( )  Γ ,, Cofun \ A @ dA ]

(** **** Type well-formation *)
with WfTypeDecl  : context -> direction -> term -> Type :=
    | wfTypeU {Γ d} :
        [ |-( ) Γ ] ->
        [ Γ |-( d ) U ]
    | wfTypeProd {Γ d} {A B} :
        [ Γ |-( dir_op d ) A ] ->
        [Γ ,, Discr \ A @ dir_op d |-( d ) B ] ->
        [ Γ |-( d ) tProd A B ]
    | wfTypeUniv {Γ d} {A} :
        [ Γ |-( d ) A : U @( Discr ) ] ->
        [ Γ |-( d ) A ]
(** **** Typing *)
with TypingDecl : context -> direction -> term -> direction -> term -> Type :=
    | wfVar {Γ d'} {n d T dT} :
        [   |-( ) Γ ] ->
        in_ctx Γ n (d \ T @ dT) ->
        dir_leq d d' ->
        [ Γ |-( d' ) tRel n : T @( dT ) ]
    | wfTermProd {Γ d} {A B} :
        [ Γ |-( dir_op d ) A : U @( Discr ) ] ->
        [Γ ,, Discr \ A @ dir_op d |-( d ) B : U @( Discr ) ] ->
        [ Γ |-( d ) tProd A B : U @( Discr ) ]
    | wfTermLam {Γ d} {dT A B t} :
        [ Γ |-( dir_op dT ) A ] ->
        [ Γ ,, Discr \ A @ dT |-( d ) t : B @( dT ) ] ->
        [ Γ |-( d ) tLambda A t : tProd A B @( dT ) ]
    | wfTermApp {Γ d} {dT f a A B} :
        [ Γ |-( d ) f : tProd A B @( dT ) ] ->
        [ Γ |-( Discr ) a : A @( dir_op dT ) ] ->
        [ Γ |-( d ) tApp f a : B[a..] @( dT ) ]
    | wfTermConv {Γ d} {t dA A B} :
        [ Γ |-( d ) t : A @( dA ) ] ->
        [ Γ |-( dA ) A ≅ B ] ->
        [ Γ |-( d ) t : B @( dA ) ]
(** **** Conversion of types *)
with ConvTypeDecl : context -> direction -> term -> term  -> Type :=
    | TypePiCong {Γ d} {A B C D} :
        [ Γ |-( dir_op d ) A] ->
        [ Γ |-( dir_op d ) A ≅ B] ->
        [ Γ ,, Discr \ A @ dir_op d |-( d ) C ≅ D] ->
        [ Γ |-( d ) tProd A C ≅ tProd B D]
    | TypeRefl {Γ d} {A} :
        [ Γ |-( d ) A ] ->
        [ Γ |-( d ) A ≅ A]
    | convUniv {Γ d} {A B} :
      [ Γ |-( d ) A ≅ B : U @( Discr ) ] ->
      [ Γ |-( d ) A ≅ B ]
    | TypeSym {Γ d} {A B} :
        [ Γ |-( d ) A ≅ B ] ->
        [ Γ |-( d ) B ≅ A ]
    | TypeTrans {Γ d} {A B C} :
        [ Γ |-( d ) A ≅ B] ->
        [ Γ |-( d ) B ≅ C] ->
        [ Γ |-( d ) A ≅ C]
(** **** Conversion of terms *)
with ConvTermDecl : context -> direction -> term -> direction -> term -> term -> Type :=
(*     | TermBRed {Γ} {a t A B} : *)
(*             [ Γ |- A ] -> *)
(*             [ Γ ,, A |- t : B ] -> *)
(*             [ Γ |- a : A ] -> *)
(*             [ Γ |- tApp (tLambda A t) a ≅ t[a..] : B[a..] ] *)
(*     | TermPiCong {Γ} {A B C D} : *)
(*         [ Γ |- A : U] -> *)
(*         [ Γ |- A ≅ B : U ] -> *)
(*         [ Γ ,, A |- C ≅ D : U ] -> *)
(*         [ Γ |- tProd A C ≅ tProd B D : U ] *)
(*     | TermAppCong {Γ} {a b f g A B} : *)
(*         [ Γ |- f ≅ g : tProd A B ] -> *)
(*         [ Γ |- a ≅ b : A ] -> *)
(*         [ Γ |- tApp f a ≅ tApp g b : B[a..] ] *)
(*     | TermFunExt {Γ} {f g A B} : *)
(*         [ Γ |- A ] -> *)
(*         [ Γ |- f : tProd A B ] -> *)
(*         [ Γ |- g : tProd A B ] -> *)
(*         [ Γ ,, A |- eta_expand f ≅ eta_expand g : B ] -> *)
(*         [ Γ |- f ≅ g : tProd A B ] *)
    | TermRefl {Γ d} {dA t A} :
        [ Γ |-( d ) t : A @( dA ) ] ->
        [ Γ |-( d ) t ≅ t : A @( dA ) ]
    | TermConv {Γ d} {t t' dA A B} :
        [ Γ |-( d ) t ≅ t': A @( dA ) ] ->
        [ Γ |-( dA ) A ≅ B ] ->
        [ Γ |-( d ) t ≅ t': B @( dA ) ]
    | TermSym {Γ d} {dA t t' A} :
        [ Γ |-( d ) t ≅ t' : A @( dA ) ] ->
        [ Γ |-( d ) t' ≅ t : A @( dA ) ]
    | TermTrans {Γ d} {dA t t' t'' A} :
        [ Γ |-( d ) t ≅ t' : A @( dA ) ] ->
        [ Γ |-( d ) t' ≅ t'' : A @( dA ) ] ->
        [ Γ |-( d ) t ≅ t'' : A @( dA ) ]

where "[   |-( ) Γ ]" := (WfContextDecl Γ)
and   "[ Γ |-( d ) T ]" := (WfTypeDecl Γ d T)
and   "[ Γ |-( dt ) t : T @( dT ) ]" := (TypingDecl Γ dt T dT t)
and   "[ Γ |-( d ) A ≅ B ]" := (ConvTypeDecl Γ d A B)
and   "[ Γ |-( dt ) t ≅ t' : T @( dT ) ]" := (ConvTermDecl Γ dt T dT t t').

#[local]
Example var_fun : [ εᵈ ,, Discr \ U @ Discr |-( Fun ) tRel 0 ].
Proof.
  constructor.
  econstructor.
  - repeat constructor.
  - constructor.
  - constructor.
Qed.


(** ** Induction principles *)

(** We use Scheme to generate mutual induction principle. Sadly, Scheme uses
the product of the standard library, which is not universe polymorphic, which
causes universe issues, typically in the fundamental lemma. So
we use some Ltac code to generate properly polymorphic versions of the inductive
principle. We also use Ltac to generate the conclusion of the mutual induction
proof, to alleviate the user from the need to write it down every time: they
only need write the predicates to be proven. *)
Section InductionPrinciples.

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
