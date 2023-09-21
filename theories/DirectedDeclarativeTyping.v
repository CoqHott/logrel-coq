(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations DirectedDirections DirectedContext NormalForms Weakening UntypedReduction.

Set Primitive Projections.


Reserved Notation "[ Γ |-( d ) A ]" (at level 0, Γ, d, A at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) t : A ]" (at level 0, Γ, d, t, A at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) t ≅ t' : A ]" (at level 0, Γ, d, t, t', A at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) t ⤳* u ∈ A ]" (at level 0, Γ, d, t, u, A at level 50).

Fixpoint is_kind (t: term) : Type :=
  match t with
  | tSort _ => unit
  | tProd _ t => is_kind t
  | _ => False
  end.

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
      | conconsDiscr {Γ dA A} :
          [ |- Γ ] ->
          [ Γ |-( dA ) A ] ->
          [ |-  Γ ,, (Discr, A) ]
      | conconsFun {Γ dA A} :
          [ |- Γ ] ->
          [ Γ |-( dA ) A ] ->
          is_kind A ->
          [ |-  Γ ,, (Fun, A) ]
      | conconsCofun {Γ dA A} :
          [ |- Γ ] ->
          [ Γ |-( dA ) A ] ->
          is_kind A ->
          [ |-  Γ ,, (Cofun, A) ]

  (** **** Type well-formation *)
  with WfTypeDecl  : context -> direction -> term -> Type :=
      | wfTypeU {Γ d} :
          [ |- Γ ] ->
          [ Γ |-( d ) U ]
      | wfTypeProd {Γ d} {A B} :
          [ Γ |-( dir_op d ) A ] ->
          [Γ ,, (Discr, A) |-( d ) B ] ->
          [ Γ |-( d ) tProd A B ]
      (* | wfTypeNat {Γ} : *)
      (*     [|- Γ] -> *)
      (*     [Γ |- tNat] *)
      (* | wfTypeEmpty {Γ} : *)
      (*     [|- Γ] -> *)
      (*     [Γ |- tEmpty] *)
      (* | wfTypeSig {Γ} {A B} : *)
      (*     [ Γ |- A ] -> *)
      (*     [Γ ,, A |- B ] -> *)
      (*     [ Γ |- tSig A B ] *)
      (* | wftTypeId {Γ} {A x y} : *)
      (*     [Γ |- A] -> *)
      (*     [Γ |- x : A] -> *)
      (*     [Γ |- y : A] -> *)
      (*     [Γ |- tId A x y] *)
      | wfTypeUniv {Γ d} {A} :
          [ Γ |-( d ) A : U ] ->
          [ Γ |-( d ) A ]
  (** **** Typing *)
  with TypingDecl : context -> direction -> term -> term -> Type :=
      | wfVar {Γ d} {n dT T} :
          [   |- Γ ] ->
          in_ctx Γ n (dT, T) ->
          dir_leq dT d ->
          [ Γ |-( d ) tRel n : T ]
      | wfTermProd {Γ d} {A B} :
          [ Γ |-( dir_op d ) A : U] ->
          [Γ ,, (Discr, A) |-( d ) B : U ] ->
          [ Γ |-( d ) tProd A B : U ]
      | wfTermLam {Γ d} {dA A B t} :
          [ Γ |-( dA ) A ] ->
          [ Γ ,, (Discr, A) |-( d ) t : B ] ->
          [ Γ |-( d ) tLambda A t : tProd A B]
      | wfTermApp {Γ d} {f a A B} :
          [ Γ |-( d ) f : tProd A B ] ->
          [ Γ |-( Discr ) a : A ] ->
          [ Γ |-( d ) tApp f a : B[a..] ]
  (*     | wfTermNat {Γ} : *)
  (*         [|-Γ] -> *)
  (*         [Γ |- tNat : U] *)
  (*     | wfTermZero {Γ} : *)
  (*         [|-Γ] -> *)
  (*         [Γ |- tZero : tNat] *)
  (*     | wfTermSucc {Γ n} : *)
  (*         [Γ |- n : tNat] -> *)
  (*         [Γ |- tSucc n : tNat] *)
  (*     | wfTermNatElim {Γ P hz hs n} : *)
  (*       [Γ ,, tNat |- P ] -> *)
  (*       [Γ |- hz : P[tZero..]] -> *)
  (*       [Γ |- hs : elimSuccHypTy P] -> *)
  (*       [Γ |- n : tNat] -> *)
  (*       [Γ |- tNatElim P hz hs n : P[n..]] *)
  (*     | wfTermEmpty {Γ} : *)
  (*         [|-Γ] -> *)
  (*         [Γ |- tEmpty : U] *)
  (*     | wfTermEmptyElim {Γ P e} : *)
  (*       [Γ ,, tEmpty |- P ] -> *)
  (*       [Γ |- e : tEmpty] -> *)
  (*       [Γ |- tEmptyElim P e : P[e..]] *)
  (*     | wfTermSig {Γ} {A B} : *)
  (*       [ Γ |- A : U] -> *)
  (*       [Γ ,, A |- B : U ] -> *)
  (*       [ Γ |- tSig A B : U ] *)
  (*     | wfTermPair {Γ} {A B a b} : *)
  (*       [Γ |- A] -> *)
  (*       [Γ,, A |- B] -> *)
  (*       [Γ |- a : A] -> *)
  (*       [Γ |- b : B[a..]] -> *)
  (*       [Γ |- tPair A B a b : tSig A B] *)
  (*     | wfTermFst {Γ A B p} : *)
  (*       [Γ |- p : tSig A B] -> *)
  (*       [Γ |- tFst p : A] *)
  (*     | wfTermSnd {Γ A B p} : *)
  (*       [Γ |- p : tSig A B] -> *)
  (*       [Γ |- tSnd p : B[(tFst p)..]] *)
  (*     | wfTermId {Γ} {A x y} : *)
  (*         [Γ |- A : U] -> *)
  (*         [Γ |- x : A] -> *)
  (*         [Γ |- y : A] -> *)
  (*         [Γ |- tId A x y : U] *)
  (*     | wfTermRefl {Γ A x} : *)
  (*         [Γ |- A] -> *)
  (*         [Γ |- x : A] -> *)
  (*         [Γ |- tRefl A x : tId A x x] *)
  (*     | wfTermIdElim {Γ A x P hr y e} : *)
  (*         [Γ |- A] -> *)
  (*         [Γ |- x : A] -> *)
  (*         [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] -> *)
  (*         [Γ |- hr : P[tRefl A x .: x..]] -> *)
  (*         [Γ |- y : A] -> *)
  (*         [Γ |- e : tId A x y] -> *)
  (*         [Γ |- tIdElim A x P hr y e : P[e .: y..]] *)
      | wfTermConv {Γ d} {t dA A B} :
          [ Γ |-( d ) t : A ] ->
          [ Γ |-( dA ) A ≅ B ] ->
          [ Γ |-( d ) t : B ]
  (** **** Conversion of types *)
  with ConvTypeDecl : context -> direction -> term -> term  -> Type :=
      | TypePiCong {Γ d} {A B C D} :
          [ Γ |-( dir_op d ) A] ->
          [ Γ |-( dir_op d ) A ≅ B] ->
          [ Γ ,, (Discr, A) |-( d ) C ≅ D] ->
          [ Γ |-( d ) tProd A C ≅ tProd B D]
  (*     | TypeSigCong {Γ} {A B C D} : *)
  (*         [ Γ |- A] -> *)
  (*         [ Γ |- A ≅ B] -> *)
  (*         [ Γ ,, A |- C ≅ D] -> *)
  (*         [ Γ |- tSig A C ≅ tSig B D] *)
  (*     | TypeIdCong {Γ A A' x x' y y'} : *)
  (*         (* [Γ |- A] -> ?  *) *)
  (*         [Γ |- A ≅ A'] -> *)
  (*         [Γ |- x ≅ x' : A] -> *)
  (*         [Γ |- y ≅ y' : A] -> *)
  (*         [Γ |- tId A x y ≅ tId A' x' y' ] *)
      | TypeRefl {Γ d} {A} :
          [ Γ |-( d ) A ] ->
          [ Γ |-( d ) A ≅ A]
      | convUniv {Γ d} {A B} :
        [ Γ |-( d ) A ≅ B : U ] ->
        [ Γ |-( d ) A ≅ B ]
      | TypeSym {Γ d} {A B} :
          [ Γ |-( d ) A ≅ B ] ->
          [ Γ |-( d ) B ≅ A ]
      | TypeTrans {Γ d} {A B C} :
          [ Γ |-( d ) A ≅ B] ->
          [ Γ |-( d ) B ≅ C] ->
          [ Γ |-( d ) A ≅ C]
  (** **** Conversion of terms *)
  with ConvTermDecl : context -> direction -> term -> term -> term -> Type :=
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
  (*     | TermSuccCong {Γ} {n n'} : *)
  (*         [Γ |- n ≅ n' : tNat] -> *)
  (*         [Γ |- tSucc n ≅ tSucc n' : tNat] *)
  (*     | TermNatElimCong {Γ P P' hz hz' hs hs' n n'} : *)
  (*         [Γ ,, tNat |- P ≅ P'] -> *)
  (*         [Γ |- hz ≅ hz' : P[tZero..]] -> *)
  (*         [Γ |- hs ≅ hs' : elimSuccHypTy P] -> *)
  (*         [Γ |- n ≅ n' : tNat] -> *)
  (*         [Γ |- tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : P[n..]]         *)
  (*     | TermNatElimZero {Γ P hz hs} : *)
  (*         [Γ ,, tNat |- P ] -> *)
  (*         [Γ |- hz : P[tZero..]] -> *)
  (*         [Γ |- hs : elimSuccHypTy P] -> *)
  (*         [Γ |- tNatElim P hz hs tZero ≅ hz : P[tZero..]] *)
  (*     | TermNatElimSucc {Γ P hz hs n} : *)
  (*         [Γ ,, tNat |- P ] -> *)
  (*         [Γ |- hz : P[tZero..]] -> *)
  (*         [Γ |- hs : elimSuccHypTy P] -> *)
  (*         [Γ |- n : tNat] -> *)
  (*         [Γ |- tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]] *)
  (*     | TermEmptyElimCong {Γ P P' e e'} : *)
  (*         [Γ ,, tEmpty |- P ≅ P'] -> *)
  (*         [Γ |- e ≅ e' : tEmpty] -> *)
  (*         [Γ |- tEmptyElim P e ≅ tEmptyElim P' e' : P[e..]] *)
  (*     | TermSigCong {Γ} {A A' B B'} : *)
  (*         [ Γ |- A : U] -> *)
  (*         [ Γ |- A ≅ A' : U ] -> *)
  (*         [ Γ ,, A |- B ≅ B' : U ] -> *)
  (*         [ Γ |- tSig A B ≅ tSig A' B' : U ] *)
  (*     | TermPairEta {Γ} {A B p q} : *)
  (*         [Γ |- A] -> *)
  (*         [Γ ,, A |- B] -> *)
  (*         [Γ |- p : tSig A B] -> *)
  (*         [Γ |- q : tSig A B] -> *)
  (*         [Γ |- tFst p ≅ tFst q : A] -> *)
  (*         [Γ |- tSnd p ≅ tSnd q : B[(tFst p)..]] -> *)
  (*         [Γ |- p ≅ q : tSig A B] *)
  (*     | TermFstCong {Γ A B p p'} : *)
  (*       [Γ |- p ≅ p' : tSig A B] -> *)
  (*       [Γ |- tFst p ≅ tFst p' : A] *)
  (*     | TermFstBeta {Γ A B a b} : *)
  (*       [Γ |- A] -> *)
  (*       [Γ ,, A |- B] -> *)
  (*       [Γ |- a : A] -> *)
  (*       [Γ |- b : B[a..]] -> *)
  (*       [Γ |- tFst (tPair A B a b) ≅ a : A] *)
  (*     | TermSndCong {Γ A B p p'} : *)
  (*       [Γ |- p ≅ p' : tSig A B] -> *)
  (*       [Γ |- tSnd p ≅ tSnd p' : B[(tFst p)..]] *)
  (*     | TermSndBeta {Γ A B a b} : *)
  (*       [Γ |- A] -> *)
  (*       [Γ ,, A |- B] -> *)
  (*       [Γ |- a : A] -> *)
  (*       [Γ |- b : B[a..]] -> *)
  (*       [Γ |- tSnd (tPair A B a b) ≅ b : B[(tFst (tPair A B a b))..]] *)
  (*     | TermIdCong {Γ A A' x x' y y'} : *)
  (*       (* [Γ |- A] -> ?  *) *)
  (*       [Γ |- A ≅ A' : U] -> *)
  (*       [Γ |- x ≅ x' : A] -> *)
  (*       [Γ |- y ≅ y' : A] -> *)
  (*       [Γ |- tId A x y ≅ tId A' x' y' : U ] *)
  (*     | TermReflCong {Γ A A' x x'} : *)
  (*       [Γ |- A ≅ A'] -> *)
  (*       [Γ |- x ≅ x' : A] -> *)
  (*       [Γ |- tRefl A x ≅ tRefl A' x' : tId A x x] *)
  (*     | TermIdElim {Γ A A' x x' P P' hr hr' y y' e e'} : *)
  (*       (* Parameters well formed: required for stability by weakening, *)
  (*         in order to show that the context Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) *)
  (*         remains well-formed under weakenings *) *)
  (*       [Γ |- A] -> *)
  (*       [Γ |- x : A] -> *)
  (*       [Γ |- A ≅ A'] -> *)
  (*       [Γ |- x ≅ x' : A] -> *)
  (*       [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'] -> *)
  (*       [Γ |- hr ≅ hr' : P[tRefl A x .: x..]] -> *)
  (*       [Γ |- y ≅ y' : A] -> *)
  (*       [Γ |- e ≅ e' : tId A x y] -> *)
  (*       [Γ |- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : P[e .: y..]] *)
  (*     | TermIdElimRefl {Γ A x P hr y A' z} : *)
  (*       [Γ |- A] -> *)
  (*       [Γ |- x : A] -> *)
  (*       [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] -> *)
  (*       [Γ |- hr : P[tRefl A x .: x..]] -> *)
  (*       [Γ |- y : A] -> *)
  (*       [Γ |- A'] -> *)
  (*       [Γ |- z : A] -> *)
  (*       [Γ |- A ≅ A'] -> *)
  (*       [Γ |- x ≅ y : A] -> *)
  (*       [Γ |- x ≅ z : A] -> *)
  (*       [Γ |- tIdElim A x P hr y (tRefl A' z) ≅ hr : P[tRefl A' z .: y..]] *)
      | TermRefl {Γ d} {t A} :
          [ Γ |-( d ) t : A ] ->
          [ Γ |-( d ) t ≅ t : A ]
      | TermConv {Γ d} {t t' dA A B} :
          [ Γ |-( d ) t ≅ t': A ] ->
          [ Γ |-( dA ) A ≅ B ] ->
          [ Γ |-( d ) t ≅ t': B ]
      | TermSym {Γ d} {t t' A} :
          [ Γ |-( d ) t ≅ t' : A ] ->
          [ Γ |-( d ) t' ≅ t : A ]
      | TermTrans {Γ d} {t t' t'' A} :
          [ Γ |-( d ) t ≅ t' : A ] ->
          [ Γ |-( d ) t' ≅ t'' : A ] ->
          [ Γ |-( d ) t ≅ t'' : A ]

  where "[   |- Γ ]" := (WfContextDecl Γ)
  and   "[ Γ |-( d ) T ]" := (WfTypeDecl Γ d T)
  and   "[ Γ |-( d ) t : T ]" := (TypingDecl Γ d T t)
  and   "[ Γ |-( d ) A ≅ B ]" := (ConvTypeDecl Γ d A B)
  and   "[ Γ |-( d ) t ≅ t' : T ]" := (ConvTermDecl Γ d T t t').

  (** (Typed) reduction is defined afterwards,
  rather than mutually with the other relations. *)

  Local Coercion isterm : term >-> class.

  Record RedClosureDecl (Γ : context) (d: direction) (A : class) (t u : term) := {
    reddecl_typ : match A with istype => [Γ |-( d ) t] | isterm A => [Γ |-( d ) t : A] end;
    reddecl_red : RedClosureAlg t u;
    reddecl_conv : match A with istype => [ Γ |-( d ) t ≅ u ] | isterm A => [Γ |-( d ) t ≅ u : A] end;
  }.

  Notation "[ Γ |-( d ) t ⤳* t' ∈ A ]" := (RedClosureDecl Γ d A t t').

  Record ConvNeuConvDecl (Γ : context) (d: direction) (A : term) (t u : term) := {
    convnedecl_whne_l : whne t;
    convnedecl_whne_r : whne u;
    convnedecl_conv : [ Γ |-( d ) t ≅ u : A ];
  }.

End Definitions.

Definition TermRedClosure Γ d A t u := RedClosureDecl Γ d (isterm A) t u.
Definition TypeRedClosure Γ d A B := RedClosureDecl Γ d istype A B.

Notation "[ Γ |-( d ) t ⤳* u ∈ A ]" := (RedClosureDecl Γ A t u).

(** ** Instances *)
(** Used for printing (see Notations) and as a support for the generic typing
properties used for the logical relation (see GenericTyping). *)
Module DeclarativeTypingData.

  Definition de : tag.
  Proof.
  constructor.
  Qed.

  (* #[export] Instance WfContext_Decl : WfContext de := WfContextDecl. *)
  (* #[export] Instance WfType_Decl : WfType de := WfTypeDecl. *)
  (* #[export] Instance Typing_Decl : Inferring de := TypingDecl. *)
  (* #[export] Instance Inferring_Decl : Typing de := TypingDecl. *)
  (* #[export] Instance InferringRed_Decl : InferringRed de := TypingDecl. *)
  (* #[export] Instance ConvType_Decl : ConvType de := ConvTypeDecl. *)
  (* #[export] Instance ConvTerm_Decl : ConvTerm de := ConvTermDecl. *)
  (* #[export] Instance ConvNeuConv_Decl : ConvNeuConv de := ConvNeuConvDecl. *)
  (* #[export] Instance RedType_Decl : RedType de := TypeRedClosure. *)
  (* #[export] Instance RedTerm_Decl : RedTerm de := TermRedClosure. *)

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

(* Lemma redtmdecl_red Γ d t u A : *)
(*   [Γ |- t ⤳* u : A] -> *)
(*   [t ⤳* u]. *)
(* Proof. *)
(* apply reddecl_red. *)
(* Qed. *)

(* Lemma redtydecl_red Γ A B : *)
(*   [Γ |- A ⤳* B] -> *)
(*   [A ⤳* B]. *)
(* Proof. *)
(* apply reddecl_red. *)
(* Qed. *)

End TypeErasure.
