(** * LogRel.GenericTyping: the generic interface of typing used to build the logical relation. *)
From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening UntypedReduction.

(** In order to factor the work, the logical relation is defined over a generic
notion of typing (and conversion),
and its properties are established given abstract properties
of this generic notion. This way, we can instantiate the logical relation multiple
times with different instances of this abstract notion of typing, gathering more
and more properties. *)

(**
More precisely, an instance consists of giving notions of 
- context well-formation [|- Γ]
- type well-formation [Γ |- A]
- term well-formation [Γ |- t : A]
- convertibility of types [Γ |- A ≅ B]
- convertibility of terms [Γ |- t ≅ u : A]
- neutral convertibility of terms [Γ |- m ~ n : A]
- (multi-step, weak-head) reduction of types [Γ |- A ⤳* B]
- (multi-step, weak-head) reduction of terms [Γ |- t ⤳* u : A]
*)

(** ** Generic definitions *)

(** These can be defined over typing and conversion in a generic way. *)

Section RedDefinitions.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  (** *** Bundling of a predicate with side-conditions *)

  Record TypeRedWhnf (l : wfLCon) (Γ : context) (A B : term) : Type :=
    {
      tyred_whnf_red :> [ Γ |- A ⤳* B ]< l > ;
      tyred_whnf_whnf :> whnf B
    }.

  Record TermRedWhnf l (Γ : context) (A t u : term) : Type :=
    {
      tmred_whnf_red :> [ Γ |- t ⤳* u : A ]< l > ;
      tmred_whnf_whnf :> whnf u
    }.

  Record TypeConvWf l (Γ : context) (A B : term) : Type :=
    { 
      tyc_wf_l : [Γ |- A]< l > ;
      tyc_wf_r : [Γ |- B]< l > ;
      tyc_wf_conv :> [Γ |- A ≅ B]< l >
    }.

  Record TermConvWf l (Γ : context) (A t u : term) : Type :=
    {
      tmc_wf_l : [Γ |- t : A]< l > ;
      tmc_wf_r : [Γ |- u : A]< l > ;
      tmc_wf_conv :> [Γ |- t ≅ u : A]< l >
    }.

  Record TypeRedWf l (Γ : context) (A B : term) : Type := {
    tyr_wf_r : [Γ |- B]< l >;
    tyr_wf_red :> [Γ |- A ⤳* B]< l >
  }.

  Record TermRedWf l (Γ : context) (A t u : term) : Type := {
    tmr_wf_r : [Γ |- u : A]< l >;
    tmr_wf_red :> [Γ |- t ⤳* u : A]< l >
  }.

  (** *** Lifting of typing and conversion to contexts and substitutions *)

  Inductive WellSubst l (Γ : context) : context -> (nat -> term) -> Type :=
    | well_sempty (σ : nat -> term) : [Γ |-s σ : ε ]< l >
    | well_scons (σ : nat -> term) (Δ : context) A :
      [Γ |-s ↑ >> σ : Δ]< l > -> [Γ |- σ var_zero : A[↑ >> σ]]< l > ->
      [Γ |-s σ : Δ,, A]< l >
  where "[ Γ '|-s' σ : Δ ]< l >" := (WellSubst l Γ Δ σ).

  Inductive ConvSubst l (Γ : context) : context -> (nat -> term) -> (nat -> term) -> Type :=
  | conv_sempty (σ τ : nat -> term) : [Γ |-s σ ≅ τ : ε ]< l >
  | conv_scons (σ τ : nat -> term) (Δ : context) A :
    [Γ |-s ↑ >> σ ≅ ↑ >> τ : Δ]< l > -> [Γ |- σ var_zero ≅ τ var_zero: A[↑ >> σ]]< l > ->
    [Γ |-s σ ≅ τ : Δ,, A]< l >
  where "[ Γ '|-s' σ ≅ τ : Δ ]< l >" := (ConvSubst l Γ Δ σ τ).

  Inductive ConvCtx (l : wfLCon) : context -> context -> Type :=
  | conv_cempty : [ |- ε ≅ ε]< l >
  | conv_ccons Γ A Δ B : [ |- Γ ≅ Δ ]< l > -> [Γ |- A ≅ B]< l > -> [ |- Γ,, A ≅ Δ,, B]< l >
  where "[ |- Γ ≅ Δ ]< l >" := (ConvCtx l Γ Δ).


  Lemma well_subst_ext l Γ Δ (σ σ' : nat -> term) :
    σ =1 σ' ->
    [Γ |-s σ : Δ]< l > ->
    [Γ |-s σ' : Δ]< l >.
  Proof.
    intros Heq.
    induction 1 in σ', Heq |- *.
    all: constructor.
    - eapply IHWellSubst.
      now rewrite Heq.
    - rewrite <- Heq.
      now replace A[↑ >> σ'] with A[↑ >> σ]
        by (now rewrite Heq).
  Qed.

  Record well_typed l Γ t :=
  {
    well_typed_type : term ;
    well_typed_typed : [Γ |- t : well_typed_type]< l >
  }.

  Record well_formed l Γ t :=
  {
    well_formed_class : class ;
    well_formed_typed :
    match well_formed_class with
    | istype => [Γ |- t]< l >
    | isterm A => [Γ |- t : A]< l >
    end
  }.

  Inductive isWfFun (l : wfLCon) (Γ : context) (A B : term) : term -> Set :=
    LamWfFun : forall A' t : term,
      [Γ |- A']< l > -> [Γ |- A ≅ A']< l > -> [Γ,, A |- t : B]< l > -> [Γ,, A' |- t : B]< l > -> isWfFun l Γ A B (tLambda A' t)
  | NeWfFun : forall f : term, [Γ |- f ~ f : tProd A B]< l > -> isWfFun l Γ A B f.

  Inductive isWfPair (l : wfLCon) (Γ : context) (A B : term) : term -> Set :=
    PairWfPair : forall A' B' a b : term,
      [Γ |- A']< l > -> [Γ |- A ≅ A']< l > ->
      [Γ,, A' |- B]< l > ->
      [Γ,, A' |- B']< l > ->
      [Γ,, A |- B']< l > ->
      [Γ,, A |- B ≅ B']< l > ->
      [Γ,, A' |- B ≅ B']< l > ->
      [Γ |- a : A]< l > ->
      [Γ |- B[a..]]< l > ->
      [Γ |- B'[a..]]< l > ->
      [Γ |- B[a..] ≅ B'[a..]]< l > ->
      [Γ |- b : B[a..]]< l > ->
      isWfPair l Γ A B (tPair A' B' a b)
  | NeWfPair : forall n : term, [Γ |- n ~ n : tSig A B]< l > -> isWfPair l Γ A B n.

End RedDefinitions.

Notation "[ Γ |- A ↘ B ]< l >" := (TypeRedWhnf l Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ↘ B ]< l >" := (TypeRedWhnf (ta := ta) l Γ A B) : typing_scope.
Notation "[ Γ |- t ↘ u : A ]< l >" := (TermRedWhnf l Γ A t u) (only parsing ): typing_scope.
Notation "[ Γ |-[ ta  ] t ↘ u : A ]< l >" := (TermRedWhnf (ta := ta) l Γ A t u) : typing_scope.
Notation "[ Γ |- A :≅: B ]< l >" := (TypeConvWf l Γ A B) (only parsing) : typing_scope.  
Notation "[ Γ |-[ ta  ] A :≅: B ]< l >" := (TypeConvWf (ta := ta) l Γ A B) : typing_scope.
Notation "[ Γ |- t :≅: u : A ]< l >" := (TermConvWf l Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :≅: u : A ]< l >" := (TermConvWf (ta := ta) l Γ A t u) : typing_scope.
Notation "[ Γ |- A :⤳*: B ]< l >" := (TypeRedWf l Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :⤳*: B ]< l >" := (TypeRedWf (ta := ta) l Γ A B) : typing_scope.
Notation "[ Γ |- t :⤳*: u : A ]< l >" := (TermRedWf l Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :⤳*: u : A ]< l >" := (TermRedWf (ta := ta) l Γ A t u) : typing_scope.
Notation "[ Γ '|-s' σ : A ]< l >" := (WellSubst l Γ A σ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ : A ]< l >" := (WellSubst (ta := ta) l Γ A σ) : typing_scope.
Notation "[ Γ '|-s' σ ≅ τ : A ]< l >" := (ConvSubst l Γ A σ τ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ ≅ τ : A ]< l >" := (ConvSubst (ta := ta) l Γ A σ τ) : typing_scope.
Notation "[ |- Γ ≅ Δ ]< l >" := (ConvCtx l Γ Δ) (only parsing) : typing_scope.
Notation "[ |-[ ta  ] Γ ≅ Δ ]< l >" := (ConvCtx (ta := ta) l Γ Δ) : typing_scope.

#[export] Hint Resolve
  Build_TypeRedWhnf Build_TermRedWhnf Build_TypeConvWf
  Build_TermConvWf Build_TypeRedWf Build_TermRedWf
  well_sempty well_scons conv_sempty conv_scons
  tyr_wf_r tyr_wf_red tmr_wf_r tmr_wf_red
  : gen_typing.

(* #[export] Hint Extern 1 =>
  match goal with
    | H : [ _ |- _ ▹h _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ : _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ : _] |- _ => destruct H
    |  H : [ _ |- _ :⤳*: _ ] |- _ => destruct H
    |  H : [ _ |- _ :⤳*: _ : _ ] |- _ => destruct H
  end
  : gen_typing. *)

(** ** Properties of the abstract interface *)

Section GenericTyping.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta} `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Class WfContextProperties :=
  {
    wfc_nil {l} : [|- ε ]< l > ;
    wfc_cons {l} {Γ} {A} : [|- Γ]< l > -> [Γ |- A]< l > -> [|- Γ,,A]< l >;
    wfc_wft {l Γ A} : [Γ |- A]< l > -> [|- Γ]< l >;
    wfc_ty {l Γ A t} : [Γ |- t : A]< l > -> [|- Γ]< l >;
    wfc_convty {l Γ A B} : [Γ |- A ≅ B]< l > -> [|- Γ]< l >;
    wfc_convtm {l Γ A t u} : [Γ |- t ≅ u : A]< l > -> [|- Γ]< l >;
    wfc_redty {l Γ A B} : [Γ |- A ⤳* B]< l > -> [|- Γ]< l >;
    wfc_redtm {l Γ A t u} : [Γ |- t ⤳* u : A]< l > -> [|- Γ]< l > ;
    wfc_Ltrans {Γ l l'} (f : l' ≤ε l) :
    [ |- Γ ]< l > -> [ |- Γ ]< l' > ;
    wfc_ϝ {l Γ n} {ne : not_in_LCon (pi1 l) n} : 
        [ |- Γ ]< l ,,l (ne, true) > ->
        [ |- Γ ]< l ,,l (ne, false) > ->
        [ |- Γ ]< l >
  }.

  Class WfTypeProperties :=
  {
    wft_wk {l Γ Δ A} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- A]< l > -> [Δ |- A⟨ρ⟩]< l > ;
    wft_U {l Γ} : 
      [ |- Γ ]< l > ->
      [ Γ |- U ]< l > ;
    wft_prod {l Γ} {A B} : 
      [ Γ |- A ]< l > -> 
      [Γ ,, A |- B ]< l > -> 
      [ Γ |- tProd A B ]< l > ;
    wft_sig {l Γ} {A B} : 
      [ Γ |- A ]< l > -> 
      [Γ ,, A |- B ]< l > -> 
      [ Γ |- tSig A B ]< l > ;
    wft_Id {l Γ} {A x y} :
      [Γ |- A]< l > ->
      [Γ |- x : A]< l > ->
      [Γ |- y : A]< l > ->
      [Γ |- tId A x y]< l > ;
    wft_term {l Γ} {A} :
      [ Γ |- A : U ]< l > -> 
      [ Γ |- A ]< l > ; 
    wft_Ltrans {Γ l l' A} (f : l' ≤ε l) :
    [ Γ |- A ]< l > -> [ Γ |- A ]< l' >;
    wft_ϝ {l Γ A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- A ]< l ,,l (ne, true) > ->
        [ Γ |- A ]< l ,,l (ne, false) > ->
        [ Γ |- A ]< l >
  }.

  Class TypingProperties :=
  {
    ty_wk {l Γ Δ t A} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- t : A]< l > -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩]< l > ;
    ty_var {l Γ} {n decl} :
      [   |- Γ ]< l > ->
      in_ctx Γ n decl ->
      [ Γ |- tRel n : decl ]< l > ;
    ty_prod {l Γ} {A B} :
        [ Γ |- A : U]< l > -> 
        [Γ ,, A |- B : U ]< l > ->
        [ Γ |- tProd A B : U ]< l > ;
    ty_lam {l Γ}  {A B t} :
        [ Γ |- A ]< l > ->
        [ Γ ,, A |- t : B ]< l > -> 
        [ Γ |- tLambda A t : tProd A B]< l > ;
    ty_app {l Γ}  {f a A B} :
        [ Γ |- f : tProd A B ]< l > -> 
        [ Γ |- a : A ]< l > -> 
        [ Γ |- tApp f a : B[a ..] ]< l > ;
    ty_nat {l Γ} :
        [|-Γ]< l > ->
        [Γ |- tNat : U]< l > ;
    ty_zero {l Γ} :
        [|-Γ]< l > ->
        [Γ |- tZero : tNat]< l > ;
    ty_succ {l Γ n} :
        [Γ |- n : tNat]< l > ->
        [Γ |- tSucc n : tNat]< l > ;
    ty_natElim {l Γ P hz hs n} :
      [Γ ,, tNat |- P ]< l > ->
      [Γ |- hz : P[tZero..]]< l > ->
      [Γ |- hs : elimSuccHypTy P]< l > ->
      [Γ |- n : tNat]< l > ->
      [Γ |- tNatElim P hz hs n : P[n..]]< l > ;
    ty_empty {l Γ} :
        [|-Γ]< l > ->
        [Γ |- tEmpty : U]< l > ;
    ty_emptyElim {l Γ P e} :
      [Γ ,,  tEmpty |- P ]< l > ->
      [Γ |- e : tEmpty]< l > ->
      [Γ |- tEmptyElim P e : P[e..]]< l > ;
    ty_bool {l Γ} :
        [|-Γ]< l > ->
        [Γ |- tBool : U]< l > ;
    ty_true {l Γ} :
        [|-Γ]< l > ->
        [Γ |- tTrue : tBool]< l > ;
    ty_false {l Γ} :
        [|-Γ]< l > ->
        [Γ |- tFalse : tBool]< l > ;
    ty_alpha {l Γ n} :
        [Γ |- n : tNat]< l > ->
        [Γ |- tAlpha n : tBool]< l > ;
    ty_boolElim {l Γ P ht hf b} :
      [Γ ,, tBool |- P ]< l > ->
      [Γ |- ht : P[tTrue..]]< l > ->
      [Γ |- hf : P[tFalse..]]< l > ->
      [Γ |- b : tBool]< l > ->
      [Γ |- tBoolElim P ht hf b : P[b..]]< l > ;
    ty_sig {l Γ} {A B} :
        [ Γ |- A : U]< l > -> 
        [Γ ,, A |- B : U ]< l > ->
        [ Γ |- tSig A B : U ]< l > ;
    ty_pair {l Γ} {A B a b} :
        [ Γ |- A ]< l > -> 
        [Γ ,, A |- B ]< l > ->
        [Γ |- a : A]< l > ->
        [Γ |- b : B[a..]]< l > ->
        [Γ |- tPair A B a b : tSig A B]< l > ;
    ty_fst {l Γ A B p} :
        [Γ |- p : tSig A B]< l > ->
        [Γ |- tFst p : A]< l > ;
    ty_snd {l Γ A B p} :
        [Γ |- p : tSig A B]< l > ->
        [Γ |- tSnd p : B[(tFst p)..]]< l > ;
    ty_Id {l Γ} {A x y} :
      [Γ |- A : U]< l > ->
      [Γ |- x : A]< l > ->
      [Γ |- y : A]< l > ->
      [Γ |- tId A x y : U]< l > ;
    ty_refl {l Γ A x} :
      [Γ |- A]< l > ->
      [Γ |- x : A]< l > ->
      [Γ |- tRefl A x : tId A x x]< l > ;
    ty_IdElim {l Γ A x P hr y e} :
      [Γ |- A]< l > ->
      [Γ |- x : A]< l > ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< l > ->
      [Γ |- hr : P[tRefl A x .: x..]]< l > ->
      [Γ |- y : A]< l > ->
      [Γ |- e : tId A x y]< l > ->
      [Γ |- tIdElim A x P hr y e : P[e .: y..]]< l >;
    ty_exp {l Γ t A A'} : [Γ |- t : A']< l > -> [Γ |- A ⤳* A']< l > -> [Γ |- t : A]< l > ;
    ty_conv {l Γ t A A'} : [Γ |- t : A']< l > -> [Γ |- A' ≅ A]< l > -> [Γ |- t : A]< l > ;
    ty_Ltrans {Γ l l' t A} (f : l' ≤ε l) :
    [ Γ |- t : A ]< l > -> [ Γ |- t : A ]< l' >;
    ty_ϝ {l Γ t A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- t : A ]< l ,,l (ne, true) > ->
        [ Γ |- t : A ]< l ,,l (ne, false) > ->
        [ Γ |- t : A ]< l >
  }.

  Class ConvTypeProperties :=
  {
    convty_term {l Γ A B} : [Γ |- A ≅ B : U]< l > -> [Γ |- A ≅ B]< l > ;
    convty_equiv {l Γ} :: PER (conv_type l Γ) ;
    convty_wk {l Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- A ≅ B]< l > -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]< l > ;
    convty_exp {l Γ A A' B B'} :
      [Γ |- A ⤳* A']< l > -> [Γ |- B ⤳* B']< l > ->
      [Γ |- A' ≅ B']< l > -> [Γ |- A ≅ B]< l > ;
    convty_uni {l Γ} :
      [|- Γ]< l > -> [Γ |- U ≅ U]< l > ;
    convty_prod {l Γ A A' B B'} :
      [Γ |- A]< l > ->
      [Γ |- A ≅ A']< l > -> [Γ,, A |- B ≅ B']< l > ->
      [Γ |- tProd A B ≅ tProd A' B']< l > ;
    convty_sig {l Γ A A' B B'} :
      [Γ |- A]< l > ->
      [Γ |- A ≅ A']< l > -> [Γ,, A |- B ≅ B']< l > ->
      [Γ |- tSig A B ≅ tSig A' B']< l > ;
    convty_Id {l Γ A A' x x' y y'} :
      (* [Γ |- A] -> ?  *)
      [Γ |- A ≅ A']< l > ->
      [Γ |- x ≅ x' : A]< l > ->
      [Γ |- y ≅ y' : A]< l > ->
      [Γ |- tId A x y ≅ tId A' x' y' ]< l > ;
    convty_Ltrans {Γ l l' A B} (f : l' ≤ε l) :
    [ Γ |- A ≅ B]< l > -> [ Γ |- A ≅ B]< l' >;
    convty_ϝ {l Γ A B n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- A ≅ B ]< l ,,l (ne, true) > ->
        [ Γ |- A ≅ B ]< l ,,l (ne, false) > ->
        [ Γ |- A ≅ B ]< l >
  }.

  Class ConvTermProperties :=
  {
    convtm_equiv {l Γ A} :: PER (conv_term l Γ A) ;
    convtm_conv {l Γ t u A A'} : [Γ |- t ≅ u : A]< l > -> [Γ |- A ≅ A']< l > -> [Γ |- t ≅ u : A']< l > ;
    convtm_wk {l Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- t ≅ u : A]< l > -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]< l > ;
    convtm_exp {l Γ A t t' u u'} :
      [Γ |- t ⤳* t' : A]< l > -> [Γ |- u ⤳* u' : A]< l > ->
      [Γ |- A]< l > -> [Γ |- t' : A]< l > -> [Γ |- u' : A]< l > ->
      [Γ |- A ≅ A]< l > -> [Γ |- t' ≅ u' : A]< l > -> [Γ |- t ≅ u : A]< l > ;
    convtm_convneu {l Γ n n' A} :
      isPosType A ->
      [Γ |- n ~ n' : A]< l > -> [Γ |- n ≅ n' : A]< l > ;
    convtm_prod {l Γ A A' B B'} :
      [Γ |- A : U]< l > ->
      [Γ |- A ≅ A' : U]< l > -> [Γ,, A |- B ≅ B' : U]< l > ->
      [Γ |- tProd A B ≅ tProd A' B' : U]< l > ;
    convtm_sig {l Γ A A' B B'} :
      [Γ |- A : U]< l > ->
      [Γ |- A ≅ A' : U]< l > -> [Γ,, A |- B ≅ B' : U]< l > ->
      [Γ |- tSig A B ≅ tSig A' B' : U]< l > ;
    convtm_eta {l Γ f g A B} :
      [ Γ |- A ]< l > ->
      [ Γ,, A |- B ]< l > ->
      [ Γ |- f : tProd A B ]< l > ->
      isWfFun l Γ A B f ->
      [ Γ |- g : tProd A B ]< l > ->
      isWfFun l Γ A B g ->
      [ Γ ,, A |- eta_expand f ≅ eta_expand g : B ]< l > ->
      [ Γ |- f ≅ g : tProd A B ]< l > ;
    convtm_nat {l Γ} :
      [|-Γ]< l > -> [Γ |- tNat ≅ tNat : U]< l > ;
    convtm_zero {l Γ} :
      [|-Γ]< l > -> [Γ |- tZero ≅ tZero : tNat]< l > ;
    convtm_succ {l Γ} {n n'} :
        [Γ |- n ≅ n' : tNat]< l > ->
        [Γ |- tSucc n ≅ tSucc n' : tNat]< l > ;
    convtm_eta_sig {l Γ p p' A B} :
      [Γ |- A]< l > ->
      [Γ ,, A |- B]< l > ->
      [Γ |- p : tSig A B]< l > ->
      isWfPair l Γ A B p ->
      [Γ |- p' : tSig A B]< l > ->
      isWfPair l Γ A B p' ->
      [Γ |- tFst p ≅ tFst p' : A]< l > ->
      [Γ |- tSnd p ≅ tSnd p' : B[(tFst p)..]]< l > ->
      [Γ |- p ≅ p' : tSig A B]< l > ;
    convtm_empty {l Γ} :
      [|-Γ]< l > -> [Γ |- tEmpty ≅ tEmpty : U]< l > ;
    convtm_bool {l Γ} :
      [|-Γ]< l > -> [Γ |- tBool ≅ tBool : U]< l > ;
    convtm_true {l Γ} :
      [|-Γ]< l > -> [Γ |- tTrue ≅ tTrue : tBool]< l > ;
    convtm_false {l Γ} :
      [|-Γ]< l > -> [Γ |- tFalse ≅ tFalse : tBool]< l > ;
    convtm_alphacong {l Γ} {n n'} :
          [ Γ |- n ≅ n' : tNat]< l > ->
          [ Γ |- tAlpha n ≅ tAlpha n' : tBool]< l >;
    convtm_alpha {l Γ n b} :
        [ |- Γ ]< l > ->
        in_LCon (pi1 l) n b ->
        [ Γ |- tAlpha (nat_to_term n) ≅ bool_to_term b : tBool ]< l > ;
    convtm_Id {l Γ A A' x x' y y'} :
      (* [Γ |- A]< l > -> ?  *)
      [Γ |- A ≅ A' : U]< l > ->
      [Γ |- x ≅ x' : A]< l > ->
      [Γ |- y ≅ y' : A]< l > ->
      [Γ |- tId A x y ≅ tId A' x' y' : U ]< l > ;
    convtm_refl {l Γ A A' x x'} :
      [Γ |- A ≅ A']< l > ->
      [Γ |- x ≅ x' : A]< l > ->
      [Γ |- tRefl A x ≅ tRefl A' x' : tId A x x]< l > ;
    convtm_Ltrans {Γ l l' t u A} (f : l' ≤ε l) :
    [ Γ |- t ≅ u : A ]< l > -> [ Γ |- t ≅ u : A ]< l' >;
    convtm_ϝ {l Γ t u A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- t ≅ u : A ]< l ,,l (ne, true) > ->
        [ Γ |- t ≅ u : A ]< l ,,l (ne, false) > ->
        [ Γ |- t ≅ u : A ]< l >
  }.

  Class ConvNeuProperties :=
  {
    convneu_equiv {l Γ A} :: PER (conv_neu_conv l Γ A) ;
    convneu_conv {l Γ t u A A'} : [Γ |- t ~ u : A]< l > -> [Γ |- A ≅ A']< l > -> [Γ |- t ~ u : A']< l > ;
    convneu_wk {l Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- t ~ u : A]< l > -> [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ : A⟨ρ⟩]< l > ;
    convneu_whne {l Γ A t u} : [Γ |- t ~ u : A]< l > -> whne t;
    convneu_var {l Γ n A} :
      [Γ |- tRel n : A]< l > -> [Γ |- tRel n ~ tRel n : A]< l > ;
    convneu_app {l Γ f g t u A B} :
      [ Γ |- f ~ g : tProd A B ]< l > ->
      [ Γ |- t ≅ u : A ]< l > ->
      [ Γ |- tApp f t ~ tApp g u : B[t..] ]< l > ;
    convneu_natElim {l Γ P P' hz hz' hs hs' n n'} :
        [Γ ,, tNat |- P ≅ P']< l > ->
        [Γ |- hz ≅ hz' : P[tZero..]]< l > ->
        [Γ |- hs ≅ hs' : elimSuccHypTy P]< l > ->
        [Γ |- n ~ n' : tNat]< l > ->
        [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' : P[n..]]< l > ;
    convneu_emptyElim {l Γ P P' e e'} :
        [Γ ,, tEmpty |- P ≅ P']< l > ->
        [Γ |- e ~ e' : tEmpty]< l > ->
        [Γ |- tEmptyElim P e ~ tEmptyElim P' e' : P[e..]]< l > ;
    convneu_boolElim {l Γ P P' ht ht' hf hf' b b'} :
        [Γ ,, tBool |- P ≅ P']< l > ->
        [Γ |- ht ≅ ht' : P[tTrue..]]< l > ->
        [Γ |- hf ≅ hf' : P[tFalse..]]< l > ->
        [Γ |- b ~ b' : tBool]< l > ->
        [Γ |- tBoolElim P ht hf b ~ tBoolElim P' ht' hf' b' : P[b..]]< l > ;
    convneu_alpha {l Γ t u n} :
      [ Γ |- t ~ u : tNat ]< l > ->
      [ Γ |- tAlpha (nSucc n t) ~ tAlpha (nSucc n u) : tBool ]< l > ;
    convneu_fst {l Γ A B p p'} :
      [Γ |- p ~ p' : tSig A B]< l > ->
      [Γ |- tFst p ~ tFst p' : A]< l > ;
    convneu_snd {l Γ A B p p'} :
      [Γ |- p ~ p' : tSig A B]< l > ->
      [Γ |- tSnd p ~ tSnd p' : B[(tFst p)..]]< l > ;
    convneu_IdElim {l Γ A A' x x' P P' hr hr' y y' e e'} :
      (* Parameters well formed: required by declarative instance *)
      [Γ |- A]< l > ->
      [Γ |- x : A]< l > ->
      [Γ |- A ≅ A']< l > ->
      [Γ |- x ≅ x' : A]< l > ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P']< l > ->
      [Γ |- hr ≅ hr' : P[tRefl A x .: x..]]< l > ->
      [Γ |- y ≅ y' : A]< l > ->
      [Γ |- e ~ e' : tId A x y]< l > ->
      [Γ |- tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' : P[e .: y..]]< l >;
    convneu_Ltrans {Γ l l' t u A} (f : l' ≤ε l) :
    [ Γ |- t ~ u : A ]< l > -> [ Γ |- t ~ u : A ]< l' >;
    convneu_ϝ {l Γ t u A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- t ~ u : A ]< l ,,l (ne, true) > ->
        [ Γ |- t ~ u : A ]< l ,,l (ne, false) > ->
        [ Γ |- t ~ u : A ]< l >
  }.

  Class RedTypeProperties :=
  {
    redty_wk {l Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- A ⤳* B]< l > -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩]< l > ;
    redty_sound {l Γ A B} : [Γ |- A ⤳* B]< l > -> [A ⤳* B]< l > ;
    redty_ty_src {l Γ A B} : [Γ |- A ⤳* B]< l > -> [Γ |- A]< l > ;
    redty_term {l Γ A B} :
      [ Γ |- A ⤳* B : U]< l > -> [Γ |- A ⤳* B ]< l > ;
    redty_refl {l Γ A} :
      [ Γ |- A]< l > ->
      [Γ |- A ⤳* A]< l > ;
    redty_trans {l Γ} ::
      Transitive (red_ty l Γ) ;
    redty_Ltrans {Γ l l' A B} (f : l' ≤ε l) :
    [ Γ |- A ⤳* B ]< l > -> [ Γ |- A ⤳* B ]< l' > ;
  }.

  Class RedTermProperties :=
  {
    redtm_wk {l Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- t ⤳* u : A]< l > -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩]< l > ;
    redtm_sound {l Γ A t u} : [Γ |- t ⤳* u : A]< l > -> [t ⤳* u]< l > ;
    redtm_ty_src {l Γ A t u} : [Γ |- t ⤳* u : A]< l > -> [Γ |- t : A]< l > ;
    redtm_beta {l Γ A B t u} :
      [ Γ |- A ]< l > ->
      [ Γ ,, A |- t : B ]< l > ->
      [ Γ |- u : A ]< l > ->
      [ Γ |- tApp (tLambda A t) u ⤳* t[u..] : B[u..] ]< l > ;
    redtm_natElimZero {l Γ P hz hs} :
        [Γ ,, tNat |- P ]< l > ->
        [Γ |- hz : P[tZero..]]< l > ->
        [Γ |- hs : elimSuccHypTy P]< l > ->
        [Γ |- tNatElim P hz hs tZero ⤳* hz : P[tZero..]]< l > ;
    redtm_natElimSucc {l Γ P hz hs n} :
        [Γ ,, tNat |- P ]< l > ->
        [Γ |- hz : P[tZero..]]< l > ->
        [Γ |- hs : elimSuccHypTy P]< l > ->
        [Γ |- n : tNat]< l > ->
        [Γ |- tNatElim P hz hs (tSucc n) ⤳* tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]]< l > ;
    redtm_app {l Γ A B f f' t} :
      [ Γ |- f ⤳* f' : tProd A B ]< l > ->
      [ Γ |- t : A ]< l > ->
      [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ]< l >;
    redtm_natelim {l Γ P hz hs n n'} :
      [ Γ,, tNat |- P ]< l > ->
      [ Γ |- hz : P[tZero..] ]< l > ->
      [ Γ |- hs : elimSuccHypTy P ]< l > ->
      [ Γ |- n ⤳* n' : tNat ]< l > ->
      [ Γ |- tNatElim P hz hs n ⤳* tNatElim P hz hs n' : P[n..] ]< l >;
    redtm_boolElimTrue {l Γ P ht hf} :
        [Γ ,, tBool |- P ]< l > ->
        [Γ |- ht : P[tTrue..]]< l > ->
        [Γ |- hf : P[tFalse..]]< l > ->
        [Γ |- tBoolElim P ht hf tTrue ⤳* ht : P[tTrue..]]< l > ;
    redtm_boolElimFalse {l Γ P ht hf} :
        [Γ ,, tBool |- P ]< l > ->
        [Γ |- ht : P[tTrue..]]< l > ->
        [Γ |- hf : P[tFalse..]]< l > ->
        [Γ |- tBoolElim P ht hf tFalse ⤳* hf : P[tFalse..]]< l > ;
    redtm_boolElim {l Γ P ht hf b b'} :
        [Γ ,, tBool |- P ]< l > ->
        [Γ |- ht : P[tTrue..]]< l > ->
        [Γ |- hf : P[tFalse..]]< l > ->
        [ Γ |- b ⤳* b' : tBool ]< l > ->
        [Γ |- tBoolElim P ht hf b ⤳* tBoolElim P ht hf b' : P[b..]]< l > ;
    redtm_alpha {l Γ n b} :
        [ |- Γ ]< l > ->
        in_LCon (pi1 l) n b ->
        [ Γ |- tAlpha (nat_to_term n) ⤳* bool_to_term b : tBool ]< l > ;
    redtm_emptyelim {l Γ P n n'} :
      [ Γ,, tEmpty |- P ]< l > ->
      [ Γ |- n ⤳* n' : tEmpty ]< l > ->
      [ Γ |- tEmptyElim P n ⤳* tEmptyElim P n' : P[n..] ]< l >;
    redtm_fst_beta {l Γ A B a b} :
      [Γ |- A]< l > ->
      [Γ ,, A |- B]< l > ->
      [Γ |- a : A]< l > ->
      [Γ |- b : B[a..]]< l > ->
      [Γ |- tFst (tPair A B a b) ⤳* a : A]< l > ;
    redtm_fst {l Γ A B p p'} :
      [Γ |- p ⤳* p' : tSig A B]< l > ->
      [Γ |- tFst p ⤳* tFst p' : A]< l > ;
    redtm_snd_beta {l Γ A B a b} :
      [Γ |- A]< l > ->
      [Γ ,, A |- B]< l > ->
      [Γ |- a : A]< l > ->
      [Γ |- b : B[a..]]< l > ->
      [Γ |- tSnd (tPair A B a b) ⤳* b : B[(tFst (tPair A B a b))..]]< l > ;
    redtm_snd {l Γ A B p p'} :
      [Γ |- p ⤳* p' : tSig A B]< l > ->
      [Γ |- tSnd p ⤳* tSnd p' : B[(tFst p)..]]< l > ;
    redtm_idElimRefl {l Γ A x P hr y A' z} :
      [Γ |- A]< l > ->
      [Γ |- x : A]< l > ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< l > ->
      [Γ |- hr : P[tRefl A x .: x..]]< l > ->
      [Γ |- y : A]< l > ->
      [Γ |- A']< l > ->
      [Γ |- z : A]< l > ->
      [Γ |- A ≅ A']< l > ->
      [Γ |- x ≅ y : A]< l > ->
      [Γ |- x ≅ z : A]< l > ->
      [Γ |- tIdElim A x P hr y (tRefl A' z) ⤳* hr : P[tRefl A' z .: y..]]< l >;
    redtm_idElim {l Γ A x P hr y e e'} :
      [Γ |- A]< l > ->
      [Γ |- x : A]< l > ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P]< l > ->
      [Γ |- hr : P[tRefl A x .: x..]]< l > ->
      [Γ |- y : A]< l > ->
      [Γ |- e ⤳* e' : tId A x y]< l > ->
      [Γ |- tIdElim A x P hr y e ⤳* tIdElim A x P hr y e' : P[e .: y..]]< l >;
    redtm_conv {l Γ t u A A'} : 
      [Γ |- t ⤳* u : A]< l > ->
      [Γ |- A ≅ A']< l > ->
      [Γ |- t ⤳* u : A']< l > ;
    redtm_refl {l Γ A t } :
      [ Γ |- t : A]< l > ->
      [Γ |- t ⤳* t : A]< l > ;
    redtm_trans {l Γ A} ::
      Transitive (red_tm l Γ A) ;
    redtm_Ltrans {Γ l l' t u A} (f : l' ≤ε l) :
    [ Γ |- t ⤳* u : A ]< l > -> [ Γ |- t ⤳* u : A ]< l' > ;
  }.

End GenericTyping.

(** This class bundles together the various predicate and relations, and their
properties all together. Most of the logical relation is constructed over an
abstract instance of this class. *)

Class GenericTypingProperties `(ta : tag)
  `(WfContext ta) `(WfType ta) `(Typing ta)
  `(ConvType ta) `(ConvTerm ta) `(ConvNeuConv ta)
  `(RedType ta) `(RedTerm ta)
  `(RedType ta) `(RedTerm ta)
:=
{
  wfc_prop :: WfContextProperties ;
  wfty_prop :: WfTypeProperties ;
  typ_prop :: TypingProperties ;
  convty_prop :: ConvTypeProperties ;
  convtm_prop :: ConvTermProperties ;
  convne_prop :: ConvNeuProperties ;
  redty_prop :: RedTypeProperties ;
  redtm_prop :: RedTermProperties ;
}.

(** Hints for gen_typing *)
(* Priority 0 *)
#[export] Hint Resolve wfc_wft wfc_ty wfc_convty wfc_convtm wfc_redty wfc_redtm : gen_typing.
(* Priority 2 *)
#[export] Hint Resolve wfc_nil wfc_cons | 2 : gen_typing.
#[export] Hint Resolve wft_wk wft_U wft_prod wft_sig wft_Id | 2 : gen_typing.
#[export] Hint Resolve ty_wk ty_var ty_prod ty_lam ty_app ty_nat ty_empty ty_zero ty_succ ty_natElim ty_emptyElim ty_sig ty_pair ty_fst ty_snd ty_Id ty_refl ty_IdElim| 2 : gen_typing.
#[export] Hint Resolve convty_wk convty_uni convty_prod convty_sig convty_Id | 2 : gen_typing.
#[export] Hint Resolve convtm_wk convtm_prod convtm_eta convtm_nat convtm_empty convtm_zero convtm_succ convtm_eta_sig convtm_Id convtm_refl | 2 : gen_typing.
#[export] Hint Resolve convneu_wk convneu_var convneu_app convneu_natElim convneu_emptyElim convneu_fst convneu_snd convneu_IdElim | 2 : gen_typing.
#[export] Hint Resolve redty_ty_src redtm_ty_src | 2 : gen_typing.
(* Priority 4 *)
#[export] Hint Resolve wft_term convty_term convtm_convneu | 4 : gen_typing.
(* Priority 6 *)
#[export] Hint Resolve ty_conv ty_exp convty_exp convtm_exp convtm_conv convneu_conv redtm_conv | 6 : gen_typing.

(** A tactic to transform applications of (untyped) renamings back to (well-typed) weakenings,
so that we can use stability by weakening. *)

Ltac renToWk0 judg :=
  lazymatch judg with
  (** Type judgement, weakening *)
  | [?X ,, ?Y |- ?T⟨↑⟩ ]< ?l > =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  (** Type judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ]< ?l > =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ]< ?l > =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (* Type judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ]< ?l > =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on

  (** Type conversion judgement, weakening *)
  | [?X ,, ?Y |- ?T⟨↑⟩ ≅ _ ]< ?l > =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  | [?X ,, ?Y |- _ ≅ ?T⟨↑⟩ ]< ?l > =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  (** Type conversion judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ≅ _ ]< ?l > =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ≅ _ ]< ?l > =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ ?T⟨upRen_term_term ↑⟩ ]< ?l > =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (* Type conversion judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ≅ _ ]< ?l > =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- _ ≅ ?T⟨upRen_term_term _⟩ ]< ?l > =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on

  (** Term judgement, weakening *)
  | [?X ,, ?Y |- _ : ?T⟨↑⟩ ]< ?l > =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- ?t⟨↑⟩ : _ ]< ?l > =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  (** Term judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ : _ ]< ?l > =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ : ?T⟨upRen_term_term ↑⟩ ]< ?l > =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ : _ ]< ?l > =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (** Term judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ : ?T⟨upRen_term_term _⟩ ]< ?l > =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ : _ ]< ?l > =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on

  (** Term conversion judgement, weakening *)
  | [?X ,, ?Y |- _ ≅ _ : ?T⟨↑⟩ ]< ?l > =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- ?t⟨↑⟩ ≅ _ : _ ]< ?l > =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- _ ≅ ?t⟨↑⟩ : _ ]< ?l > =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  (** Term conversion judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ≅ _ : _ ]< ?l > =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ _ : ?T⟨upRen_term_term ↑⟩ ]< ?l > =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ ≅ _ : _ ]< ?l > =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ ?t⟨upRen_term_term ↑⟩ : _ ]< ?l > =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (** Term conversion judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ ≅ _ : ?T⟨upRen_term_term _⟩ ]< ?l > =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ ≅ _ : _ ]< ?l > =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ ≅ ?t⟨upRen_term_term _⟩ : _ ]< ?l > =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on


  end.

Ltac renToWk :=
  fold ren_term;
  repeat change (ren_term ?x ?y) with y⟨x⟩;
  repeat change S with ↑;
  repeat lazymatch goal with 
  | [ _ : _ |- ?G] => renToWk0 G 
  end.


(** ** Easy consequences of the previous properties. *)

Section GenericConsequences.
  Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!WfContextProperties} `{!WfTypeProperties}
  `{!TypingProperties} `{!ConvTypeProperties}
  `{!ConvTermProperties} `{!ConvNeuProperties}
  `{!RedTypeProperties} `{!RedTermProperties}.

  (** *** Meta-conversion *)
  (** Similar to conversion, but using a meta-level equality rather
  than a conversion *)

  Lemma typing_meta_conv (l : wfLCon) (Γ : context) (t A A' : term) :
    [Γ |- t : A]< l > ->
    A' = A ->
    [Γ |- t : A']< l >.
  Proof.
    now intros ? ->.
  Qed.

  Lemma convtm_meta_conv (l : wfLCon)  (Γ : context) (t u u' A A' : term) :
    [Γ |- t ≅ u : A]< l > ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A']< l >.
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma convne_meta_conv (l : wfLCon)  (Γ : context) (t u u' A A' : term) :
    [Γ |- t ~ u : A]< l > ->
    A' = A ->
    u' = u ->
    [Γ |- t ~ u' : A']< l >.
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtm_meta_conv (l : wfLCon)  (Γ : context) (t u u' A A' : term) :
    [Γ |- t ⤳* u : A]< l > ->
    A' = A ->
    u' = u ->
    [Γ |- t ⤳* u' : A']< l >.
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtmwf_meta_conv_ty (l : wfLCon)  (Γ : context) (t u A A' : term) :
    [Γ |- t :⤳*: u : A]< l > ->
    A' = A ->
    [Γ |- t :⤳*: u : A']< l >.
  Proof.
    now intros ? ->. 
  Qed.

  (** *** Properties of well-typed reduction *)

  Lemma tyr_wf_l {l Γ A B} : [Γ |- A :⤳*: B]< l > -> [Γ |- A]< l >.
  Proof.
    intros []; now eapply redty_ty_src.
  Qed.
  
  Lemma tmr_wf_l {l Γ t u A} : [Γ |- t :⤳*: u : A]< l > -> [Γ |- t : A]< l >.
  Proof.
    intros []; now eapply redtm_ty_src.
  Qed.

  #[local] Hint Resolve tyr_wf_l tmr_wf_l : gen_typing.
  #[local] Hint Resolve redty_wk redty_term redty_refl redtm_wk redtm_app redtm_refl | 2 : gen_typing.
  #[local] Hint Resolve redtm_beta redtm_natElimZero redtm_natElimSucc | 2 : gen_typing.
  #[local] Hint Resolve  redtm_conv | 6 : gen_typing.

  Lemma redty_red {l Γ A B} :
      [Γ |- A ⤳* B]< l > -> [ A ⤳* B ]< l >.
  Proof.
    intros ?%redty_sound. 
    assumption.
  Qed.

  Lemma redtm_red {l Γ t u A} : 
      [Γ |- t ⤳* u : A]< l > ->
      [t ⤳* u]< l >.
  Proof.
    intros ?%redtm_sound.
    assumption.
  Qed.

  #[local] Hint Resolve redty_red  redtm_red | 2 : gen_typing.

  Lemma redtywf_wk {l Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- A :⤳*: B]< l > -> [Δ |- A⟨ρ⟩ :⤳*: B⟨ρ⟩]< l >.
  Proof.
    intros ? []; constructor; gen_typing.
  Qed.

  Lemma redtywf_red {l Γ A B} : [Γ |- A :⤳*: B]< l > -> [A ⤳* B]< l >.
  Proof.
    intros []; now eapply redty_red.
  Qed.
  
  Lemma redtywf_term {l Γ A B} :
      [ Γ |- A :⤳*: B : U]< l > -> [Γ |- A :⤳*: B ]< l >.
  Proof.
    intros []; constructor; gen_typing.
  Qed.

  Lemma redtywf_refl {l Γ A} : [Γ |- A]< l > -> [Γ |- A :⤳*: A]< l >.
  Proof.  constructor; gen_typing.  Qed.

  #[global]
  Instance redtywf_trans {l Γ} : Transitive (TypeRedWf l Γ). (* fun A B => [Γ |- A :⤳*: B]< l > *)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  (** Almost all of the RedTermProperties can be derived 
    for the well-formed reduction [Γ |- t :⤳*: u : A]
    but for application (which requires stability of typing under substitution). *)
    
  Definition redtmwf_wk {l Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ]< l > -> [Γ |- t :⤳*: u : A]< l > -> [Δ |- t⟨ρ⟩ :⤳*: u⟨ρ⟩ : A⟨ρ⟩]< l >.
  Proof.  intros ? []; constructor; gen_typing. Qed.

  Definition redtmwf_red {l Γ t u A} :
    [Γ |- t :⤳*: u : A]< l > -> [t ⤳* u]< l >.
  Proof. intros []; now eapply redtm_red. Qed.

  Definition redtmwf_conv {l Γ} {t u A B} :
      [Γ |- t :⤳*: u : A]< l > ->
      [Γ |- A ≅ B ]< l > ->
      [Γ |- t :⤳*: u : B]< l >.
  Proof.
    intros [wfl red] ?.
    constructor.
    all: gen_typing.
  Qed.

  Lemma redtmwf_refl {l Γ a A} : [Γ |- a : A]< l > -> [Γ |- a :⤳*: a : A]< l >.
  Proof.
    constructor; tea.
    now apply redtm_refl.
  Qed.

  #[global]
  Instance redtmwf_trans {l Γ A} : Transitive (TermRedWf l Γ A). (*fun t u => [Γ |- t :⤳*: u : A]< l >*)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  Lemma redtmwf_app {l Γ A B f f' t} :
    [ Γ |- f :⤳*: f' : tProd A B ]< l > ->
    [ Γ |- t : A ]< l > ->
    [ Γ |- tApp f t :⤳*: tApp f' t : B[t..] ]< l >.
  Proof.
    intros [] ?; constructor; gen_typing.
  Qed.
  
  Lemma redtmwf_appwk {l Γ Δ A B B' t u a} (ρ : Δ ≤ Γ) :
    [Γ |- t :⤳*: u : tProd A B]< l > ->
    [Δ |- a : A⟨ρ⟩]< l > ->
    B' = B⟨upRen_term_term ρ⟩[a..] ->
    [Δ |- tApp t⟨ρ⟩ a :⤳*: tApp u⟨ρ⟩ a : B']< l >.
  Proof.
    intros redtu **.
    eapply redtmwf_meta_conv_ty; tea.
    eapply redtmwf_app; tea.
    unshelve eapply (redtmwf_wk ρ _ redtu).
    gen_typing.
  Qed.

  Lemma redtmwf_natElimZero {l Γ P hz hs} :
    [Γ ,, tNat |- P ]< l > ->
    [Γ |- hz : P[tZero..]]< l > ->
    [Γ |- hs : elimSuccHypTy P]< l > ->
    [Γ |- tNatElim P hz hs tZero :⤳*: hz : P[tZero..]]< l >.
  Proof.
    intros ???; constructor; tea; gen_typing.
  Qed.

  (** *** Properties of well-typing *)

  Definition well_typed_well_formed l Γ t : well_typed l Γ t -> well_formed l Γ t :=
  fun w =>
  {|
    well_formed_class := isterm (well_typed_type l Γ t w) ;
    well_formed_typed := well_typed_typed l Γ t w
  |}.

  #[warning="-uniform-inheritance"]Coercion well_typed_well_formed : well_typed >-> well_formed.

  Definition well_formed_well_typed l Γ t (w : well_formed l Γ t) : (well_typed l Γ t + [Γ |- t]< l >) :=
  (match (well_formed_class _ _ _ w) as c return
      (match c with
      | istype => [Γ |-[ ta ] t]< l >
      | isterm A => [Γ |-[ ta ] t : A]< l >
      end -> well_typed l Γ t + [Γ |-[ ta ] t]< l >)
  with
  | istype => inr
  | isterm A => fun w' => inl {| well_typed_type := A ; well_typed_typed := w' |}
    end) (well_formed_typed _ _ _ w).

  (** *** Derived typing, reduction and conversion judgements *)

  Lemma ty_var0 {l Γ A} : 
    [Γ |- A]< l > ->
    [Γ ,, A |- tRel 0 : A⟨↑⟩]< l >.
  Proof. 
    intros; refine (ty_var _ (in_here _ _)); gen_typing.
  Qed.

  Lemma wft_simple_arr {l Γ A B} :
    [Γ |- A]< l > ->
    [Γ |- B]< l > ->
    [Γ |- arr A B]< l >.
  Proof.
    intros. eapply wft_prod; renToWk; tea.
    eapply wft_wk; gen_typing.
  Qed.

  Lemma convty_simple_arr {l Γ A A' B B'} :
    [Γ |- A]< l > ->
    [Γ |- A ≅ A']< l > ->
    [Γ |- B ≅ B']< l > ->
    [Γ |- arr A B ≅ arr A' B']< l >.
  Proof.
    intros; eapply convty_prod; tea.
    renToWk; eapply convty_wk; gen_typing.
  Qed.

  Lemma ty_simple_app {l Γ A B f a} :
    [Γ |- A]< l > ->
    [Γ |- B]< l > ->
    [Γ |- f : arr A B]< l > ->
    [Γ |- a : A]< l > ->
    [Γ |- tApp f a : B]< l >.
  Proof.
    intros. replace B with B⟨shift⟩[a..] by now asimpl.
    eapply ty_app; tea.
  Qed.

  Lemma convneu_simple_app {l Γ f g t u A B} :
      [ Γ |- f ~ g : arr A B ]< l > ->
      [ Γ |- t ≅ u : A ]< l > ->
      [ Γ |- tApp f t ~ tApp g u : B ]< l >.
  Proof.
    intros.
    replace B with B⟨↑⟩[t..] by now asimpl.
    now eapply convneu_app.
  Qed.

  #[local]
  Hint Resolve ty_simple_app : gen_typing.
  
  Lemma ty_id {l Γ A B C} : 
    [Γ |- A]< l > ->
    [Γ |- A ≅ B]< l > ->
    [Γ |- A ≅ C]< l > ->
    [Γ |- idterm A : arr B C]< l >.
  Proof.
    intros.
    eapply ty_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply ty_lam; tea.
    now eapply ty_var0.
  Qed.

  Lemma ty_id' {l Γ A} : 
    [Γ |- A]< l > ->
    [Γ |- idterm A : arr A A]< l >.
  Proof.
    intros.
    (* eapply ty_conv. *)
    (* 2: eapply convty_simple_arr; cycle 1; tea. *)
    eapply ty_lam; tea.
    now eapply ty_var0.
  Qed.
  
  Lemma redtm_id_beta {l Γ a A} :
    [Γ |- A]< l > ->
    [Γ |- A ≅ A]< l > ->
    [Γ |- a : A]< l > ->
    [Γ |- tApp (idterm A) a ⤳* a : A]< l >.
  Proof.
    intros.
    eapply redtm_meta_conv.
    1: eapply redtm_beta; tea.
    + now eapply ty_var0.
    + cbn; now bsimpl.
    + now asimpl.
  Qed.

  Lemma convtm_id {l Γ A A' B C} : 
    [|- Γ]< l > ->
    [Γ |- A]< l > ->
    [Γ |- A']< l > ->
    [Γ |- A ≅ A']< l > ->
    [Γ |- A ≅ B]< l > ->
    [Γ |- A ≅ C]< l > ->
    [Γ,, A |- tRel 0 ≅ tRel 0 : A⟨↑⟩]< l > ->
    [Γ |- idterm A ≅ idterm A' : arr B C]< l >.
  Proof.
    intros.
    assert [Γ |- A ≅ A]< l > by (etransitivity; tea; now symmetry).
    eapply convtm_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply convtm_eta; tea.
    { renToWk; apply wft_wk; [apply wfc_cons|]; tea. }
    2:{ constructor; first [now eapply lrefl|now apply ty_var0|tea]. }
    3:{ constructor; first [now eapply lrefl|now apply ty_var0|tea].
        eapply ty_conv; [now apply ty_var0|].
        do 2 rewrite <- (@wk1_ren_on Γ A'); apply convty_wk; [|now symmetry].
        now apply wfc_cons. }
    1,2: eapply ty_id; tea; now symmetry.
    assert [|- Γ,, A]< l > by gen_typing.
    assert [Γ,, A |-[ ta ] A⟨@wk1 Γ A⟩]< l > by now eapply wft_wk. 
    eapply convtm_exp.
    - cbn. eapply redtm_id_beta.
      3: now eapply ty_var0.
      1,2: renToWk; tea; now eapply convty_wk.
    - cbn. 
      assert [Γ,, A |- A'⟨↑⟩ ≅ A⟨↑⟩]< l >
        by (renToWk; symmetry; now eapply convty_wk). 
      eapply redtm_conv; tea.
      eapply redtm_id_beta.
      1: renToWk; now eapply wft_wk.
      1: now eapply lrefl.
      eapply ty_conv. 2: now symmetry.
      now eapply ty_var0.
    - renToWk; tea; now eapply convty_wk.
    - now eapply ty_var0.
    - now eapply ty_var0.
    - renToWk; tea; now eapply convty_wk.
    - eassumption.
  Qed.

  Lemma ty_comp {l Γ A B C f g} :
    [Γ |- A]< l > ->
    [Γ |- B]< l > ->
    [Γ |- C]< l > ->
    [Γ |- g : arr A B]< l > ->
    [Γ |- f : arr B C]< l > ->
    [Γ |- comp A f g : arr A C]< l >.
  Proof.
    intros tyA tyB **. 
    eapply ty_lam; tea.
    assert [|- Γ,, A]< l > by gen_typing.
    pose (r := @wk1 Γ A).
    eapply ty_simple_app; renToWk.
    - unshelve eapply (wft_wk _ _ tyB) ; tea. 
    - now eapply wft_wk.
    - replace (arr _ _) with (arr B C)⟨r⟩ by (unfold r; now bsimpl).
      now eapply ty_wk.
    - eapply ty_simple_app; renToWk.
      + unshelve eapply (wft_wk _ _ tyA) ; tea. 
      + now eapply wft_wk.
      + replace (arr _ _) with (arr A B)⟨r⟩ by (unfold r; now bsimpl).
        now eapply ty_wk.
      + unfold r; rewrite wk1_ren_on; now refine (ty_var _ (in_here _ _)).
  Qed.
  
  Lemma wft_wk1 {l Γ A B} : [Γ |- A]< l > -> [Γ |- B]< l > -> [Γ ,, A |- B⟨↑⟩]< l >.
  Proof.
    intros; renToWk; eapply wft_wk; gen_typing.
  Qed.
  
  Lemma redtm_comp_beta {l Γ A B C f g a} :
    [Γ |- A]< l > ->
    [Γ |- B]< l > ->
    [Γ |- C]< l > ->
    [Γ |- f : arr A B]< l > ->
    [Γ |- g : arr B C]< l > ->
    [Γ |- a : A]< l > ->
    [Γ |- tApp (comp A g f) a ⤳* tApp g (tApp f a) : C]< l >.
  Proof.
    intros hA hB hC hf hg ha.
    eapply redtm_meta_conv.
    1: eapply redtm_beta; tea.
    + eapply ty_simple_app.
      4: eapply ty_simple_app.
      1,2,4,5: eapply wft_wk1; [gen_typing|].
      1: exact hB. 1: exact hC. 1: exact hA. 1: tea.
      1,2: rewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      now eapply ty_var0.
    + cbn; now bsimpl.
    + now asimpl.
  Qed.

  Lemma convtm_comp_app {l Γ A B C f f' g g'} :
    [|- Γ]< l > ->
    [Γ |- A]< l > ->
    [Γ |- B]< l > ->
    [Γ |- C]< l > ->
    [Γ |- C ≅ C]< l > ->
    [Γ |- f : arr A B]< l > ->
    [Γ |- f' : arr A B]< l > ->
    [Γ |- g : arr B C]< l > ->
    [Γ |- g' : arr B C]< l > ->
    [Γ,, A |- tApp g⟨↑⟩ (tApp f⟨↑⟩ (tRel 0)) ≅ tApp g'⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : C⟨↑⟩]< l > ->
    [Γ ,, A |- tApp (comp A g f)⟨↑⟩ (tRel 0) ≅ tApp (comp A g' f')⟨↑⟩ (tRel 0) : C⟨↑⟩]< l >.
  Proof.
    intros.
    eapply convtm_exp.
    - cbn.
      do 2 rewrite <- shift_upRen.
      eapply redtm_comp_beta.
      5: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      4: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      1-3: now eapply wft_wk1.
      now eapply ty_var0.
    - cbn. do 2 rewrite <- shift_upRen.
      eapply redtm_comp_beta.
      5: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      4: erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      1-3: now eapply wft_wk1.
      now eapply ty_var0.
    - now eapply wft_wk1.
    - eapply @ty_simple_app with (A := B⟨↑⟩).
      + now eapply wft_wk1.
      + now eapply wft_wk1.
      + erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      + eapply @ty_simple_app with (A := A⟨↑⟩); [now eapply wft_wk1|now eapply wft_wk1| |now apply ty_var0].
        erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
    - eapply @ty_simple_app with (A := B⟨↑⟩).
      + now eapply wft_wk1.
      + now eapply wft_wk1.
      + erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
      + eapply @ty_simple_app with (A := A⟨↑⟩); [now eapply wft_wk1|now eapply wft_wk1| |now apply ty_var0].
        erewrite <- arr_ren1; renToWk; eapply ty_wk; tea; gen_typing.
    - renToWk; apply convty_wk; gen_typing.
    - assumption.
  Qed.


  Lemma convtm_comp {l Γ A B C f f' g g'} :
    [|- Γ]< l > ->
    [Γ |- A]< l > ->
    [Γ |- A ≅ A]< l > ->
    [Γ |- B]< l > ->
    [Γ |- C]< l > ->
    [Γ |- C ≅ C]< l > ->
    [Γ |- f : arr A B]< l > ->
    [Γ |- f' : arr A B]< l > ->
    [Γ |- g : arr B C]< l > ->
    [Γ |- g' : arr B C]< l > ->
    [Γ,, A |-[ ta ] tApp g⟨↑⟩ (tApp f⟨↑⟩ (tRel 0)) ≅ tApp g'⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : C⟨↑⟩]< l > ->
    [Γ |- comp A g f ≅ comp A g' f' : arr A C]< l >.
  Proof.
    intros.
    assert (Hup : forall X Y h, [Γ |- h : arr X Y]< l > -> [Γ,, A |- h⟨↑⟩ : arr X⟨↑⟩ Y⟨↑⟩]< l >).
    { intros; rewrite <- arr_ren1, <- !(wk1_ren_on Γ A).
      apply (ty_wk (@wk1 Γ A)); [|now rewrite wk1_ren_on].
      now apply wfc_cons. }
    eapply convtm_eta; tea.
    { renToWk; apply wft_wk; [apply wfc_cons|]; tea. }
    2:{ assert [Γ,, A |-[ ta ] tApp g⟨↑⟩ (tApp f⟨↑⟩ (tRel 0)) : C⟨↑⟩]< l >.
        { eapply (ty_simple_app (A := B⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          eapply (ty_simple_app (A := A⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          now apply ty_var0. }
        constructor; tea. }
    3:{ assert [Γ,, A |-[ ta ] tApp g'⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : C⟨↑⟩]< l >.
        { eapply (ty_simple_app (A := B⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          eapply (ty_simple_app (A := A⟨↑⟩)); first [now apply wft_wk1|now apply Hup|idtac].
          now apply ty_var0. }
        constructor; tea. }
    1,2: eapply ty_comp.
    4,5,9,10: tea.
    all: tea.
    eapply convtm_comp_app; cycle 4; tea.
  Qed.

  Lemma typing_eta (l : wfLCon)  (Γ : context) A B f :
    [Γ |- A]< l > ->
    [Γ,, A |- B]< l > ->
    [Γ |- f : tProd A B]< l > ->
    [Γ,, A |- eta_expand f : B]< l >.
  Proof.
    intros ? ? Hf.
    eapply typing_meta_conv.
    eapply ty_app; tea.
    2: refine (ty_var _ (in_here _ _)); gen_typing.
    1: eapply typing_meta_conv; [renToWk; eapply ty_wk; tea;gen_typing|now rewrite wk1_ren_on].
    fold ren_term. bsimpl; rewrite scons_eta'; now asimpl.
  Qed.


  Lemma lambda_cong {l Γ A A' B B' t t'} :
    [Γ |- A]< l > ->
    [Γ |- A']< l > ->
    [Γ,, A |- B]< l > ->
    [Γ,, A |- t : B]< l > ->
    [Γ,, A |- t' : B]< l > ->
    [Γ,, A' |- t' : B']< l > ->
    [Γ |- A ≅ A']< l > ->
    [Γ,, A |- B ≅ B']< l > ->
    [Γ,, A' |- B ≅ B']< l > ->
    [Γ,, A |- t ≅ t' : B]< l > ->
    [Γ |- tLambda A t ≅ tLambda A' t' : tProd A B]< l >.
  Proof.
    intros.
    assert [|- Γ,, A]< l > by gen_typing.
    apply convtm_eta ; tea.
    - gen_typing.
    - constructor; first[now eapply lrefl|tea].
    - eapply ty_conv.
      1: eapply ty_lam ; tea.
      symmetry.
      now eapply convty_prod.
    - constructor; tea.
      now eapply ty_conv.
    - eapply @convtm_exp with (t' := t) (u' := t'); tea.
      3: now eapply lrefl.
      2: eapply redtm_conv ; cbn ; [eapply redtm_meta_conv |..] ; [eapply redtm_beta |..].
      1: eapply redtm_meta_conv ; cbn ; [eapply redtm_beta |..].
      + renToWk.
        now eapply wft_wk.
      + renToWk.
        eapply ty_wk ; tea.
        eapply wfc_cons ; tea.
        now eapply wft_wk.
      + eapply ty_var ; tea.
        now econstructor.
      + bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      + bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      + renToWk.
        now eapply wft_wk.
      + renToWk.
        eapply ty_wk ; tea.
        eapply wfc_cons ; tea.
        now eapply wft_wk.
      + eapply ty_conv.
        1: eapply ty_var0 ; tea.
        renToWk.
        now eapply convty_wk.
      + shelve.
      + bsimpl.
        rewrite scons_eta'.
        now bsimpl.
      + symmetry. eassumption.
      Unshelve.
      bsimpl.
      rewrite scons_eta'.
      now bsimpl.
  Qed.
  
  
  (** *** Lifting determinism properties from untyped reduction to typed reduction. *)

  Lemma redtm_whnf {l Γ t u A} : [Γ |- t ⤳* u : A]< l > -> whnf t -> t = u.
  Proof.
    intros.
    apply (@red_whnf l); [|assumption].
    now eapply redtm_sound.
  Qed.

  Lemma redtmwf_whnf {l Γ t u A} : [Γ |- t :⤳*: u : A]< l > -> whnf t -> t = u.
  Proof.
    intros []; now eapply redtm_whnf.
  Qed.

  Lemma redtmwf_whne {l Γ t u A} : [Γ |- t :⤳*: u : A]< l > -> whne t -> t = u.
  Proof.
    intros ? ?%whnf_whne; now eapply redtmwf_whnf.
  Qed.

  Lemma redty_whnf {l Γ A B} : [Γ |- A ⤳* B]< l > -> whnf A -> A = B.
  Proof.
    intros.
    apply (@red_whnf l); [|eassumption].
    now eapply redty_sound.
  Qed.

  Lemma redtywf_whnf {l Γ A B} : [Γ |- A :⤳*: B]< l > -> whnf A -> A = B.
  Proof.
    intros []; now eapply redty_whnf.
  Qed.

  Lemma redtywf_whne {l Γ A B} : [Γ |- A :⤳*: B]< l > -> whne A -> A = B.
  Proof.
    intros ? ?%whnf_whne; now eapply redtywf_whnf.
  Qed.

  Lemma redtmwf_det {l Γ t u u' A A'} :
    whnf u -> whnf u' ->
    [Γ |- t :⤳*: u : A]< l > -> [Γ |- t :⤳*: u' : A']< l > ->
    u = u'.
  Proof.
    intros ?? [] [].
    eapply whred_det; tea.
    all: now eapply redtm_sound.
  Qed.

  Lemma redtywf_det {l Γ A B B'} :
    whnf B -> whnf B' ->
    [Γ |- A :⤳*: B]< l > -> [Γ |- A :⤳*: B']< l > ->
    B = B'.
  Proof.
    intros ?? [] [].
    eapply whred_det; tea.
    all: now eapply redty_sound.
  Qed.

  (* Unused, consider removing*)
  Lemma whredtm_det l Γ t u u' A A' :
    [Γ |- t ↘ u : A]< l > -> [Γ |- t ↘ u' : A']< l > ->
    u = u'.
  Proof.
    intros [] [].
    eapply whred_det; tea.
    all: now eapply redtm_sound.
  Qed.

  (* Unused, consider removing*)
  Lemma whredty_det l Γ A B B' :
    [Γ |- A ↘ B]< l > -> [Γ |- A ↘ B']< l > ->
    B = B'.
  Proof.
    intros [] [].
    eapply whred_det; tea.
    all: now eapply redty_sound.
  Qed.


  Lemma isWfFun_isFun : forall l Γ A B t, isWfFun l Γ A B t -> isFun t.
  Proof.
  intros * []; constructor; now eapply convneu_whne.
  Qed.

  Lemma isWfPair_isPair : forall l Γ A B t, isWfPair l Γ A B t -> isPair t.
  Proof.
  intros * []; constructor; now eapply convneu_whne.
  Qed.

End GenericConsequences.

#[export] Hint Resolve tyr_wf_l tmr_wf_l well_typed_well_formed : gen_typing.
#[export] Hint Resolve redtywf_wk redtywf_term redtywf_red redtywf_refl redtmwf_wk redtmwf_app redtmwf_refl redtm_beta redtmwf_red redtmwf_natElimZero | 2 : gen_typing.
#[export] Hint Resolve  redtmwf_conv | 6 : gen_typing.
