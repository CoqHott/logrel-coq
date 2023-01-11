From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening UntypedReduction.

Section RedDefinitions.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Inferring ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeu ta}
    `{!RedType ta} `{!RedTerm ta}.

  Record InferRed (Γ : context) (A t : term) : Type :=
    {
      infty : term ;
      inf_inf :> [Γ |- t ▹ infty] ;
      inf_red :> [Γ |- infty ⇒* A] ;
    }.

  Record TypeRedWhnf (Γ : context) (A B : term) : Type :=
    {
      tyred_whnf_red :> [ Γ |- A ⇒* B ] ;
      tyred_whnf_whnf :> whnf B
    }.

  Record TermRedWhnf (Γ : context) (A t u : term) : Type :=
    {
      tmred_whnf_red :> [ Γ |- t ⇒* u : A ] ;
      tmred_whnf_whnf :> whnf u
    }.

  Record TypeConvWf (Γ : context) (A B : term) : Type :=
    { 
      tyc_wf_l : [Γ |- A] ;
      tyc_wf_r : [Γ |- B] ;
      tyc_wf_conv :> [Γ |- A ≅ B]
    }.

  Record TermConvWf (Γ : context) (A t u : term) : Type :=
    {
      tmc_wf_l : [Γ |- t : A] ;
      tmc_wf_r : [Γ |- u : A] ;
      tmc_wf_conv :> [Γ |- t ≅ u : A]
    }.

  Record TypeRedWf (Γ : context) (A B : term) : Type := {
    tyr_wf_l : [Γ |- A];
    tyr_wf_r : [Γ |- B];
    tyr_wf_red :> [Γ |- A ⇒* B]
  }.

  Record TermRedWf (Γ : context) (A t u : term) : Type := {
    tmr_wf_l : [Γ |- t : A];
    tmr_wf_r : [Γ |- u : A];
    tmr_wf_red :> [Γ |- t ⇒* u : A]
  }.

End RedDefinitions.

Notation "[ Γ |- t ▹h A ]" := (InferRed Γ A t) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ▹h A ]" := (InferRed (ta := ta) Γ A t) : typing_scope.
Notation "[ Γ |- A ↘ B ]" := (TypeRedWhnf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ↘ B ]" := (TypeRedWhnf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t ↘ u : A ]" := (TermRedWhnf Γ A t u) (only parsing ): typing_scope.
Notation "[ Γ |-[ ta  ] t ↘ u : A ]" := (TermRedWhnf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :≅: B ]" := (TypeConvWf Γ A B) (only parsing) : typing_scope.  
Notation "[ Γ |-[ ta  ] A :≅: B ]" := (TypeConvWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :≅: u : A ]" := (TermConvWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :≅: u : A ]" := (TermConvWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :⇒*: B ]" := (TypeRedWf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :⇒*: B ]" := (TypeRedWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :⇒*: u : A ]" := (TermRedWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :⇒*: u : A ]" := (TermRedWf (ta := ta) Γ A t u) : typing_scope.

#[export] Hint Resolve
  Build_InferRed Build_TypeRedWhnf Build_TermRedWhnf Build_TypeConvWf
  Build_TermConvWf Build_TypeRedWf Build_TermRedWf
  : gen_typing.

#[export] Hint Extern 1 =>
  match goal with
    | H : [ _ |- _ ▹h _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ ] |- _ => destruct H
    |  H : [ _ |- _ ↘ _ : _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ ] |- _ => destruct H
    |  H : [ _ |- _ :≅: _ : _] |- _ => destruct H
    |  H : [ _ |- _ :⇒*: _ ] |- _ => destruct H
    |  H : [ _ |- _ :⇒*: _ : _ ] |- _ => destruct H
  end
  : gen_typing.

Section GenericTyping.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta} `{!Inferring ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeu ta}
    `{!RedType ta} `{!RedTerm ta}.

  Class WfContextProperties :=
  {
    wfc_nil : [|- ε ] ;
    wfc_cons {Γ} na {A} : [|- Γ] -> [Γ |- A] -> [|- Γ,,vass na A];
    wfc_wft {Γ A} : [Γ |- A] -> [|- Γ];
    wfc_inf {Γ A t} : [Γ |- t ▹ A] -> [|- Γ] ;
    wfc_ty {Γ A t} : [Γ |- t : A] -> [|- Γ];
    wfc_convty {Γ A B} : [Γ |- A ≅ B] -> [|- Γ];
    wfc_convtm {Γ A t u} : [Γ |- t ≅ u : A] -> [|- Γ];
    wfc_redty {Γ A B} : [Γ |- A ⇒* B] -> [|- Γ];
    wfc_redtm {Γ A t u} : [Γ |- t ⇒* u : A] -> [|- Γ];
  }.

  Class WfTypeProperties :=
  {
    wft_wk {Γ Δ A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A] -> [Δ |- A⟨ρ⟩] ;
    wft_U {Γ} : 
      [ |- Γ ] -> 
      [ Γ |- U ] ;
    wft_prod {Γ} {na : aname} {A B} : 
      [ Γ |- A ] -> 
      [Γ ,, (vass na A) |- B ] -> 
      [ Γ |- tProd na A B ] ;
    wft_term {Γ} {A} :
      [ Γ |- A : U ] -> 
      [ Γ |- A ] ;
  }.

  Class InferringProperties :=
  {
    inf_wk {Γ Δ t A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ▹ A] -> [Δ |- t⟨ρ⟩ ▹ A⟨ρ⟩] ;
    inf_var {Γ} {n decl} :
      [   |- Γ ] ->
      in_ctx Γ n decl ->
      [ Γ |- tRel n ▹ decl.(decl_type) ] ;
    inf_prod {Γ} {na} {A B} :
        [ Γ |- A ▹h U] -> 
        [Γ ,, (vass na A) |- B ▹h U ] ->
        [ Γ |- tProd na A B ▹ U ] ;
    inf_lam {Γ} {na} {A B t} :
        [ Γ |- A ] ->
        [ Γ ,, vass na A |- t ▹ B ] -> 
        [ Γ |- tLambda na A t ▹ tProd na A B] ;
    inf_app {Γ} {na} {f a A B} :
        [ Γ |- f ▹h tProd na A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- tApp f a ▹ B[a ..] ]
  }.

  Class TypingProperties :=
  {
    ty_wk {Γ Δ t A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t : A] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩] ;
    ty_inf {Γ t A A'} : [Γ |- t ▹ A'] -> [Γ |- A' ≅ A] -> [Γ |- t : A] ;
    ty_exp {Γ t A A'} : [Γ |- t : A'] -> [Γ |- A ⇒* A'] -> [Γ |- t : A] ;
    ty_conv {Γ t A A'} : [Γ |- t : A'] -> [Γ |- A' ≅ A] -> [Γ |- t : A] ;
  }.

  Class ConvTypeProperties :=
  {
    convty_term {Γ A B} : [Γ |- A ≅ B : U] -> [Γ |- A ≅ B] ;
    convty_equiv {Γ} :> PER (conv_type Γ) ;
    convty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ≅ B] -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩] ;
    convty_exp {Γ A A' B B'} :
      [Γ |- A ⇒* A'] -> [Γ |- B ⇒* B'] ->
      [Γ |- A' ≅ B'] -> [Γ |- A ≅ B] ;
    convty_uni {Γ} :
      [|- Γ] -> [Γ |- U ≅ U] ;
    convty_prod {Γ na na' A A' B B'} :
      eq_binder_annot na na' -> [Γ |- A] ->
      [Γ |- A ≅ A'] -> [Γ,, vass na A |- B ≅ B'] ->
      [Γ |- tProd na A B ≅ tProd na' A' B'] ;
  }.

  Class ConvTermProperties :=
  {
    convtm_equiv {Γ A} :> PER (conv_term Γ A) ;
    convtm_conv {Γ t u A A'} : [Γ |- t ≅ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ≅ u : A'] ;
    convtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ≅ u : A] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩] ;
    convtm_exp {Γ A A' t t' u u'} :
      [Γ |- A ⇒* A'] -> [Γ |- t ⇒* t' : A'] -> [Γ |- u ⇒* u' : A'] ->
      [Γ |- t' ≅ u' : A'] -> [Γ |- t ≅ u : A] ;
    convtm_convneu {Γ n n' A} :
      [Γ |- n ~ n' ▹ A] -> [Γ |- n ≅ n' : A] ;
    convtm_prod {Γ na na' A A' B B'} :
      eq_binder_annot na na' -> [Γ |- A] ->
      [Γ |- A ≅ A' : U] -> [Γ,, vass na A |- B ≅ B' : U] ->
      [Γ |- tProd na A B ≅ tProd na' A' B' : U] ;
    convtm_eta {Γ na f g A B} :
      [ Γ |- A ] ->
      [ Γ |- f : tProd na A B ] ->
      [ Γ |- g : tProd na A B ] ->
      [ Γ ,, vass na A |- eta_expand f ≅ eta_expand g : B ] ->
      [ Γ |- f ≅ g : tProd na A B ] ;
  }.

  Class ConvNeuProperties :=
  {
    convneu_equiv {Γ A} :> PER (conv_neu Γ A) ;
    (* convneu_conv {Γ t u A A'} : [Γ |- t ~ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ~ u : A'] ; *)
    convneu_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ~ u ▹ A] -> [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ ▹ A⟨ρ⟩] ;
    convneu_var {Γ n A} :
      [Γ |- tRel n : A] -> [Γ |- tRel n ~ tRel n ▹ A] ;
    convneu_app {Γ f g t u na A B} :
      [ Γ |- f ~ g ▹ tProd na A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp f t ≅ tApp g u : B[t..] ]
  }.

  Class RedTypeProperties :=
  {
    redty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ⇒* B] -> [Δ |- A⟨ρ⟩ ⇒* B⟨ρ⟩] ;
    redty_red {Γ A B} :
      [Γ |- A ⇒* B] -> [ A ⇒* B ] ;
    redty_term {Γ A B} :
      [ Γ |- A ⇒* B : U] -> [Γ |- A ⇒* B ] ;
    redty_refl {Γ A} :
      [ Γ |- A] ->
      [Γ |- A ⇒* A] ;
    redty_trans {Γ} :>
      Transitive (red_ty Γ) ;
  }.

  Class RedTermProperties :=
  {
    redtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ⇒* u : A] -> [Δ |- t⟨ρ⟩ ⇒* u⟨ρ⟩ : A⟨ρ⟩] ;
    redtm_red {Γ t u A} : 
      [Γ |- t ⇒* u : A] ->
      [t ⇒* u] ;
    redtm_beta {Γ na A B t u} :
      [ Γ |- A ] ->
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- u : A ] ->
      [ Γ |- tApp (tLambda na A t) u ⇒* t[u..] : B[u..] ] ;
    redtm_app {Γ na A B f f' t} :
      [ Γ |- f ⇒* f' : tProd na A B ] ->
      [ Γ |- t : A ] ->
      [ Γ |- tApp f t ⇒* tApp f' t : B[t..] ];
    redtm_conv {Γ t u A A'} : 
      [Γ |- t ⇒* u : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- t ⇒* u : A'] ;
    redtm_refl {Γ A t } :
      [ Γ |- t : A] ->
      [Γ |- t ⇒* t : A] ;
    redtm_trans {Γ A} :>
      Transitive (red_tm Γ A) ;
  }.

End GenericTyping.

Class GenericTypingProperties `(ta : tag)
  `(WfContext ta) `(WfType ta) `(Typing ta) `(Inferring ta)
  `(ConvType ta) `(ConvTerm ta) `(ConvNeu ta)
  `(RedType ta) `(RedTerm ta) :=
{
  wfc_prop :> WfContextProperties ;
  wfty_prop :> WfTypeProperties ;
  typ_prop :> TypingProperties ;
  convty_prop :> ConvTypeProperties ;
  convtm_prop :> ConvTermProperties ;
  convne_prop :> ConvNeuProperties ;
  redty_prop :> RedTypeProperties ;
  redtm_prop :> RedTermProperties ;
}.

#[export] Hint Immediate wfc_wft wfc_ty wfc_convty wfc_convtm wfc_redty wfc_redtm : gen_typing.
#[export] Hint Resolve wfc_nil wfc_cons wft_wk wft_U wft_prod inf_wk inf_var inf_prod inf_lam inf_app ty_wk ty_inf convty_wk convty_uni convty_prod convtm_wk convtm_prod convtm_eta convneu_wk convneu_var convneu_app redty_wk redty_red redty_term redty_refl redtm_wk redtm_red redtm_beta redtm_app redtm_refl | 2 : gen_typing.
#[export] Hint Resolve wft_term convty_term convtm_convneu | 4 : gen_typing.
#[export] Hint Resolve ty_conv ty_exp convty_exp convtm_exp convtm_conv redtm_conv | 6 : gen_typing.

Section GenericConsequences.
  Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Inferring ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeu ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!WfContextProperties} `{!WfTypeProperties}
  `{!TypingProperties} `{!ConvTypeProperties}
  `{!ConvTermProperties} `{!ConvNeuProperties}
  `{!RedTypeProperties} `{!RedTermProperties}.

  Definition wfredtm_conv {Γ} {t u A B} :
      [Γ |- t :⇒*: u : A] ->
      [Γ |- A ≅ B ] ->
      [Γ |- t :⇒*: u : B].
  Proof.
    intros [wfr wfl red] ?.
    constructor.
    all: gen_typing.
  Qed.

  Lemma redtm_whnf Γ t u A : [Γ |- t ⇒* u : A] -> whnf t -> t = u.
  Proof.
    intros.
    apply red_whnf.
    all: gen_typing.
  Qed.

  Lemma redty_whnf Γ A B : [Γ |- A ⇒* B] -> whnf A -> A = B.
  Proof.
    intros.
    apply red_whnf.
    all: gen_typing.
  Qed.

  Lemma whredtm_det Γ t u u' A A' :
    [Γ |- t ↘ u : A] -> [Γ |- t ↘ u' : A'] ->
    u = u'.
  Proof.
    intros [] [].
    eapply whred_det.
    all: gen_typing.
  Qed.

  Lemma whredty_det Γ A B B' :
    [Γ |- A ↘ B] -> [Γ |- A ↘ B'] ->
    B = B'.
  Proof.
    intros [] [].
    eapply whred_det.
    all: gen_typing.
  Qed.

  Lemma inf_meta_conv (Γ : context) (t A A' : term) :
    [Γ |- t ▹ A] ->
    A' = A ->
    [Γ |- t ▹ A'].
  Proof.
    now intros ? ->.
  Qed.

  Lemma typing_meta_conv (Γ : context) (t A A' : term) :
    [Γ |- t : A] ->
    A' = A ->
    [Γ |- t : A'].
  Proof.
    now intros ? ->.
  Qed.

  Lemma convtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ≅ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma convne_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ≅ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ⇒* u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ⇒* u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

End GenericConsequences.

(*To be able to still use typing/conversion term-directe rules even when the type or the other member of the conversion are not of the right shape*)
Ltac meta_constructor :=
  intros ;
  match goal with
    | |- [_ |- _ ▹ _] => eapply inf_meta_conv
    | |- [_ |- _ ≅ _ : _ ] => eapply convtm_meta_conv
    | |- [_ |- _ ~ _ ▹ _] => eapply convne_meta_conv
    | |- [_ |- _ ⇒* _ : _] => eapply redtm_meta_conv
  end ;
  [ match goal with
    | |- [_ |- tRel _ ▹ _ ] => eapply inf_var 
    | |- [_ |- tProd _ _ _ ▹ _ ] => eapply inf_prod
    | |- [_ |- tLambda _ _ _ ▹ _] => eapply inf_lam
    | |- [_ |- tApp _ _ ▹ _] => eapply inf_app
    | |- [_ |- tProd _ _ _ ≅ _ : _] => eapply convtm_prod
    | |- [_ |- tRel _ ≅ _ : _] => eapply convtm_convneu ; eapply convneu_var
    | |- [_ |- tRel _ ~ _ ▹ _ ] => eapply convneu_var
    | |- [_ |- tApp _ _ ≅ _ : _ ] => eapply convtm_convneu ; eapply convneu_app
    | |- [_ |- tApp _ _ ~ _ ▹ _ ] => eapply convneu_app
    | |- [_ |- tApp (tLambda _ _ _) ⇒* _ : _] => eapply redtm_beta
    | |- [_ |- tApp _ ⇒* _ : _ ] => eapply redtm_app
  end |..].