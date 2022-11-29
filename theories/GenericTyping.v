From Coq Require Import CRelationClasses.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRenameConv PCUICSigmaCalculus PCUICInstConv.
From LogRel Require Import Notations Untyped Weakening.

(* The database used for generic typing *)
Create HintDb gen_typing.
#[global] Hint Constants Opaque : gen_typing.
#[global] Hint Variables Transparent : gen_typing.

Ltac gen_typing := typeclasses eauto 10 with gen_typing typeclass_instances.

Class GenericTypingData (ta : tag) := {
  wfc :> WfContext ta ;
  wf_ty :> WfType ta ;
  ty :> Typing ta ;
  co_ty :> ConvType ta ;
  co_tm :> ConvTerm ta ;
  co_ne :> ConvNeu ta ;
  red_ty :> OneRedType ta ;
  red_tm :> OneRedTerm ta
  }.

Section RedDefinitions.

  Open Scope untagged_scope.

  Context {ta : tag}
    `{wfc : !WfContext ta} `{wf_ty : !WfType ta} `{ty : !Typing ta}
    `{co_ty : !ConvType ta} `{co_tm : !ConvTerm ta} `{co_ne : !ConvNeu ta}
    `{red_ty : !OneRedType ta} `{red_tm : !OneRedTerm ta}.

  Inductive TermRedClosure (Γ : context) : term -> term -> term -> Type :=
      | term_red_id {t A} :
          [ Γ |- t : A ] ->
          [ Γ |- t ⇒* t : A ]
      | term_red_succ {A t t' u} :
          [ Γ |- t ⇒ t' : A ] ->
          [ Γ |- t' ⇒* u : A ] ->
          [ Γ |- t ⇒* u : A ]

  where "[ Γ |- t ⇒* t' : A ]" := (TermRedClosure Γ t t' A).

  Inductive TypeRedClosure (Γ : context) : term -> term -> Type :=
  | type_red_id {A} :
      [ Γ |- A ] ->
      [ Γ |- A ⇒* A]
  | type_red_succ {A A' B} :
      [ Γ |- A ⇒ A' ] ->
      [ Γ |- A' ⇒* B ] ->
      [ Γ |- A ⇒* B ]

  where "[ Γ |- A ⇒* B ]" := (TypeRedClosure Γ A B).

  Record TypeRedWhnf (Γ : context) (A B : term) : Type :=
    {
      tyred_whnf_red :> [ Γ |- A ⇒* B ] ;
      tyred_whnf_whnf :> whnf Γ B
    }.

  Record TermRedWhnf (Γ : context) (t u A : term) : Type :=
    {
      tmred_whnf_red :> [ Γ |- t ⇒* u : A ] ;
      tmred_whnf_whnf :> whnf Γ u
    }.

  Record TypeConvWf (Γ : context) (A B : term) : Type :=
    { 
      tyc_wf_l : [Γ |- A] ;
      tyc_wf_r : [Γ |- B] ;
      tyc_wf_conv :> [Γ |- A ≅ B]
    }.

  Record TermConvWf (Γ : context) (t u A : term) : Type :=
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

  Record TermRedWf (Γ : context) (t u A : term) : Type := {
    tmr_wf_l : [Γ |- t : A];
    tmr_wf_r : [Γ |- u : A];
    tmr_wf_red :> [Γ |- t ⇒* u : A]
  }.

End RedDefinitions.

Notation "[ Γ |- t ⇒* t' : A ]" := (TermRedClosure Γ t t' A) : untagged_scope.
Notation "[ Γ |-[ ta  ] t ⇒* t' : A ]" := (TermRedClosure (ta := ta) Γ t t' A) : tagged_scope.
Notation "[ Γ |- A ⇒* B ]" := (TypeRedClosure Γ A B) : untagged_scope.
Notation "[ Γ |-[ ta  ] A ⇒* B ]" := (TypeRedClosure (ta := ta) Γ A B) : tagged_scope.
Notation "[ Γ |- A ↘ B ]" := (TypeRedWhnf Γ A B) : untagged_scope.
Notation "[ Γ |-[ ta  ] A ↘ B ]" := (TypeRedWhnf (ta := ta) Γ A B) : tagged_scope.
Notation "[ Γ |- t ↘ u : A ]" := (TermRedWhnf Γ t u A) : untagged_scope.
Notation "[ Γ |-[ ta  ] t ↘ u : A ]" := (TermRedWhnf (ta := ta) Γ t u A) : tagged_scope.
Notation "[ Γ |- A :≅: B ]" := (TypeConvWf Γ A B) : untagged_scope.  
Notation "[ Γ |-[ ta  ] A :≅: B ]" := (TypeConvWf (ta := ta) Γ A B) : tagged_scope.
Notation "[ Γ |- t :≅: u : A ]" := (TermConvWf Γ t u A) : untagged_scope.
Notation "[ Γ |-[ ta  ] t :≅: u : A ]" := (TermConvWf (ta := ta) Γ t u A) : tagged_scope.
Notation "[ Γ |- A :⇒*: B ]" := (TypeRedWf Γ A B) : untagged_scope.
Notation "[ Γ |-[ ta  ] A :⇒*: B ]" := (TypeRedWf (ta := ta) Γ A B) : tagged_scope.
Notation "[ Γ |- t :⇒*: u : A ]" := (TermRedWf Γ t u A) : untagged_scope.
Notation "[ Γ |-[ ta  ] t :⇒*: u : A ]" := (TermRedWf (ta := ta) Γ t u A) : tagged_scope.


#[export] Hint Resolve
  term_red_id term_red_succ type_red_id type_red_succ
  Build_TypeRedWhnf Build_TermRedWhnf Build_TypeConvWf
  Build_TermConvWf Build_TypeRedWf Build_TermRedWf
  : gen_typing.

#[export] Hint Extern 1 =>
  match goal with
    |  H : [ _ |- _ ↘ _ ]%untagged |- _ => destruct H
    |  H : [ _ |- _ ↘ _ : _ ]%untagged |- _ => destruct H
    |  H : [ _ |- _ :≅: _ ]%untagged |- _ => destruct H
    |  H : [ _ |- _ :≅: _ : _]%untagged |- _ => destruct H
    |  H : [ _ |- _ :⇒*: _ : _ ]%untagged |- _ => destruct H
  end
  : gen_typing.

Section GenericTyping.

  Open Scope untagged_scope.

  Context {ta : tag}
    `{wfc : !WfContext ta} `{wf_ty : !WfType ta} `{ty : !Typing ta}
    `{co_ty : !ConvType ta} `{co_tm : !ConvTerm ta} `{co_ne : !ConvNeu ta}
    `{red_ty : !OneRedType ta} `{red_tm : !OneRedTerm ta}.

  Class WfContextProp :=
  {
    wfc_nil : [|- []] ;
    wfc_cons {Γ na A} : [|- Γ] -> [Γ |- A] -> [|- Γ,,vass na A]
  }.

  Class WfTypeProp :=
  {
    wft_wk {Γ Δ A} (ρ : Γ ≤ Δ) :
      [Γ |- A] -> [Δ |- A.[ren ρ]] ;
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

  Class TypingProp :=
  {
    ty_wk {Γ Δ t A} (ρ : Γ ≤ Δ) :
      [Γ |- t : A] -> [Δ |- t.[ren ρ] : A.[ren ρ]] ;
    ty_var {Γ} {n decl} :
      [   |- Γ ] ->
      nth_error Γ n = Some decl ->
      [ Γ |- tRel n : lift0 (S n) decl.(decl_type) ] ;
    ty_prod {Γ} {na} {A B} :
        [ Γ |- A : U] -> 
        [Γ ,, (vass na A) |- B : U ] ->
        [ Γ |- tProd na A B : U ] ;
    ty_lam {Γ} {na} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, vass na A |- t : B ] -> 
        [ Γ |- tLambda na A t : tProd na A B] ;
    ty_app {Γ} {na} {f a A B} :
        [ Γ |- f : tProd na A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- tApp f a : B{0 := a} ] ;
    ty_conv {Γ t A A'} : [Γ |- t : A] -> [Γ |- A ≅ A'] -> [Γ |- t : A'] ;
  }.

  Class ConvTypeProp :=
  {
    convty_term {Γ A B} : [Γ |- A ≅ B : U] -> [Γ |- A ≅ B] ;
    convty_equiv {Γ} :> PER (fun A B => [Γ |- A ≅ B]) ;
    convty_wk {Γ Δ A B} (ρ : Γ ≤ Δ) :
      [Γ |- A ≅ B] -> [Δ |- A.[ren ρ] ≅ B.[ren ρ]] ;
    convty_whexp {Γ A A' B B'} :
      [Γ |- A ⇒* A'] -> [Γ |- B ⇒* B'] ->
      [Γ |- A' ≅ B'] -> [Γ |- A ≅ B] ;
    convty_uni {Γ} :
      [Γ |- U ≅ U] ;
    convty_prod {Γ na na' A A' B B'} :
      eq_binder_annot na na' ->
      [Γ |- A ≅ A'] -> [Γ,, vass na A |- B ≅ B'] ->
      [Γ |- tProd na A B ≅ tProd na' A' B'] ;
  }.

  Class ConvTermProp :=
  {
    convtm_equiv {Γ A} :> PER (fun t u => [Γ |- t ≅ u : A]) ;
    convtm_conv {Γ t u A A'} : [Γ |- t ≅ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ≅ u : A'] ;
    convtm_wk {Γ Δ t u A} (ρ : Γ ≤ Δ) :
      [Γ |- t ≅ u : A] -> [Δ |- t.[ren ρ] ≅ u.[ren ρ] : A.[ren ρ]] ;
    convtm_whexp {Γ A A' t t' u u'} :
      [Γ |- A ⇒* A'] -> [Γ |- t ⇒* t' : A'] -> [Γ |- u ⇒* u' : A'] ->
      [Γ |- t' ≅ u' : A'] -> [Γ |- t ≅ u : A] ;
    convtm_convneu {Γ n n' A} :
      [Γ |- n ~ n' : A] -> [Γ |- n ≅ n' : A] ;
    convtm_prod {Γ na na' A A' B B'} :
      eq_binder_annot na na' ->
      [Γ |- A ≅ A' : U] -> [Γ,, vass na A |- B ≅ B' : U] ->
      [Γ |- tProd na A B ≅ tProd na' A' B' : U] ;
    convtm_eta {Γ na f g A B} :
      [ Γ |- A ] ->
      [ Γ |- f : tProd na A B ] ->
      [ Γ |- g : tProd na A B ] ->
      [ Γ ,, vass na A |- eta_expand f ≅ eta_expand g : B ] ->
      [ Γ |- f ≅ g : tProd na A B ] ;
  }.

  Class ConvNeuProp :=
  {
    convneu_equiv {Γ A} :> PER (fun t u => [Γ |- t ~ u : A]) ;
    convneu_conv {Γ t u A A'} : [Γ |- t ~ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ~ u : A'] ;
    convneu_wk {Γ Δ t u A} (ρ : Γ ≤ Δ) :
      [Γ |- t ~ u : A] -> [Δ |- t.[ren ρ] ~ u.[ren ρ] : A.[ren ρ]] ;
    convneu_var {Γ n A} :
      [Γ |- tRel n : A] -> [Γ |- tRel n ~ tRel n : A] ;
    convneu_app {Γ f g t u na A B} :
        [ Γ |- f ~ g : tProd na A B ] ->
        [ Γ |- t ≅ u : A ] ->
        [ Γ |- tApp f t ≅ tApp g u : B{0 := t} ]
  }.

  Class OneRedTypeProp :=
  {
    oredty_whnf {Γ N A} :
      whnf Γ N -> [Γ |- N ⇒ A] -> False ;
    oredty_det {Γ T U V} :
      [Γ |- T ⇒ U] -> [Γ |- T ⇒ V] ->
      U = V ;
    oredty_term {Γ A B} :
    [Γ |- A ⇒ B : U] -> [Γ |- A ⇒ B]
  }.

  Class OneRedTermProp :=
  {
    oredtm_whnf {Γ n u A} :
      whnf Γ n -> [Γ |- n ⇒ u : A] -> False ;
    oredtm_det {Γ A B t u v} :
      [Γ |- t ⇒ u : A] -> [Γ |- t ⇒ v : B] ->
      u = v ;
    oredtm_beta {Γ na A B t u} :
      [ Γ |- A ] ->
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- u : A ] ->
      [ Γ |- tApp (tLambda na A t) u ≅ t{0 := u} : B{0 := u} ] ;
    oredtm_app {Γ na A B f f' t} :
      [ Γ |- f ⇒ f' : tProd na A B ] ->
      [ Γ |- t : A ] ->
      [ Γ |- tApp f t ⇒ tApp f' t : B{0 := t} ];
    oredtm_conv {Γ t u A A'} : 
      [Γ |- t ⇒ u : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- t ⇒ u : A']
  }.

End GenericTyping.


Class GenericTypingProp `(ta : tag)
  `(WfContext ta) `(WfType ta) `(Typing ta)
  `(ConvType ta) `(ConvTerm ta) `(ConvNeu ta)
  `(OneRedType ta) `(OneRedTerm ta) :=
{
  wfc_prop :> WfContextProp ;
  wfty_prop :> WfTypeProp ;
  typ_prop :> TypingProp ;
  convty_prop :> ConvTypeProp ;
  convtm_prop :> ConvTermProp ;
  convne_prop :> ConvNeuProp ;
  redty_prop :> OneRedTypeProp ;
  redtm_prop :> OneRedTermProp ;
}.

#[export] Hint Resolve wfc_nil wfc_cons wft_wk wft_U wft_prod ty_wk ty_var ty_prod ty_lam ty_app convty_wk convty_uni convty_prod convtm_wk convtm_prod convtm_eta convneu_wk convneu_var convneu_app oredty_term oredtm_beta oredtm_app | 2 : gen_typing.
#[export] Hint Resolve wft_term ty_conv convty_term convtm_conv convneu_conv oredtm_conv | 4 : gen_typing.

Section GenericConsequences.
  Context {ta : tag}
  `{wfc : !WfContext ta} `{wf_ty : !WfType ta} `{ty : !Typing ta}
  `{co_ty : !ConvType ta} `{co_tm : !ConvTerm ta} `{co_ne : !ConvNeu ta}
  `{ored_ty : !OneRedType ta} `{ored_tm : !OneRedTerm ta}
  `{GenericTypingProp}.
  Open Scope untagged_scope.

  Definition mredtm_conv {Γ t u A B} :
      [Γ |- t ⇒* u : A] ->
      [Γ |- A ≅ B] ->
      [Γ |- t ⇒* u : B].
  Proof.
    induction 1.
    all: econstructor ; gen_typing.
  Qed.

  Definition wfredtm_conv {Γ} {t u A B} :
      [Γ |- t :⇒*: u : A] ->
      [Γ |- A ≅ B] ->
      [Γ |- t :⇒*: u : B].
  Proof.
    intros [wfr wfl red] ?.
    constructor.
    1-2: gen_typing.
    clear wfr wfl.
    induction red ; gen_typing.
  Qed.

  Lemma mredtm_whnf Γ t u A : [Γ |- t ⇒* u : A] -> whnf Γ t -> t = u.
  Proof.
    intros [] ?.
    1: reflexivity.
    exfalso.
    eauto using oredtm_whnf.
  Qed.

  Corollary mredty_whnf Γ A B : [Γ |- A ⇒* B] -> whnf Γ A -> A = B.
  Proof.
    intros [] ?.
    1: reflexivity.
    exfalso.
    now eauto using oredty_whnf.
  Qed.

  Lemma whredtm_mredtm_det Γ t u u' A A' :
  [Γ |- t ↘ u : A] -> [Γ |- t ⇒* u' : A'] ->
  [Γ |- u' ↘ u : A].
  Proof.
    intros [red whnf] red'.
    induction red in whnf, A', u', red' |- *.
    - constructor ; tea.
      eapply mredtm_whnf in red' as -> ; tea.
      now econstructor.
    - destruct red' as [? | ? ? ? ? o'].
      + econstructor.
        2: gen_typing.
        now econstructor.
      + unshelve epose proof (oredtm_det o o') as <-.
        now eapply IHred.
  Qed.

  Corollary whredtm_det Γ t u u' A A' :
    [Γ |- t ↘ u : A] -> [Γ |- t ↘ u' : A'] ->
    u = u'.
  Proof.
    intros red [].
    eapply whredtm_mredtm_det in red as [] ; tea.
    symmetry.
    now eapply mredtm_whnf.
  Qed.

  Lemma whredty_mredty_det Γ A B B' :
    [Γ |- A ↘ B] -> [Γ |- A ⇒* B'] ->
    [Γ |- B' ↘ B].
  Proof.
    intros [red whnf] red'.
    induction red in whnf, B', red' |- *.
    - eapply mredty_whnf in red' as -> ; tea.
      gen_typing.
    - destruct red' as [| ? ? ? red'].
      1: gen_typing.
      now epose proof (oredty_det o red') as <-.
  Qed.

  Corollary nred_det_ty Γ A B B' :
    [Γ |- A ↘ B] -> [Γ |- A ↘ B'] ->
    B = B'.
  Proof.
    intros red [].
    eapply whredty_mredty_det in red as [] ; tea.
    symmetry.
    now eapply mredty_whnf.
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
    now intros ? ->.
  Qed.

  Lemma convne_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ≅ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A'].
  Proof.
    now intros ? ->.
  Qed.

End GenericConsequences.


(*To be able to still use typing/conversion term-directe rules even when the type or the other member of the conversion are not of the right shape*)
Ltac meta_constructor :=
  intros ;
  match goal with
    | |- [_ |- _ : _]%untagged => eapply typing_meta_conv
    | |- [_ |- _ ≅ _ : _ ]%untagged => eapply convtm_meta_conv
    | |- [_ |- _ ~ _ : _]%untagged => eapply convne_meta_conv
  end ;
  [ match goal with
    | |- [_ |- tRel _ : _ ]%untagged => eapply ty_var 
    | |- [_ |- tLambda _ _ _ : _]%untagged => eapply ty_lam
    | |- [_ |- tApp _ _ : _]%untagged => eapply ty_app
    | |- [_ |- tProd _ _ _ ≅ _ : _]%untagged => eapply convtm_prod
    | |- [_ |- tRel _ ≅ _ : _]%untagged => eapply convtm_convneu ; eapply convneu_var
    | |- [_ |- tRel _ ~ _ : _ ]%untagged => eapply convneu_var
    | |- [_ |- tApp _ _ ≅ _ : _ ]%untagged => eapply convtm_convneu ; eapply convneu_app
    | |- [_ |- tApp _ _ ~ _ : _ ]%untagged => eapply convneu_app
  end |..].