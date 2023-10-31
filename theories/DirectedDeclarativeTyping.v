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
    | wfTypeProd {Γ A dA B dB dT} :
        [ Γ |-( dA ) A ] ->
        [Γ ,, Discr \ A @ dA |-( dB ) B ] ->
        max_dir (dir_op dA) dB dT ->
        [ Γ |-( dT ) tProd A B ]
    | wfTypeUniv {Γ d dU} {A} :
        [ Γ |-( d ) A : U @( dU ) ] ->
        [ Γ |-( d ) A ]
(** **** Typing *)
with TypingDecl : context -> direction -> term -> direction -> term -> Type :=
    | wfVar {Γ d'} {n d T dT} :
        [   |-( ) Γ ] ->
        in_ctx Γ n (d \ T @ dT) ->
        dir_leq d d' ->
        [ Γ |-( d' ) tRel n : T @( dT ) ]
    | wfTermProd {Γ A dA B dB dT} :
        [ Γ |-( dA ) A : U @( Discr ) ] ->
        [Γ ,, Discr \ A @ dA |-( dB ) B : U @( Discr ) ] ->
        max_dir (dir_op dA) dB dT ->
        [ Γ |-( dT ) tProd A B : U @( Discr ) ]
    | wfTermLam {Γ d} {dT A B t} :
        [ Γ |-( dir_op dT ) A ] ->
        [ Γ ,, Discr \ A @ dir_op dT |-( d ) t : B @( dT ) ] ->
        [ Γ |-( d ) tLambda A t : tProd A B @( dT ) ]
    | wfTermApp {Γ d} {dT dB f a A B} :
        [ Γ |-( d ) f : tProd A B @( dT ) ] ->
        [ Γ |-( Discr ) a : A @( dir_op dT ) ] ->
        [ Γ |-(dir_op dT) A ] ->
        [ Γ ,, Discr \ A @ dir_op dT |-(dB) B] ->
        [ Γ |-( d ) tApp f a : B[a..] @( dB ) ]
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


Section Weakening.

  Inductive WellDirWeakening : forall (Γ Δ : context), (nat -> nat) -> Type :=
  | wellDirWkEmpty ρ : WellDirWeakening εᵈ εᵈ ρ
  | wellDirWkStep Γ Δ A ρ :
    WellDirWeakening Γ Δ ρ -> WellDirWeakening (Γ ,, A) Δ (ρ >> S) 
  | wellDirWkUp Γ Δ d d' dA (* TODO : dA' *) A ρ :
    dir_leq d d' ->
    WellDirWeakening Γ Δ ρ -> 
    WellDirWeakening (Γ ,, (d \ A @ dA)⟨ρ⟩) (Δ ,, d' \ A @ dA) (up_ren ρ).

  #[projections(primitive)]
  Record DirWeakening {Γ Δ} := 
    { dir_wk_ren :> nat -> nat ; dir_wk_well : WellDirWeakening Γ Δ dir_wk_ren }.

  Arguments DirWeakening _ _ : clear implicits.

  Notation "Γ ≤ Δ" := (DirWeakening Γ Δ) (at level 40).

  #[global] 
  Instance Ren1_well_dir_wk {Y Z : Type} `{Ren1 (nat -> nat) Y Z} {Γ Δ : context} :
    (Ren1 (Γ ≤ Δ) Y Z) :=
    fun ρ t => t⟨ρ.(dir_wk_ren)⟩.

  Lemma dir_wk_step {Γ Δ} A (ρ : Γ ≤ Δ) : Γ ,, A ≤ Δ.
  Proof. do 2 econstructor; now eapply dir_wk_well. Unshelve. tea. Defined.
  
  Lemma dir_wk_up {Γ Δ} A (ρ : Γ ≤ Δ) : Γ ,, A⟨ρ⟩ ≤ Δ ,, A.
  Proof.
    econstructor; eapply wellDirWkUp.
    1:reflexivity.
    now eapply dir_wk_well.
  Defined.

  Lemma dir_wk_id_mut Γ : ∑ (ρ : Γ ≤ Γ), ρ =1 id. 
  Proof.
    induction Γ.
    - unshelve econstructor.
      + unshelve econstructor.
        1: exact id.
        econstructor.
      + intros; reflexivity.
    - destruct IHΓ as [ρ eq].
      unshelve econstructor.
      + unshelve econstructor.
        1: exact (up_ren ρ).
        assert (eqa : a = a⟨ρ⟩).
        1: destruct a; cbn; f_equal; rewrite eq; now asimpl.
        rewrite {1}eqa.
        econstructor; [reflexivity| eapply dir_wk_well].
      + intros []; cbn; first reflexivity; now rewrite eq.
  Qed.

  Lemma dir_wk_id Γ : Γ ≤ Γ.
  Proof. apply dir_wk_id_mut. Defined.

  Lemma dir_wk_id_eq Γ : dir_wk_id Γ =1 id.
  Proof. unfold dir_wk_id; now destruct (dir_wk_id_mut Γ). Qed.

  Lemma dir_wk1 Γ A : Γ ,, A ≤ Γ.
  Proof. eapply dir_wk_step; eapply dir_wk_id. Defined.

  Lemma dir_wk1_eq Γ A : dir_wk1 Γ A =1 ↑.
  Proof. intros ?; cbn; now rewrite dir_wk_id_eq. Qed.

  Lemma dir_wk_pointwise_tm {Γ Δ} (ρ : Γ ≤ Δ) (τ : nat -> nat) :
    ρ =1 τ -> forall (t : term), t⟨ρ⟩ = t⟨τ⟩.
  Proof.
    intros eq ?; change ?t⟨?ρ⟩ with t⟨ρ.(dir_wk_ren)⟩ at 1; now rewrite eq.
  Qed.

  Lemma dir_wk_pointwise {Γ Δ} (ρ : Γ ≤ Δ) (τ : nat -> nat) :
    ρ =1 τ -> forall t, t⟨ρ⟩ = t⟨τ⟩.
  Proof.
    intros eq []; cbn; f_equal; now rewrite eq.
  Qed.

  Lemma dir_wk1_ren_on Γ A (t : term) : t⟨↑⟩ = t⟨dir_wk1 Γ A⟩.
  Proof. 
    erewrite <-dir_wk_pointwise_tm; first reflexivity.
    eapply dir_wk1_eq.
  Qed.

  Lemma dir_wk_in_ctx {Γ Δ} (ρ : Δ ≤ Γ) : forall {A n}, in_ctx Γ n A -> ∑ d', dir_leq d' A.(dir) × in_ctx Δ (ρ n) (d' \ A.(ty)⟨ρ⟩ @ A.(ty_dir)).
  Proof.
    destruct ρ as [ρ wρ]; induction wρ; cbn; intros B n hin.
    all: change (ty ?A)⟨{| dir_wk_ren := ?ρ ; dir_wk_well := _ |}⟩ with (ty A)⟨ρ⟩.
    - inversion hin.
    - replace (ty B)⟨_⟩ with (ty B)⟨ρ⟩⟨↑⟩ by now asimpl.
      destruct (IHwρ _ _ hin) as [? []].
      eexists; split; tea.
      change (?d \ ?A⟨↑⟩ @ ?dA) with (d \ A @ dA)⟨↑⟩.
      now econstructor.
    - destruct n as [|m]; cbn.
      + inversion hin; subst.
        eexists; split; tea.
        cbn; replace (_ \ _⟨_⟩⟨_⟩ @ _) with (d \ A⟨ρ⟩ @ dA)⟨↑⟩.
        2: cbn; f_equal; cbn; asimpl; reflexivity.
        econstructor.
      + inversion hin; subst.
        destruct (IHwρ _ _ H3) as [dB []].
        eexists; destruct d1 as [B Bdir ?]; split; tea; cbn.
        replace (_ \ _⟨_⟩⟨_⟩ @ _) with (dB \ B⟨ρ⟩ @ Bdir)⟨↑⟩.
        2: cbn; f_equal; cbn; asimpl; reflexivity.
        now econstructor.
  Qed.
        

  Let PCon (Γ : context) := True.
  Let PTy Γ dA A := forall Δ (ρ : Δ ≤ Γ), [|-() Δ] -> [Δ |-(dA) A⟨ρ⟩].
  Let PTm Γ d A dA t := forall Δ (ρ : Δ ≤ Γ), [|-() Δ] -> [Δ |-(d) t⟨ρ⟩ : A⟨ρ⟩ @(dA)].
  Let PTyEq Γ dA A B := forall Δ (ρ : Δ ≤ Γ), [|-() Δ] -> [Δ |-(dA) A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq Γ d A dA t u := forall Δ (ρ : Δ ≤ Γ), [|-() Δ] -> [Δ |-(d) t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ @(dA)].
  
  Theorem dir_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    apply WfDeclInduction; try (intros; exact I).
    - intros ** ???; cbn; now constructor.
    - intros * ? ihA ? ihB ???. cbn. 
      econstructor; tea.
      1: now eapply ihA.
      change B⟨_⟩ with B⟨dir_wk_up (Discr \ A @ dA) ρ⟩.
      eapply ihB.
      econstructor; tea; now eapply ihA.
    - intros * ? ihU ???; econstructor.
      change U with U⟨ρ⟩; eapply ihU; tea.
    - intros ** ???; cbn.
      apply (dir_wk_in_ctx ρ) in H0 as [d'' []].
      econstructor; tea.
      now etransitivity.
    - intros * ? ihA ? ihB ???.
      econstructor; tea; change U with U⟨ρ⟩.
      1: now apply ihA.
      change B⟨_⟩ with B⟨dir_wk_up (Discr \ A @ dA) ρ⟩.
      apply ihB.
      econstructor; tea; econstructor; now eapply ihA.
    - intros * ? ihA ? iht ???.
      econstructor.
      1: now eapply ihA.
      change ?t⟨upRen_term_term _⟩ with t⟨dir_wk_up (Discr \ A @ dir_op dT) ρ⟩.
      eapply iht; econstructor; tea. 
      now eapply ihA.
    - intros * ? ihf ? iha ? ihA ? ihB ???.
      replace B[a..]⟨ρ⟩ with B⟨up_ren ρ⟩[a⟨ρ⟩..].
      2: destruct ρ; cbn; asimpl; reflexivity.
      econstructor.
      + replace (tProd _ _) with (tProd A B)⟨ρ⟩.
        2: cbn; f_equal.
        now eapply ihf.
      + now eapply iha.
      + now eapply ihA.
      + eapply (ihB _ (dir_wk_up (Discr \ A @ dir_op dT) ρ)).
        econstructor; tea.
        now eapply ihA.
    - intros * ? iht ? ihAB ???.
      econstructor.
      1: now eapply iht.
      now eapply ihAB.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

End Weakening.

Section Subdirectionning.
  Let PCon (Γ : context) := True.
  Let PTy Γ dA A := forall dA', dA ⪯ dA' -> [Γ |-(dA') A]. 
  (* Need to strenghen variable cases for more subdirectionning *)
  Let PTm Γ d A dA t := forall d' , d ⪯ d' -> (* dA ⪯ dA' -> *) [Γ |-(d') t : A @(dA)].
  Let PTyEq Γ dA A B := forall dA', dA ⪯ dA' -> [Γ |-(dA') A ≅ B].
  Let PTmEq Γ d A dA t u := forall d' , d ⪯ d' -> (* dA ⪯ dA' -> *) [Γ |-(d') t ≅ u : A @(dA)].
 
  Lemma subdir : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    apply WfDeclInduction; try (intros; exact I). 
    all: unfold PCon, PTy, PTm, PTyEq, PTmEq.
    all: try solve [intros; now econstructor].
    - intros * ? ihA ? ihB ? dT' hdT'; econstructor.
      + eapply ihA; reflexivity.
      + eapply ihB. 
        etransitivity; last exact hdT'.
        now eapply MaxDirProp.upper_bound2.
      + eapply MaxDirProp.max_left; etransitivity; tea.
        now eapply MaxDirProp.upper_bound1.
    - intros **. 
      econstructor; tea.
      now etransitivity.
    - intros * ? ihA ? ihB ?? hdT'; econstructor. 
      + eapply ihA; reflexivity.
      + eapply ihB. 
        etransitivity; last exact hdT'.
        now eapply MaxDirProp.upper_bound2.
      + eapply MaxDirProp.max_left; etransitivity; tea.
        now eapply MaxDirProp.upper_bound1.
    - intros * ? ihA ? ihAB ? ihCD ? hdT'; econstructor.
      (* add the max in the congruence rule for products *)
      admit.
    Admitted.

End Subdirectionning.


(** More derived typing lemmas *)

Lemma wfCtxCons' {Θ d A dA} : 
  [|-() Θ] -> 
  ([|-() Θ] -> [Θ |-(dA) A]) ->
  match d with Discr => unit | _ => is_kind A end ->
  [|-() Θ ,, d \ A @ dA].
Proof.
  intros hΘ hA; destruct d; econstructor; tea; eauto.
Qed.

Lemma wfTypeProd' {Γ d} {A B} :
  [ |-() Γ  ] -> 
  [ Γ |-( dir_op d ) A ] ->
  ( [|-() Γ ,, Discr \ A @ dir_op d] -> 
    [ Γ |-( dir_op d ) A ] ->
    [Γ ,, Discr \ A @ dir_op d |-( d ) B ]) ->
  [ Γ |-( d ) tProd A B ].
Proof.
  intros hΓ hA hB.
  econstructor; tea.
  1: apply hB; tea; now econstructor.
  destruct d; reflexivity.
Qed.


Fixpoint shift_n {A} `{Ren1 (nat -> nat) A A} (t : A) n := match n with 0 => t | S m => (shift_n t m)⟨↑⟩ end.

Lemma wfTypeVar {Θ n d d' dU} :
  [ |-( ) Θ ] ->
  in_ctx Θ n (shift_n (d \ U @ dU) n) ->
  dir_leq d d' ->
  [ Θ |-( d' ) tRel n ].
Proof.
  assert (h : forall k, shift_n (d \ U @ dU) k = (d \ U @ dU)).
  by (intros k; induction k as [| ? ih]; cbn; rewrite ?ih; reflexivity).
  rewrite h.
  intros.
  eapply wfTypeUniv.
  now econstructor.
Qed.



Module Examples.

  #[local]
  Example var_fun : [ εᵈ ,, Discr \ U @ Discr |-( Fun ) tRel 0 ].
  Proof.
    eapply wfTypeVar; repeat econstructor.
  Qed.

  Module List.
  
  (* Context of parameters for list *)
  Definition ctx := εᵈ ,, Fun \ U @ Discr.
  (* Context of arguments for nil; 
    the parameters of list should form a prefix *)
  Definition nil_ctx := ctx.
  (* Not sure how we will represent inductive occurences
    of the inductive being defined so I abstract that 
    as an arbitrary function tList taking |ctx| arguments of type term
    and producing a term for now *)
  Definition cons_ctx (tList : term -> term) := ctx,, Discr \ tRel 0 @ Fun,, Discr \ tList (tRel 1) @ Fun.

  Section ListTyping.

  Lemma ctxWfCtx : [|-() ctx ].
  Proof. repeat econstructor. Qed.

  Lemma nil_ctxWfCtx : [|-() nil_ctx ].
  Proof.  apply ctxWfCtx.  Qed.

  Lemma cons_ctxWfCtx 
    (tList : term -> term)
    (ih : forall Θ A, [Θ |-(Fun) A] -> [Θ |-(Fun) tList A]) :
    [|-() cons_ctx tList ].
  Proof.
    pose ctxWfCtx; eapply wfCtxCons'; [econstructor|intros| easy]; tea.
    - do 2 econstructor; tea; econstructor.
    - eapply ih. 
      eapply wfTypeVar; tea.
      2: reflexivity.
      do 2 econstructor.
  Qed.

  End ListTyping.
  End List.


  Module W.

    Definition ctx := εᵈ ,, Fun \ U @ Discr ,, Cofun \ tProd (tRel 0) U @ Cofun.
    
    Definition sup_ctx 
      (* tW should bind one variable in its second argument *)
      (tW : term -> term -> term) :=
      ctx ,, Discr \ tRel 1 @ Fun ,, Discr \ tProd (tApp (tRel 1) (tRel 0)) (tW (tRel 3) (tApp (tRel 3) (tRel 0))) @ Fun.
    
    Section WTyping.

    Lemma ctxWfCtx : [|-() ctx ].
    Proof.
      eapply wfCtxCons'; [eapply wfCtxCons'|..]; intros.
      1-3,5: unshelve econstructor; tea.
      eapply wfTypeProd'; tea.
      1: eapply wfTypeVar; [tea| repeat econstructor| reflexivity].
      intros; now econstructor.
    Qed.

    Lemma supWfCtx (tW : term -> term -> term) 
      (ih : forall Θ A B, 
        [Θ |-(Fun) A] ->
        [Θ ,, Discr \ A @ Fun |-(Cofun) B ] ->
        [Θ |-(Fun) tW A B]) :
      [|-() sup_ctx tW ].
    Proof.
      eapply wfCtxCons'; [eapply wfCtxCons'|..]; try easy; intros.
      1: apply ctxWfCtx.
      1: eapply wfTypeVar; tea; [do 2 econstructor|reflexivity].
      eapply wfTypeProd'; intros; tea.
      + eapply (wfTypeUniv (dU:=Cofun)).
        change U with (U[(tRel 0)..]).
        eapply (wfTermApp (dT := Cofun) (A:=(tRel 2))).
        all: econstructor; tea; try reflexivity.
        2: econstructor.
        - change (?d \ tProd _ _ @ ?dT) with (shift_n (d \ tProd (tRel 0) U @ dT) 2).
          do 2 econstructor.
        - econstructor ; tea; last reflexivity.
          change (?d \ U @ ?dT) with (shift_n (d \ U @ dT) 3).
          repeat econstructor.
        - econstructor; tea.
          eapply wfTypeVar; tea.
          1: do 3 econstructor.
          reflexivity.
      + set (ctx' := _,, _ ,, _).
        assert [ctx' |-(Fun) tRel 3].
        1:{ eapply wfTypeVar; tea; try reflexivity; repeat econstructor. }
        assert [|-() ctx' ,, Discr \ tRel 3 @ Fun] by now econstructor.
        apply ih; tea.
        eapply (wfTypeUniv (dU:=Cofun)).
        change U with (U[(tRel 0)..]).
        eapply (wfTermApp (dT := Cofun) (A:=(tRel 4))).
        1,2: econstructor; tea; try reflexivity.
        2: econstructor.
        - change (?d \ tProd _ _ @ ?dT) with (shift_n (d \ tProd (tRel 1) U @ dT) 3).
          repeat econstructor.
        - eapply wfTypeVar; tea; last reflexivity.
          repeat econstructor.
        - do 2 econstructor; tea.
          eapply wfTypeVar; tea.
          1: repeat econstructor.
          reflexivity.
    Qed.

    End WTyping.
  End W.  


  Module Composition.
    Definition comp_ctx := 
      εᵈ ,, 
      (* A : *) Cofun \ U @ Discr ,, 
      (* B : *) Discr \ U @ Discr ,,
      (* C : *) Fun \ U @ Discr ,,
      (* f : *) Discr \ arr (tRel 2) (tRel 1) @ Fun ,,
      (* g : *) Discr \ arr (tRel 2) (tRel 1) @ Fun ,,
      (* a : *) Discr \ tRel 4 @ Cofun.
    
    Definition comp_tm := tApp (tRel 1) (tApp (tRel 2) (tRel 0)).

    Lemma wfTypeArr {Γ A dA B dB dT} : 
      [|-() Γ] ->
      [Γ |-(dA) A] ->
      [Γ |-(dB) B] ->
      max_dir (dir_op dA) dB dT ->
      [Γ |-(dT) arr A B].
    Proof.
      intros.
      econstructor; tea.
      rewrite (dir_wk1_ren_on Γ (Discr \ A @ dA) B).
      eapply dir_wk; tea.
      econstructor; tea.
    Qed.

    Lemma comp_ctxWfCtx : [ |-() comp_ctx ].
    Proof.
      repeat eapply wfCtxCons'; try easy; intros; try now constructor.
      - eapply wfTypeArr; tea.
        1,2: eapply wfTypeVar; tea;[repeat econstructor|reflexivity].
        reflexivity.
      - eapply wfTypeArr; tea.
        1,2: eapply wfTypeVar; tea;[repeat econstructor|reflexivity].
        reflexivity.
      - eapply wfTypeVar; tea;[repeat econstructor|reflexivity].
    Qed.

    Lemma wfTermSimpleApp {Γ d} {dT dB f a A B} :
        [|-() Γ] ->
        [ Γ |-( d ) f : arr A B @( dT ) ] ->
        [ Γ |-( Discr ) a : A @( dir_op dT ) ] ->
        [ Γ |-(dir_op dT) A] ->
        [ Γ |-(dB) B] ->
        [ Γ |-( d ) tApp f a : B @( dB ) ].
    Proof.
      intros; rewrite <- (shift_subst_eq B a).
      econstructor; tea.
      rewrite (dir_wk1_ren_on Γ (Discr \ A @ dir_op dT) B).
      eapply dir_wk; tea.
      econstructor; tea.
    Qed.

    Definition a : [ comp_ctx |-(Discr) tRel 0 : tRel 5 @(Cofun) ].
    Proof.
      econstructor; [apply comp_ctxWfCtx| | reflexivity].
      change (?d \ _ @ ?dT) with (shift_n (d \ tRel 4 @ dT) 1).
      econstructor.
    Qed.

    Definition g : [ comp_ctx |-(Discr) tRel 1 : arr (tRel 4) (tRel 3) @(Fun) ].
    Proof.
      econstructor; [apply comp_ctxWfCtx| | reflexivity].
      change (?d \ _ @ ?dT) with (shift_n (d \ arr (tRel 2) (tRel 1)  @ dT) 2).
      repeat econstructor.
    Qed.
    
    Definition f : [ comp_ctx |-(Discr) tRel 2 : arr (tRel 5) (tRel 4) @(Fun) ].
    Proof.
      econstructor; [apply comp_ctxWfCtx| | reflexivity].
      change (?d \ _ @ ?dT) with (shift_n (d \ arr (tRel 2) (tRel 1)  @ dT) 3).
      repeat econstructor.
    Qed.

    Definition A : [comp_ctx |-(Cofun) tRel 5].
    Proof.
      eapply wfTypeVar; [apply comp_ctxWfCtx| | reflexivity].
      repeat econstructor.
    Qed.
    
    Definition B : [comp_ctx |-(Discr) tRel 4].
    Proof.
      eapply wfTypeVar; [apply comp_ctxWfCtx| | reflexivity].
      repeat econstructor.
    Qed.

    Definition C : [comp_ctx |-(Fun) tRel 3].
    Proof.
      eapply wfTypeVar; [apply comp_ctxWfCtx| | reflexivity].
      repeat econstructor.
    Qed.

    Lemma comp_tmWfTerm : [ comp_ctx |-(Discr) comp_tm : tRel 3 @(Fun) ].
    Proof.
      pose comp_ctxWfCtx.
      unfold comp_tm.
      eapply wfTermSimpleApp; tea.
      - eapply g.
      - eapply wfTermSimpleApp; tea.
        + eapply f.
        + eapply a.
        + eapply A.
        + eapply subdir; first eapply B; constructor.
      - eapply subdir; first eapply B; constructor.
      - eapply C.
    Qed.

  End Composition.
  
End Examples.


