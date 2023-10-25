
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping DeclarativeInstance Weakening GenericTyping. (* DeclarativeSubst*)
From LogRel Require Import DirectedDirections DirectedContext DirectedDirectioning DirectedTyping. 
(* DirectedErasure DirectedDeclarativeTyping . *)


Reserved Notation "[ Δ |- w : t -( d )- u : A ]" (at level 0, Δ, d, t, u, A, w at level 50).
Reserved Notation "[ Δ |- ϕ : σ -( )- τ : Θ ]" (at level 0, Δ, Θ, σ, τ, ϕ at level 50).

(* Import DeclarativeTypingData.
Import DeclarativeTypingProperties.
Import Notations. *)

(* Definition witType (d: direction) :=
  match d with
  | Fun | Cofun => term
  | Discr => unit
  end. *)

Definition err_term : term := tApp U U.

Section MorphismDefinition.
  Context `{GenericTypingProperties}.

  Inductive TermRel (Δ: Context.context) (t u: term) : forall (d: direction), term -> term -> Type :=
  | termRelFun { f } :
    [ Δ |- f : arr t u ] ->
    [ Δ |- f : t -( Fun )- u : U ]
  | termRelCofun { f } :
    [ Δ |- f : arr u t ] ->
    [ Δ |- f : t -( Cofun )- u : U ]
  | termRelDiscr { A } :
    [ Δ |- t ≅ u : A ] ->
    [ Δ |- err_term : t -( Discr )- u : A ]
  | termRelPiFun { A B w }:
    (* KM: I'm a bit skeptical that this typing premise should be needed.
        This relation should assume that the type is well-formed and comes with all the inversion lemmas needed *)
    [ Δ |- A ] ->
    [ Δ ,, A |- w : tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Fun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
    [ Δ |- tLambda A w : t -( Fun )- u : tProd A B ]
  | termRelPiCofun { A B w }:
    [ Δ |- A ] ->
    [ Δ ,, A |- w : tApp t⟨@wk1 Δ A⟩ (tRel 0) -( Cofun )- tApp u⟨@wk1 Δ A⟩ (tRel 0) : B ] ->
    [ Δ |- tLambda A w : t -( Cofun )- u : tProd A B ]

  where "[ Δ |- w : t -( d )- u : A ]" := (TermRel Δ t u d A w).

  Context (type_act : forall (γ : list direction) (dA : direction) (A : term) (wdA : [γ |- A ◃ dA]) (φ : list term), term).

  (* Given a context of directions γ coming from Θ,
    substitutions, Δ |- σ, τ : |Θ|,
    a morphism Δ |- φ : σ ⇒ τ : Θ,
    a type |Θ| |- A, terms Δ |- t : A[σ], Δ |- u : A[τ],
    returns the adequate triple (t',u', A') by acting
    on t/u and substituting A according to the direction dA of A *)
  Definition dispatch_dir γ σ τ φ A dA wdA t u :=
    match dA with
    (* Discrete case, A[σ] ≅ A[τ], no transport needed *)
    | Discr => (t, u, A[σ]) 
    (* Fun case, A @ φ : A[σ] → A[τ] *)
    | Fun => (tApp (type_act γ dA A wdA φ) t, u, A[τ])
    (* Cofun case, A @ φ : A[τ] → A[σ] *)
    | Cofun => (t, tApp (type_act γ dA A wdA φ) u, A[σ])
    end.

  Inductive SubstRel (Δ: Context.context) :
    (nat -> term) -> (nat -> term) -> DirectedContext.context -> list term -> Type :=
  | substRelSEmpty : forall σ τ, [ Δ |- nil : σ -( )- τ : nil ]
  | substRelSCons {Θ σ τ φ A dA t u w d} (wdA : [dirs Θ |- A ◃ dA]) 
    (tuA := dispatch_dir (dirs Θ) σ τ φ A dA wdA t u) (t':= fst tuA) (u' := fst (snd tuA)) (A' := snd (snd tuA)):
    [ Δ |- φ : σ -( )- τ : Θ] ->
    [ Δ |- w : t' -( d )- u' : A' ] ->
    [ Δ |- (w :: φ) : (t .: σ) -( )- (u .: τ) : (Θ ,,  d \ A @ dA)]
  where "[ Δ |- ϕ : σ -( )- τ : Θ ]" := (SubstRel Δ σ τ Θ ϕ).

  
End MorphismDefinition.
  



(* Definition TermRel_actionType {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : *)
(*   match d with Fun | Cofun => term | Discr => unit end. *)
(* Proof. *)
(*   induction rel. *)
(*   - exact (arr t u). *)
(*   - exact (arr u t). *)
(*   - exact tt. *)
(*   - exact (tProd A IHrel). *)
(*   - exact (tProd A IHrel). *)
(* Defined. *)

(* Definition TermRel_action_concl {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : Type. *)
(* Proof. *)
(*   destruct d. *)
(*   - exact (∑(w: term), [ Δ |- w : TermRel_actionType rel ]). *)
(*   - exact (∑(w: term), [ Δ |- w : TermRel_actionType rel ]). *)
(*   - exact [ Δ |- t ≅ u : A ]. *)
(* Defined. *)

(* Definition TermRel_action {Δ d t u A} (rel: [ Δ |- t -( d )- u : A ]) : TermRel_action_concl rel. *)
(* Proof. *)
(*   depind rel; simpl. *)
(*   - exists f. assumption. *)
(*   - exists f. assumption. *)
(*   - assumption. *)
(*   - destruct IHrel as [v H]. *)
(*     exists (tLambda A v). now constructor. *)
(*   - destruct IHrel as [v H]. *)
(*     exists (tLambda A v). now constructor. *)
(* Defined. *)

(* Lemma TermRel_Fun_is_kind {Δ t u A} : *)
(*   [ Δ |- t -( Fun )- u : A ] -> DirectedDeclarativeTyping.is_kind A. *)
(* Proof. *)
(*   intro h. *)
(*   depind h. *)
(*   all: try inversion H. *)
(*   all: by cbn. *)
(* Qed. *)

(* Lemma TermRel_Cofun_is_kind {Δ t u A} : *)
(*   [ Δ |- t -( Cofun )- u : A ] -> DirectedDeclarativeTyping.is_kind A. *)
(* Proof. *)
(*   intro h. *)
(*   depind h. *)
(*   all: try inversion H. *)
(*   all: by cbn. *)
(* Qed. *)

(* Lemma TermRel_WellTyped {Δ t u d A} : *)
(*   [ Δ |- t -( d )- u : A ] -> [ Δ |- t : A ] × [ Δ |- u : A ]. *)
(* Proof. *)
(*   induction 1. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)

(* Definition witList := list (∑ (d: direction), witType d).

Inductive SubstRel (Δ: context) :
  (nat -> term) -> (nat -> term) -> DirectedContext.context -> witList -> Type :=
| substRelSEmpty : forall σ τ, [ Δ |- nil : σ -( )- τ : nil ]
| substRelSConsDiscr : forall σ τ Θ d A ϕ w,
    [ Δ |- ϕ : (↑ >> σ) -( )- (↑ >> τ) : Θ ] ->
    [ Δ |- A[↑ >> σ] ≅ A[↑ >> τ] ] ->
    [ Δ |- w : (σ var_zero) -( d )- (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- cons (d; w) ϕ : σ -( )- τ : cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Discr;
                      DirectedContext.dir := d |} Θ ]
| substRelSConsFun : forall σ τ Θ d A f ϕ w,
    [ Δ |- ϕ : (↑ >> σ) -( )- (↑ >> τ) : Θ ] ->
    [ Δ |- f : arr A[↑ >> σ] A[↑ >> τ] ] ->
    [ Δ |- w : tApp f (σ var_zero) -( d )- (τ var_zero) : A[↑ >> τ] ] ->
    [ Δ |- cons (d; w) ϕ : σ -( )- τ : cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Fun ;
                      DirectedContext.dir := d |} Θ ]
| substRelSConsCofun : forall σ τ Θ d A f ϕ w,
    [ Δ |- ϕ : (↑ >> σ) -( )- (↑ >> τ) : Θ ] ->
    [ Δ |- f : arr A[↑ >> τ] A[↑ >> σ] ] ->
    [ Δ |- w : (σ var_zero) -( d )- tApp f (τ var_zero) : A[↑ >> σ] ] ->
    [ Δ |- cons (d; w) ϕ : σ -( )- τ : cons {| DirectedContext.ty := A;
                      DirectedContext.ty_dir := Cofun ;
                      DirectedContext.dir := d |} Θ ]
where "[ Δ |- ϕ : σ -( )- τ : Θ ]" := (SubstRel Δ σ τ Θ ϕ). *)

(* Lemma TermRel_WellSubst_l {Δ σ τ Θ} : *)
(*   [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s σ : erase_dir Θ ]. *)
(* Proof. *)
(*   induction 1. *)
(*   - constructor. *)
(*   - constructor; tea. *)
(*     unshelve eapply (fst (TermRel_WellTyped _)). *)
(*     3: eassumption. *)
(*   - constructor; tea. *)
(*     admit. *)
(*   - admit. *)
(* Admitted. *)


(* Lemma TermRel_WellSubst_r {Δ σ τ Θ} : *)
(*   [ Δ |- σ -( Θ )- τ ] -> [ Δ |-s τ : erase_dir Θ ]. *)
(* Proof. *)
(* Admitted. *)


