
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst.
From LogRel Require Import DirectedDirections DirectedContext DirectedDirectioning.

Reserved Notation "[ Δ |- w : t -( d )- u : A ]" (at level 0, Δ, d, t, u, A, w at level 50).
Reserved Notation "[ Δ |- ϕ : σ -( )- τ : Θ ]" (at level 0, Δ, Θ, σ, τ, ϕ at level 50).

Definition err_term : term := tApp U U.

Definition action
  (δ: list direction)
  (dt: direction) (t: term) :
  [δ |- t ▹ dt] ->
  forall (σ τ: nat -> term), list term -> term.
Proof.
  induction 1 eqn: eq; intros σ τ l.
  - exact (tLambda U (tRel 0)).
  - exact (List.nth n l err_term).
  - remember d'' as dt. destruct d''.
    (* there might be an error here, the telescope should be modified according to the direction of the domain?? *)
    (* maybe it still work, but its just doing subdirectioning *)
    + pose (tA := IHd1 _ eq_refl σ τ l).
      pose (tB := IHd2 _ eq_refl
                    (scons (tApp tA⟨↑⟩ (tRel 0)) σ)
                    (scons (tRel 0) τ)
                    (cons err_term l)).
      exact (tLambda (tProd A B)[σ] (tLambda A[τ] (
                                         tApp tB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp tA⟨↑⟩⟨↑⟩ (tRel 0)))
            ))).
    + pose (tA := IHd1 _ eq_refl σ τ l).
      pose (tB := IHd2 _ eq_refl
                    (scons (tRel 0) σ)
                    (scons (tApp tA⟨↑⟩ (tRel 0)) τ)
                    (cons err_term l)).
      exact (tLambda (tProd A B)[τ] (tLambda A[σ] (
                                         tApp tB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp tA⟨↑⟩⟨↑⟩ (tRel 0)))
            ))).
    + exact (tLambda (tProd A B)[σ] (tRel 0)).
  - pose (tA := IHd1 _ eq_refl σ τ l).
    remember dA as d''. destruct d''.
    + pose (tt := IHd2 _ eq_refl
                    (scons (tRel 0) σ)
                    (scons (tApp tA⟨↑⟩ (tRel 0)) τ)
                    (cons (tLambda (* TODO FixMe *) err_term (tRel 0)) l)).
      exact (tLambda A[σ] (tLambda A[τ] tt⟨↑⟩)).
    + pose (tt := IHd2 _ eq_refl
                    (scons (tApp tA⟨↑⟩ (tRel 0)) σ)
                    (scons (tRel 0) τ)
                    (cons (tLambda (* TODO FixMe *) err_term (tRel 0)) l)).
      exact (tLambda A[σ] (tLambda A[τ] tt)⟨↑⟩).
    + pose (tt := IHd2 _ eq_refl
                    (scons (tRel 0) σ)
                    (scons (tRel 0) τ)
                    (cons (tLambda A[σ] (* ≅ A[τ]*) (tRel 0)) l)).
      exact (tLambda A[σ] (tLambda A[τ] tt⟨↑⟩)).
  - (* TODO: I think the direction of A is (dir_op dT) *)
    pose (tf := IHd1 _ eq_refl σ τ l).
    exact (tApp (tApp tf a[σ]) a[τ]).
Defined.

Fixpoint compute_dir_and_action
  (δ: list direction) (t: term)
  (σ τ: nat -> term) (ϕ: list term) : (direction × term) :=
  match t with
  | tSort set => (Discr, idterm U)
  | tRel n => (List.nth n δ Discr, List.nth n ϕ err_term)
  | tProd A B =>
      let '(dA, aA) := compute_dir_and_action δ A σ τ ϕ in
      match dA with
      | Discr =>
          let '(dB, aB) := compute_dir_and_action
                             (cons Discr δ)
                             B
                             (scons (tRel 0) σ)
                             (scons (tRel 0) τ)
                             (cons err_term ϕ) in
          match dB with
          | Discr => (Discr, tLambda (tProd A B)[σ] (tRel 0))
          | Fun => (Fun,
                    (tLambda (tProd A B)[σ] (tLambda A[τ] (
                                                 tApp aB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp aA⟨↑⟩⟨↑⟩ (tRel 0)))))))
          | Cofun => (Cofun,
                      (tLambda (tProd A B)[τ] (tLambda A[σ] (
                                                   tApp aB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp aA⟨↑⟩⟨↑⟩ (tRel 0)))))))
          end
      | Fun =>
          let '(dB, aB) := compute_dir_and_action
                             (cons Discr δ)
                             B
                             (scons (tRel 0) σ)
                             (scons (tApp aA⟨↑⟩ (tRel 0)) τ)
                             (cons err_term ϕ) in
          match dB with
          | Fun => (Discr, err_term)
          | Discr | Cofun =>
                      (Cofun, (tLambda (tProd A B)[τ] (tLambda A[σ] (
                                                           tApp aB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp aA⟨↑⟩⟨↑⟩ (tRel 0)))))))
          end
      | Cofun =>
          let '(dB, aB) := compute_dir_and_action
                             (cons Discr δ)
                             B
                             (scons (tApp aA⟨↑⟩ (tRel 0)) σ)
                             (scons (tRel 0) τ)
                             (cons err_term ϕ) in
          match dB with
          | Cofun => (Discr, err_term)
          | Discr | Fun => (Fun,
                    (tLambda (tProd A B)[σ] (tLambda A[τ] (
                                                 tApp aB⟨up_ren ↑⟩ (tApp (tRel 1) (tApp aA⟨↑⟩⟨↑⟩ (tRel 0)))))))
          end
      end
  | tLambda A t =>
      let '(dA, aA) := compute_dir_and_action δ A σ τ ϕ in
      match dA with
      | Discr =>
          let '(dt, at_) := compute_dir_and_action
                             (cons Discr δ)
                             t
                             (scons (tRel 0) σ)
                             (scons (tRel 0) τ)
                             (cons err_term ϕ) in
          (dt, (tLambda A[σ] (tLambda A[τ]⟨↑⟩ at_⟨↑⟩)))
      | Fun =>
          let '(dt, at_) := compute_dir_and_action
                             (cons Discr δ)
                             t
                             (scons (tRel 0) σ)
                             (scons (tApp aA⟨↑⟩ (tRel 0)) τ)
                             (cons err_term ϕ) in
          (dt, (tLambda A[σ] (tLambda A[τ]⟨↑⟩ at_⟨↑⟩)))
      | Cofun =>
          let '(dt, at_) := compute_dir_and_action
                             (cons Discr δ)
                             t
                             (scons (tApp aA⟨↑⟩ (tRel 0)) σ)
                             (scons (tRel 0) τ)
                             (cons err_term ϕ) in
          (dt, (tLambda A[σ] (tLambda A[τ] at_)⟨↑⟩))
      end
  | tApp f a => let '(df, af) := compute_dir_and_action δ f σ τ ϕ in
               (df, (tApp (tApp af a[σ]) a[τ]))
  | _ => (Discr, err_term)
  end.

(* TODO: state this lemma in a different way with direction on compute_DirInfer *)
Lemma compute_action_spec (δ: list direction) (t: term) (σ τ: nat -> term) (ϕ: list term) :
  snd (compute_dir_and_action δ t σ τ ϕ) = match compute_DirInfer δ t with
  | None => err_term
  | Some (d; der) => action δ d t der σ τ ϕ
  end.
Abort.

(* TODO: cleanup *)
Definition compute_action (δ: list direction) (t: term) (σ τ: nat -> term) (ϕ: list term) : term :=
  snd (compute_dir_and_action δ t σ τ ϕ).


From LogRel Require Import Notations Context Weakening GenericTyping.


Section MorphismDefinition.
  Context `{GenericTypingProperties}.

  Fixpoint termRelArr Δ t u A : term :=
    match A with
    | U => arr t u
    | tProd A B => tProd A (termRelArr (Δ ,, A) (eta_expand t) (eta_expand u) B)
    | _ => err_term
    end.

  (* Definition termRel Δ t u d (A : term) : Type := *)
  (*   match d with *)
  (*   | Fun => ∑ f, [ Δ |- f : termRelArr Δ t u A ] *)
  (*   | Cofun => ∑ f, [ Δ |- f : termRelArr Δ u t A ]  *)
  (*   | Discr => [Δ |- t ≅ u : A] *)
  (*   end. *)

  Definition termRelPred Δ t u d (A : term) (f : term) : Type :=
    match d with
    | Fun => [ Δ |- f : termRelArr Δ t u A ]
    | Cofun => [ Δ |- f : termRelArr Δ u t A ]
    | Discr => [Δ |- t ≅ u : A]
    end.

  Definition dispatchDir γ σ τ φ A dA t u :=
    match dA with
    (* Discrete case, A[σ] ≅ A[τ], no transport needed *)
    | Discr => (t, u, A[σ])
    (* Fun case, A @ φ : A[σ] → A[τ] *)
    | Fun => (tApp (compute_action γ A σ τ φ) t, u, A[τ])
    (* Cofun case, A @ φ : A[τ] → A[σ] *)
    | Cofun => (t, tApp (compute_action γ A σ τ φ) u, A[σ])
    end.

  Definition tail (σ : nat -> term) := fun n => σ (S n).

  Fixpoint substRel
    (Δ: Context.context)
    (σ τ : nat -> term)
    (Θ : DirectedContext.context)
    (φ : list term) : Type :=
  match Θ, φ with
  | nil, nil => unit
  | (cons Adecl Θ), (cons w φ) =>
    substRel Δ (tail σ) (tail τ) Θ φ ×
    let '(t',u',A') :=
      dispatchDir (dirs Θ) (tail σ) (tail τ) φ Adecl.(ty) Adecl.(ty_dir) (σ 0) (τ 0)
    in termRelPred Δ t' u' Adecl.(dir) A' w
  | _, _ => False
  end.


End MorphismDefinition.

  Notation "[ Δ |- ϕ : σ -( )- τ : Θ ]" := (substRel Δ σ τ Θ ϕ).
