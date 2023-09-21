(** * LogRel.Context: definition of contexts and operations on them.*)
From Coq Require Import ssreflect Morphisms Setoid.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst DirectedDirections.

Set Primitive Projections.

(** ** Context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)

Definition context := list (direction × term).

Notation "'ε'" := (@nil (direction × term)).
Notation " Γ ,, d " := (@cons (direction × term) d Γ) (at level 20, d at next level).
Notation " Γ ,,, Δ " := (@app (direction × term) Δ Γ) (at level 25, Δ at next level, left associativity).

(** States that a definition, correctly weakened, is in a context. *)
Inductive in_ctx : context -> nat -> (direction × term) -> Type :=
  | in_here (Γ : context) d t : in_ctx (Γ,, (d, t)) 0 (d, t⟨↑⟩)
  | in_there (Γ : context) d t d' t' n : in_ctx Γ n (d, t) -> in_ctx (Γ,,(d', t')) (S n) (d, ren_term shift t).

Lemma in_ctx_inj Γ n decl decl' :
  in_ctx Γ n decl -> in_ctx Γ n decl' -> decl = decl'.
Proof.
  induction 1 in decl' |- * ; inversion 1 ; subst.
  1: reflexivity.
  have eq: (d, t) = (d0, t0) by now trivial.
  inversion eq.
  f_equal.
Qed.
