(** * LogRel.Context: definition of contexts and operations on them.*)
From Coq Require Import ssreflect Morphisms Setoid.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst DirectedDirections.

Set Primitive Projections.

(** ** Directed context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)

Record context_decl :=
  { ty: term ;
    ty_dir: direction ; (* merely an invariant *)
    dir: direction ;
  }.

Notation "d \ A @ dA " := {| ty := A ; ty_dir := dA ; dir := d |} (at level 15).

Definition context := list context_decl.

Definition tys := List.map ty.
Definition dirs := List.map dir.
Definition ty_dirs := List.map ty_dir.

(* For in_ctx *)
#[global]
Instance: Ren1 (nat -> nat) context_decl context_decl := 
  fun ρ Θ => dir Θ \ (ty Θ)⟨ρ⟩ @ ty_dir Θ.

Notation "'εᵈ'" := (@nil context_decl).
