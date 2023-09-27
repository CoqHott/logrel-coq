(** * LogRel.Context: definition of contexts and operations on them.*)
From Coq Require Import ssreflect Morphisms Setoid.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst DirectedDirections.

Set Primitive Projections.

(** ** Context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)

Record context_decl :=
  { ty: term ;
    ty_dir: direction ; (* merely an invariant *)
    dir: direction ;
  }.

Definition context := list context_decl.

Notation "'ε'" := (@nil context_decl).
Notation " Γ ,, d " := (@cons context_decl d Γ) (at level 20, d at next level).
Notation " Γ ,,, Δ " := (@app context_decl Δ Γ) (at level 25, Δ at next level, left associativity).

(** States that a definition, correctly weakened, is in a context. *)
Inductive in_ctx : context -> nat -> context_decl -> Type :=
  | in_here (Γ : context) T dT d :
    in_ctx (Γ,, {| ty := T; ty_dir := dT; dir := d |}) 0
           {| ty := T⟨↑⟩; ty_dir := dT; dir := d |}
  | in_there (Γ : context) T dT d T' dT' d' n :
    in_ctx Γ n {| ty := T; ty_dir := dT; dir := d |} ->
    in_ctx (Γ,,{| ty := T'; ty_dir := dT'; dir := d' |}) (S n) {| ty := ren_term shift T; ty_dir := dT; dir := d |}.

Lemma in_ctx_inj Γ n decl decl' :
  in_ctx Γ n decl -> in_ctx Γ n decl' -> decl = decl'.
Proof.
  induction 1 in decl' |- * ; inversion 1 ; subst.
  1: reflexivity.
  have eq: {| ty := T; ty_dir := dT; dir := d |}
           = {| ty := T0; ty_dir := dT0; dir := d0 |} by now trivial.
  inversion eq.
  f_equal.
Qed.
