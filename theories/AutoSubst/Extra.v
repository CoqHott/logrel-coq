From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils.

Export UnscopedNotations.
#[global] Open Scope subst_scope.

#[global] Instance Ren1_subst {Y Z : Type} `{Ren1 (nat -> nat) Y Z} :
  (Ren1 (nat -> nat) (nat -> Y) (nat -> Z)) :=
  fun ρ σ i => (σ i)⟨ρ⟩.

Ltac fold_autosubst :=
    change ren_term with (@ren1 _ _ _ Ren_term) in * ;
    change subst_term with (@subst_term _ _ _ Subst_term) in *;
    change (fun i => (?σ i)⟨?ρ⟩) with (@ren1 _ _ _ Ren1_subst ρ σ) in *.

Smpl Add fold_autosubst : refold.

Arguments ren1 {_ _ _}%type_scope {Ren1} _ !_/.
(* Ideally, we'd like Ren_term to not be there, and ren_term to be directly the Ren1 instance…*)
Arguments Ren_term _ _ /.
Arguments Ren1_subst {_ _ _} _ _/.