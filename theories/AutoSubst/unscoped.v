(** * Autosubst Header for Unnamed Syntax

Version: December 11, 2019.
 *)

(* Adrian:
 I changed this library a bit to work better with my generated code.
 1. I use nat directly instead of defining fin to be nat and using Some/None as S/O
 2. I removed the "s, sigma" notation for scons because it interacts with dependent function types "forall x, A"*)
From LogRel.AutoSubst Require Import core.
Require Import Setoid Morphisms Relation_Definitions.

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition apc {X Y} {f g : X -> Y} {x y : X} (p : f = g) (q : x = y) : f x = g y :=
  match q with eq_refl => match p with eq_refl => eq_refl end end.

(** ** Primitives of the Sigma Calculus. *)

Definition shift  := S.

Definition var_zero := 0.

Definition id {X} := @Datatypes.id X.

Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

#[ export ]
Hint Opaque scons : rewrite.

(** ** Type Class Instances for Notation
Required to make notation work. *)

(** *** Type classes for renamings. *)

Class Ren1 (X1  : Type) (Y Z : Type) :=
  ren1 : X1 -> Y -> Z.

Class Ren2 (X1 X2 : Type) (Y Z : Type) :=
  ren2 : X1 -> X2 -> Y -> Z.

Class Ren3 (X1 X2 X3 : Type) (Y Z : Type) :=
  ren3 : X1 -> X2 -> X3 -> Y -> Z.

Class Ren4 (X1 X2 X3 X4 : Type) (Y Z : Type) :=
  ren4 : X1 -> X2 -> X3 -> X4 -> Y -> Z.

Class Ren5 (X1 X2 X3 X4 X5 : Type) (Y Z : Type) :=
  ren5 : X1 -> X2 -> X3 -> X4 -> X5 -> Y -> Z.

Module RenNotations.
  Notation "s ⟨ xi1 ⟩" := (ren1 xi1 s) (at level 7, left associativity, format "s  ⟨ xi1 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ; xi3 ⟩" := (ren3 xi1 xi2 xi3 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩" := (ren4  xi1 xi2 xi3 xi4 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩" := (ren5  xi1 xi2 xi3 xi4 xi5 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩") : subst_scope.

  Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : fscope.

  Notation "⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2) (at level 1, left associativity, format "⟨ xi1 ; xi2 ⟩") : fscope.
End RenNotations.

(** *** Type Classes for Substiution *)

Class Subst1 (X1 : Type) (Y Z: Type) :=
  subst1 : X1 -> Y -> Z.

Class Subst2 (X1 X2 : Type) (Y Z: Type) :=
  subst2 : X1 -> X2 -> Y  -> Z.

Class Subst3 (X1 X2 X3 : Type) (Y Z: Type) :=
  subst3 : X1 -> X2 -> X3 ->  Y  -> Z.

Class Subst4 (X1 X2 X3 X4: Type) (Y Z: Type) :=
  subst4 : X1 -> X2 -> X3 -> X4 -> Y  -> Z.

Class Subst5 (X1 X2 X3 X4 X5 : Type) (Y Z: Type) :=
  subst5 : X1 -> X2 -> X3 -> X4 -> X5  -> Y  -> Z.

Module SubstNotations.
  Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.

  Notation "s [ sigma ; tau ]" := (subst2 sigma tau s) (at level 7, left associativity, format "s '/' [ sigma ; '/'  tau ]") : subst_scope.
End SubstNotations.

(** *** Type Class for Variables *)

Class Var X Y :=
  ids : X -> Y.

#[global] Instance idsRen : Var nat nat := id.

(** ** Proofs for the substitution primitives. *)

Arguments funcomp {X Y Z} (g)%fscope (f)%fscope.

Module CombineNotations.
  Notation "f >> g" := (funcomp g f) (at level 50) : fscope.

  Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.

  #[ global ]
  Open Scope fscope.
  #[ global ]
  Open Scope subst_scope.
End CombineNotations.

Import CombineNotations.


(** A generic lifting of a renaming. *)
Definition up_ren (xi : nat -> nat) :=
  0 .: (xi >> S).

(** A generic proof that lifting of renamings composes. *)
Lemma up_ren_ren (xi: nat -> nat) (zeta : nat -> nat) (rho: nat -> nat) (E: forall x, (xi >> zeta) x = rho x) :
  forall x, (up_ren xi >> up_ren zeta) x = up_ren rho x.
Proof.
  intros [|x].
  - reflexivity.
  - unfold up_ren. cbn. unfold funcomp. f_equal. apply E.
Qed.

(** Eta laws. *)
Lemma scons_eta' {T} (f : nat -> T) :
  pointwise_relation _ eq (f var_zero .: (funcomp f shift)) f.
Proof. intros x. destruct x; reflexivity. Qed.

Lemma scons_eta_id' :
  pointwise_relation _ eq (var_zero .: shift) id.
Proof. intros x. destruct x; reflexivity. Qed.

Lemma scons_comp' (T: Type) {U} (s: T) (sigma: nat -> T) (tau: T -> U) :
  pointwise_relation _ eq (funcomp tau (s .: sigma)) ((tau s) .: (funcomp tau sigma)).
Proof. intros x. destruct x; reflexivity. Qed.

(* Morphism for Setoid Rewriting. The only morphism that can be defined statically. *)
#[global] Instance scons_morphism {X: Type} :
  Proper (eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq) (@scons X).
Proof.
  intros ? t -> sigma tau H.
  intros [|x].
  cbn. reflexivity.
  apply H.
Qed.

#[global] Instance scons_morphism2 {X: Type} :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq) (@scons X).
Proof.
  intros ? t -> sigma tau H ? x ->.
  destruct x as [|x].
  cbn. reflexivity.
  apply H.
Qed.

(** ** Generic lifting of an allfv predicate *)
Definition up_allfv (p: nat -> Prop) : nat -> Prop := scons True p.

(** ** Notations for unscoped syntax *)
Module UnscopedNotations.
  Include RenNotations.
  Include SubstNotations.
  Include CombineNotations.
  
  (* Notation "s , sigma" := (scons s sigma) (at level 60, format "s ,  sigma", right associativity) : subst_scope. *)

  Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

  Notation "↑" := (shift) : subst_scope.

  #[ global ]
  Open Scope subst_scope.
End UnscopedNotations.

(** ** Tactics for unscoped syntax *)

(** Automatically does a case analysis on a natural number, useful for proofs with context renamings/context morphisms. *)
Tactic Notation "auto_case" tactic(t) :=  (match goal with
                                           | [|- forall (i : nat), _] => intros []; t
                                           end).


(** Generic fsimpl tactic: simplifies the above primitives in a goal. *)
Ltac fsimpl :=
  repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context [id ?s]] => change (id s) with s
         | [|- context[(?f >> ?g) >> ?h]] => change ((f >> g) >> h) with (f >> (g >> h))
         | [|- context[(?v .: ?g) var_zero]] => change ((v .: g) var_zero) with v
         | [|- context[(?v .: ?g) 0]] => change ((v .: g) 0) with v
         | [|- context[(?v .: ?g) (S ?n)]] => change ((v .: g) (S n)) with (g n)
         | [|- context[?f >> (?x .: ?g)]] => change (f >> (x .: g)) with g (* f should evaluate to shift *)
         | [|- context[var_zero]] =>  change var_zero with 0
         | [|- context[?x2 .: (funcomp ?f shift)]] => change (scons x2 (funcomp f shift)) with (scons (f var_zero) (funcomp f shift)); setoid_rewrite (@scons_eta' _ _ f)
         | [|- context[?f var_zero .: ?g]] => change (scons (f var_zero) g) with (scons (f var_zero) (funcomp f shift)); rewrite scons_eta'
         | [|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s)
         | [|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s)
         (* DONE had to put an underscore as the lAst Extra.argument to scons. This might be an argument against unfolding funcomp *)
         | [|- context[funcomp _ (scons _ _)]] => setoid_rewrite scons_comp'; eta_reduce
         | [|- context[scons var_zero shift]] => setoid_rewrite scons_eta_id'; eta_reduce
                        end.