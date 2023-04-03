(* Function composition *)

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Lemma funcomp_assoc {W X Y Z} (g: Y -> Z) (f: X -> Y) (h: W -> X) :
  funcomp g (funcomp f h) = (funcomp (funcomp g f) h).
Proof.
  reflexivity.
Qed.


(** ** Functor Instances

Exemplary functor instances needed to make Autosubst's generation possible for functors.
Two things are important:
1. The names are fixed.
2. For Coq to check termination, also the proofs have to be closed with Defined.
 *)

(** *** List Instance *)
Require Import List.

Notation "'list_map'" := map.

Definition list_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs, list_map f xs = list_map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition list_id {A}  { f : A -> A} :
  (forall x, f x = x) -> forall xs, list_map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition list_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.

(** *** Prod Instance *)

Definition prod_map {A B C D} (f : A -> C) (g : B -> D) (p : A * B) :
  C * D.
Proof.
  destruct p as [a b]. split.
  exact (f a). exact (g b).
Defined.

Definition prod_id {A B} {f : A -> A} {g : B -> B} :
  (forall x, f x = x) -> (forall x, g x = x) -> forall p, prod_map f g p = p.
Proof.
  intros H0 H1. destruct p. cbn. f_equal; [ apply H0 | apply H1 ].
Defined.

Definition prod_ext {A B C D} {f f' : A -> C} {g g': B -> D} :
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> forall p, prod_map f g p = prod_map f' g' p.
Proof.
  intros H0 H1. destruct p as [a b]. cbn. f_equal; [ apply H0 | apply H1 ].
Defined.

Definition prod_comp {A B C D E F} {f1 : A -> C} {g1 : C -> E} {h1 : A -> E} {f2: B -> D} {g2: D -> F} {h2 : B -> F}:
  (forall x, (funcomp  g1 f1) x = h1 x) -> (forall x, (funcomp g2 f2) x = h2 x) -> forall p, prod_map g1 g2 (prod_map f1 f2 p) = prod_map h1 h2 p.
Proof.
  intros H0 H1. destruct p as [a b]. cbn. f_equal; [ apply H0 | apply H1 ].
Defined.

(* a.d. TODO hints outside of sections without explicit locality are deprecated. Is this even used in the first place?  *)
(* but with 8.13.1 the attribute is forbidden. So what's the correct way to use this? *)
(* #[ global ] *)
Hint Rewrite in_map_iff : FunctorInstances.

(* Declaring the scopes that all our notations will live in *)
Declare Scope fscope.
Declare Scope subst_scope.

Ltac eta_reduce :=
  repeat match goal with
         | [|- context[fun x => ?f x]] => change (fun x => f x) with f (* eta reduction *)
         end.

Ltac minimize :=
  repeat match goal with
         | [|- context[fun x => ?f x]] => change (fun x => f x) with f (* eta reduction *)
         | [|- context[fun x => ?g (?f x)]] => change (fun x => g (f x)) with (funcomp g f) (* funcomp folding *)
         end.

(* had to add this tactic abbreviation because I could not print a setoid_rewrite with the arrow *)
Ltac setoid_rewrite_left t := setoid_rewrite <- t.

Ltac check_no_evars :=
  match goal with
  | [|- ?x] => assert_fails (has_evar x)
  end.

Require Import Setoid Morphisms.

Lemma pointwise_forall {X Y:Type} (f g: X -> Y) :
  (pointwise_relation _ eq f g) -> forall x, f x = g x.
Proof.
  trivial.
Qed.

#[global] Instance funcomp_morphism {X Y Z} :
  Proper (@pointwise_relation Y Z eq ==> @pointwise_relation X Y eq ==> @pointwise_relation X Z eq) funcomp.
Proof.
  cbv - [funcomp].
  intros g0 g1 Hg f0 f1 Hf x.
  unfold funcomp. rewrite Hf, Hg.
  reflexivity.
Qed.

#[global] Instance funcomp_morphism2 {X Y Z} :
  Proper (@pointwise_relation Y Z eq ==> @pointwise_relation X Y eq ==> eq ==> eq) funcomp.
Proof.
  intros g0 g1 Hg f0 f1 Hf ? x ->.
  unfold funcomp. rewrite Hf, Hg.
  reflexivity.
Qed.

Ltac unfold_funcomp := match goal with
                           | |-  context[(funcomp ?f ?g) ?s] => change ((funcomp f g) s) with (f (g s))
                           end.
