From MetaCoq Require Import utils.

Definition iff (A B : Type) :=
  (A -> B) × (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.