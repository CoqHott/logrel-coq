(** Declarative Typing *)
(* The context Γ is well-formed *)
Reserved Notation "[   |- Γ ]" (at level 0, Γ at level 50).
(* The type A is well-formed in Γ *)
Reserved Notation "[ Γ |- A ]" (at level 0, Γ, A at level 50).
(* The term t has type A in Γ *)
Reserved Notation "[ Γ |- t : A ]" (at level 0, Γ, t, A at level 50).
(* Types A and B are (declaratively) convertible in Γ *)
Reserved Notation "[ Γ |- A ≅ B ]" (at level 0, Γ, A, B at level 50).
(* Terms t and t' are (declaratively) convertible in Γ *)
Reserved Notation "[ Γ |- t ≅ t' : A ]" (at level 0, Γ, t, t', A at level 50).
(* Type A one-step weak-head reduces to type B in Γ *)

(** Weakenings *)
(* Well-formed weakening *)
Reserved Notation "Γ ≤ Δ" (at level 40).
(* Composition of weakenings *)
Reserved Notation "ρ ∘w ρ'" (at level 50).

(** Substitutions *)
(* Substitution σ is of type Δ in context Γ*)
Reserved Notation "[ Γ '|-s' σ : Δ ]" (at level 0, Γ, σ, Δ at level 50).
(* Substitutions σ and τ are convertible at types Δ in context Γ *)
Reserved Notation "[ Γ '|-s' σ ≅ τ : Δ ]" (at level 0, Γ, σ, τ, Δ at level 50).

(** Reductions *)
Reserved Notation "[ Γ |- A ⇒ B ]" (at level 0, Γ, A, B at level 50).
(* Term t one-step weak-head reduces to term u at type A in Γ *)
Reserved Notation "[ Γ |- t ⇒ u : A ]" (at level 0, Γ, t, u, A at level 50).
(* Type A multi-step weak-head reduces to type B in Γ *)
Reserved Notation "[ Γ |- A ⇒* B ]" (at level 0, Γ, A, B at level 50).
(* Term t multi-step weak-head reduces to term t' at type A in Γ *)
Reserved Notation "[ Γ |- t ⇒* t' : A ]" (at level 0, Γ, t, t', A at level 50).
(* Type A weak-head reduces in at least one step to type B in Γ *)
Reserved Notation "[ Γ |- A ⇒⁺ B ]" (at level 0, Γ, A, B at level 50).
(* Term t weak-head reduces in at least one step to term u at type A in Γ *)
Reserved Notation "[ Γ |- t ⇒⁺ u : A ]" (at level 0, Γ, t, u, A at level 50).
(* Type A weak-head normalizes to B in Γ, ie it multi-step reduces to the weak-head normal form B*)
Reserved Notation "[ Γ |- A ↘ B ]" (at level 0, Γ, A, B at level 50).
(* Term t weak-head normalizes to u at type A in Γ *)
Reserved Notation "[ Γ |- t ↘ u : A ]" (at level 0, Γ, t, u, A at level 50).
(* Types A and B are well-formed and convertible in Γ *)

(** Extra typing conditions *)
Reserved Notation "[ Γ |- A :≅: B ]" (at level 0, Γ, A, B at level 50).
(* Terms t and u are well-typed and convertible at type A in Γ *)
Reserved Notation "[ Γ |- t :≅: u : A ]" (at level 0, Γ, t, u, A at level 50).
(* Type A and B are well-formed and A weak-head reduces to B in Γ *)
Reserved Notation "[ Γ |- A :⇒*: B ]" (at level 0, Γ, A, B at level 50).
(* Terms t and u have type A in Γ and t weak-head reduces to u *)
Reserved Notation "[ Γ |- t :⇒*: u : A ]" (at level 0, Γ, t, u, A at level 50).

(** Logical relation *)

(* The universe is reducible in Γ, according to the kit K *)
Reserved Notation "[ K | Γ ||-U ]" (at level 0, K, Γ at level 50).
(* The type A is reducible as a product type in Γ according to the kit K *)
Reserved Notation "[ K | Γ ||-Π A ]" (at level 0, K, Γ, A at level 50).
(* The type A is reducible in Γ, according to the kit K *)
Reserved Notation "[ K | Γ ||- A ]"  (at level 0, K, Γ, A at level 50).
(* The types A and B are reducibly convertible in Γ, given the proof R than A is reducible, according to the kit K*)
Reserved Notation "[ K | Γ ||- A ≅ B | R ]" (at level 0, K, Γ, A, B, R at level 50).
(* The term t is reducible at type A in Γ, given the proof R than A is reducible, according to the kit K *)
Reserved Notation "[ K | Γ ||- t : A | R ]"  (at level 0, K, Γ, t, A, R at level 50).
(* The terms t and u are reducibly convertible at type A in Γ, given the proof R than A is reducible, according to the kit K *)
Reserved Notation "[ K | Γ ||- t ≅ u : A | R ]" (at level 0, K, Γ, t, u, A, R at level 50).

(* The types A and B are reducibly equal in Γ, according to the pack P for Γ and A *)
Reserved Notation "[ P | Γ ||- A ≅ B ]" (at level 0, P, Γ, A, B at level 50).
(* The term t is reducible at type A in Γ, according to the pack P *)
Reserved Notation "[ P | Γ ||- t : A ]" (at level 0, P, Γ, t, A at level 50).
(* The terms t and u are reducibly equal at type A in Γ, according to the pack P *)
Reserved Notation "[ P | Γ ||- t ≅ u : A ]" (at level 0, P, Γ, t, u, A at level 50).

(* Type level l is (strictly) smaller than type level l' *)
Reserved Notation "l << l'" (at level 70, l' at next level).

(* A is reducible as a neutral in Γ *)
Reserved Notation "[ Γ ||-ne A ]" (at level 0, Γ, A at level 50).
(* Type B is reducibly convertible to type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne A ≅ B | neA ]" (at level 0, Γ, A, B, neA at level 50).
(* Term t is reducible at type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne t : A | neA ]" (at level 0, Γ, t, A, neA at level 50).
(* Terms t and u are reducibly convertible at type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne t ≅ u : A | neA ]" (at level 0, Γ, t, u, A at level 50).

(* The type U is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-U l ]" (at level 0, Γ, l at level 50).
(* The type B is reducibly convertible to U *)
Reserved Notation "[ Γ ||-U≅ B ]" (at level 0, Γ, B at level 50).
(* The term t is reducible at the universe U, given the proof R that the universe is reducible and the kits rec at lower levels *)
Reserved Notation "[ rec | Γ ||-U t :U | R ]" (at level 0, rec, Γ, t, R at level 50).
(* The terms t and u are reducibly convertible at the universe U, given the same *)
Reserved Notation "[ rec | Γ ||-U t ≅ u :U | R ]" (at level 0, rec, Γ, t, u, R at level 50).


(* The type A has the packs of a reducible product type in Γ *)
Reserved Notation "[ Γ ||-Πd A ]" (at level 0, Γ, A at level 50).
(* The type B is reducibly convertible to A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π A ≅ B | ΠA ]" (at level 0, Γ, A, B, ΠA at level 50).
(* The term t is reducible at type A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π t : A | ΠA ]" (at level 0, Γ, t, A, ΠA at level 50).
(* The terms t and u are reducibly convertible at type A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π t ≅ u : A | ΠA ]" (at level 0, Γ, t, u, A, ΠA at level 50).

(* The universe is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-< l >U]" (at level 0, Γ, l at level 50).
(* The type A is reducible as a product type in Γ at level l *)
Reserved Notation "[ Γ ||-< l >Π  A ]" (at level 0, Γ, l, A at level 50).
(* The type A is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-< l >  A ]" (at level 0, Γ, l, A at level 50).
(* The types A and B are reducibly convertible in Γ at level l, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< l >  A ≅ B | R ]" (at level 0, Γ, l, A, B, R at level 50).
(* The term t is reducible at type A and level l in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< l >  t : A | R ]" (at level 0, Γ, l, t, A, R at level 50).
(* The terms t and u are reducibly convertible at type A and level l in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< l > t ≅ u : A | R ]" (at level 0, Γ, l, t, u, A, R at level 50).