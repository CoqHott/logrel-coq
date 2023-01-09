From LogRel Require Import Utils BasicAst Ast Context.

(* We have two families of definitions: the declarative ones (tagged de), and the algorithmic ones (tagged al) *)
(* All notations come in two versions: the tagged and the untagged one. The untagged one can be used in input,
ideally wisely in cases where there is only one instance at hand. The tagged one is used systematically in printing,
and can be used in input when disambiguation is needed.*)

Variant tag := | de | al.

Declare Scope typing_scope.
Delimit Scope typing_scope with ty.

Open Scope typing_scope.

(** Typing *)
Class WfContext (ta : tag) := wf_context : context -> Set.
Class WfType (ta : tag) := wf_type : context -> term -> Set.
Class Typing (ta : tag) := typing : context -> term -> term -> Set.
Class Infering (ta : tag) := infering : context -> term -> term -> Set.
Class ConvType (ta : tag) := conv_type : context -> term -> term -> Set.
Class ConvTerm (ta : tag) := conv_term : context -> term -> term -> term -> Set.
Class ConvNeu (ta : tag) := conv_neu : context -> term -> term -> term -> Set.

(* The context Γ is well-formed *)
Notation "[ |- Γ ]" := (wf_context Γ)
  (at level 0, Γ at level 50, only parsing) : typing_scope.
Notation "[ |-[ ta  ] Γ ]" := (wf_context (ta := ta) Γ)
  (at level 0, ta, Γ at level 50) : typing_scope.
(* The type A is well-formed in Γ *)
Notation "[ Γ |- A ]" := (wf_type Γ A)
  (at level 0, Γ, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ]" := (wf_type (ta := ta) Γ A)
  (at level 0, ta, Γ, A at level 50) : typing_scope.
(* The term t has type A in Γ *)
Notation "[ Γ |- t : A ]" := (typing Γ A t)
  (at level 0, Γ, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t : A ]" :=
  (typing (ta := ta) Γ A t) (at level 0, ta, Γ, t, A at level 50) : typing_scope.
(* The term t infers A in Γ *)
Notation "[ Γ |- t ▹ A ]" := (infering Γ A t)
  (at level 0, Γ, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ▹ A ]" :=
  (infering (ta := ta) Γ A t) (at level 0, ta, Γ, t, A at level 50) : typing_scope.
(* The term t infers the reduced A in Γ *)
Reserved Notation "[ Γ |- t ▹h A ]" (at level 0, Γ, t, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t ▹h A ]" (at level 0, ta, Γ, t, A at level 50).
(* Types A and B are convertible in Γ *)
Notation "[ Γ |- A ≅ B ]" := (conv_type Γ A B)
  (at level 0, Γ, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ≅ B ]" := (conv_type (ta := ta) Γ A B)
  (at level 0, ta, Γ, A, B at level 50) : typing_scope.
(* Types in whnf A and B are convertible in Γ *)
Reserved Notation "[ Γ |- A '≅h' B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A '≅h' B ]" (at level 0, ta, Γ, A, B at level 50).
(* Terms t and t' are convertible in Γ *)
Notation "[ Γ |- t ≅ t' : A ]" := (conv_term Γ A t t')
  (at level 0, Γ, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ≅ t' : A ]" := (conv_term (ta := ta) Γ A t t')
  (at level 0, ta, Γ, t, t', A at level 50) : typing_scope.
(* Whnfs t and t' are convertible in Γ *)
Reserved Notation "[ Γ |- t '≅h' t' : A ]" (at level 0, Γ, t, t', A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t '≅h' t' : A ]" (at level 0, ta, Γ, t, t', A at level 50).
(* Neutral n and n' are convertible in Γ *)
Notation "[ Γ |- n ~ n' ▹ A ]" := (conv_neu Γ A n n')
  (at level 0, Γ, n, n', A at level 50, only parsing) : typing_scope. 
Notation "[ Γ |-[ ta  ] n ~ n' ▹ A ]" := (conv_neu (ta := ta) Γ A n n')
  (at level 0, ta, Γ, n, n', A at level 50) : typing_scope.
(* Neutral n and n' are convertible at the reduced type A in Γ *)
Reserved Notation "[ Γ |- n '~h' n' ▹ A ]" (at level 0, Γ, n, n', A at level 50).
Reserved Notation "[ Γ |-[ ta  ] n '~h' n' ▹ A ]" (at level 0, ta, Γ, n, n', A at level 50).

(** Reductions *)
Class OneRedType (ta : tag) := one_red_ty : context -> term -> term -> Set.
Class OneRedTerm (ta : tag) := one_red_tm : context -> term -> term -> term -> Set.
(* Class MultiRedType := multi_red_ty : context -> term -> term -> Set.
Class MultiRedTerm := multi_red_tm : context -> term -> term -> term -> Set.
Class WhNormType := wh_norm_ty : context -> term -> term -> Set.
Class WhNormTerm := wh_norm_tm : context -> term -> term ->term -> Set. *)

(* Set A one-step weak-head reduces to type B in Γ *)
Notation "[ Γ |- A ⇒ B ]" := (one_red_ty Γ A B)
  (at level 0, Γ, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ⇒ B ]" := (one_red_ty (ta := ta) Γ A B)
  (at level 0, ta, Γ, A, B at level 50) : typing_scope.
(* Term t one-step weak-head reduces to term u at type A in Γ *)
Notation "[ Γ |- t ⇒ u : A ]" := (one_red_tm Γ A t u)
  (at level 0, Γ, t, u, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ⇒ u : A ]" := (one_red_tm (ta := ta) Γ A t u)
  (at level 0, ta, Γ, t, u, A at level 50) : typing_scope.
(* Set A multi-step weak-head reduces to type B in Γ *)
Reserved Notation "[ Γ |- A ⇒* B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A ⇒* B ]" (at level 0, ta, Γ, A, B at level 50).
(* Term t multi-step weak-head reduces to term t' at type A in Γ *)
Reserved Notation "[ Γ |- t ⇒* t' : A ]" (at level 0, Γ, t, t', A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t ⇒* t' : A ]" (at level 0, ta, Γ, t, t', A at level 50).
(* Set A weak-head normalizes to B in Γ, ie it multi-step reduces to the weak-head normal form B*)
Reserved Notation "[ Γ |- A ↘ B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A ↘ B ]" (at level 0, ta, Γ, A, B at level 50).
(* Term t weak-head normalizes to u at type A in Γ *)
Reserved Notation "[ Γ |- t ↘ u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t ↘ u : A ]" (at level 0, ta, Γ, t, u, A at level 50).

(** Substitutions *)

Class WfSubst (ta : tag) := wf_subst : context -> context -> (nat -> term) -> Set.
Class ConvSubst (ta : tag) := conv_subst : context -> context -> (nat -> term) -> (nat -> term) -> Set.

(* Substitution σ is of type Δ in context Γ*)
Notation "[ Γ '|-s' σ : Δ ]" := (wf_subst Γ σ Δ)
  (at level 0, Γ, σ, Δ at level 50, only parsing) : typing_scope.
Notation "[ Γ '|-'[ ta  ']s' σ : Δ ]" := (wf_subst (ta := ta) Γ Δ σ)
  (at level 0, ta, Γ, σ, Δ at level 50) : typing_scope.
(* Substitutions σ and τ are convertible at types Δ in context Γ *)
Notation "[ Γ '|-s' σ ≅ τ : Δ ]" := (conv_subst Γ Δ σ τ)
  (at level 0, Γ, σ, τ, Δ at level 50, only parsing) : typing_scope.
Notation "[ Γ '|-[ ta ']s' σ ≅ τ : Δ ]" := (conv_subst (ta := ta) Γ Δ σ τ)
  (at level 0, ta, Γ, σ, τ, Δ at level 50) : typing_scope.

(** Extra typing conditions *)
(* Types A and B are well-formed and convertible in Γ *)
Reserved Notation "[ Γ |- A :≅: B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A :≅: B ]" (at level 0, ta, Γ, A, B at level 50).
(* Terms t and u are well-typed and convertible at type A in Γ *)
Reserved Notation "[ Γ |- t :≅: u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t :≅: u : A ]" (at level 0, ta, Γ, t, u, A at level 50).
(* Set A and B are well-formed and A weak-head reduces to B in Γ *)
Reserved Notation "[ Γ |- A :⇒*: B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A :⇒*: B ]" (at level 0, ta, Γ, A, B at level 50).
(* Terms t and u have type A in Γ and t weak-head reduces to u *)
Reserved Notation "[ Γ |- t :⇒*: u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t :⇒*: u : A ]" (at level 0, ta, Γ, t, u, A at level 50).

(** Weakenings *)
(* Well-formed weakening *)
Reserved Notation "Γ ≤ Δ" (at level 40).
(* Composition of weakenings *)
Reserved Notation "ρ ∘w ρ'" (at level 50).


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

(* Set level l is (strictly) smaller than type level l' *)
Reserved Notation "l << l'" (at level 70, l' at next level).

(* A is reducible as a neutral in Γ *)
Reserved Notation "[ Γ ||-ne A ]" (at level 0, Γ, A at level 50).
(* Set B is reducibly convertible to type A in Γ, given the proof neA that A is reducible as neutral *)
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