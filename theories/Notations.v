(** * LogRel.Notations: notations for conversion, typing and the logical relations. *)
From LogRel Require Import Utils BasicAst Context LContexts.
From LogRel.AutoSubst Require Import Ast.

(** We have four families of definitions: the declarative ones (tagged de), the algorithmic ones (tagged al), and the bundled ones, which package an algorithmic typing derivation with its preconditions (tagged bn).
The bundled intermediate (bni) family uses algorithmic conversion but declarative typing (somewhat similar to the original formalization), while bn uses algorithmic typing and conversion.

All notations come in two versions: the tagged and the untagged one. The untagged one can be used in input only,
ideally wisely in cases where there is only one instance at hand. The tagged one is used systematically in printing,
and can be used in input when disambiguation is desired. *)

Variant tag := | de | al | bn | bni.
Inductive class := istype | isterm : term -> class.

Declare Scope typing_scope.
Delimit Scope typing_scope with ty.

Declare Scope declarative_scope.
Delimit Scope declarative_scope with de.
Close Scope declarative_scope.

Open Scope typing_scope.

(** ** Typing *)
Class WfContext (ta : tag) := wf_context : wfLCon -> context -> Set.
Class WfType (ta : tag) := wf_type : wfLCon -> context -> term -> Set.
Class Typing (ta : tag) := typing : wfLCon -> context -> term -> term -> Set.
Class Inferring (ta : tag) := inferring : wfLCon -> context  -> term -> term -> Set.
Class InferringRed (ta : tag) := infer_red : wfLCon -> context  -> term -> term -> Set.
Class Checking (ta : tag) := check : wfLCon -> context  -> term -> term -> Set.
Class TypeNe (ta : tag) := type_ne : wfLCon -> context  -> term -> Set.
Class TypeNf (ta : tag) := type_nf : wfLCon -> context  -> term -> Set.
Class TermNe (ta : tag) := term_ne : wfLCon -> context  -> term -> term -> Set.
Class TermNf (ta : tag) := term_nf : wfLCon -> context  -> term -> term -> Set.
Class ConvType (ta : tag) := conv_type : wfLCon -> context  -> term -> term -> Set.
Class ConvTypeRed (ta : tag) :=
  conv_type_red : wfLCon -> context  -> term -> term -> Set.
Class ConvTerm (ta : tag) :=
  conv_term : wfLCon -> context  -> term -> term -> term -> Set.
Class ConvTermRed (ta : tag) :=
  conv_term_red : wfLCon -> context  -> term -> term -> term -> Set.
Class ConvNeu (ta : tag) := conv_neu : wfLCon -> context  -> term -> term -> term -> Set.
Class ConvNeuRed (ta : tag) :=
  conv_neu_red : wfLCon -> context  -> term -> term -> term -> Set.
Class ConvNeuConv (ta : tag) :=
  conv_neu_conv : wfLCon -> context  -> term -> term -> term -> Set.

(** The context Γ is well-formed *)
Notation "[ |- Γ ]< l >" := (wf_context l Γ)
  (at level 0, Γ, l at level 50, only parsing) : typing_scope.
Notation "[ |-[ ta  ] Γ ]< l >" := (wf_context (ta := ta) l Γ)
  (at level 0, ta, Γ, l at level 50) : typing_scope.
(** The contexts Γ and Δ are convertible *)
Reserved Notation "[ |- Γ ≅ Δ ]< l >" (at level 0, Γ, l, Δ at level 50).
Reserved Notation "[ |-[ ta  ] Γ ≅ Δ ]< l >" (at level 0, ta, Γ, l, Δ at level 50).
(** The type A is well-formed in Γ *)
Notation "[ Γ |- A ]< l >" := (wf_type l Γ A)
  (at level 0, Γ, l, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ]< l >" := (wf_type (ta := ta) l Γ A)
  (at level 0, ta, Γ, l, A at level 50) : typing_scope.

(** The term t has type A in Γ *)
Notation "[ Γ |- t : A ]< l >" := (typing l Γ A t)
  (at level 0, Γ, l, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t : A ]< l >" :=
  (typing (ta := ta) l Γ A t) (at level 0, ta, Γ, l, t, A at level 50) : typing_scope.

Notation "Nf[ Γ |- A ]< l >" := (type_nf l Γ A)
  (at level 0, Γ, l, A at level 50, only parsing) : typing_scope.
Notation "Nf[ Γ |-[ ta  ] A ]< l >" := (type_nf (ta := ta) l Γ A)
  (at level 0, Γ, l, A at level 50) : typing_scope.
Notation "Ne[ Γ |- A ]< l >" := (type_ne l Γ A)
  (at level 0, Γ, l, A at level 50, only parsing) : typing_scope.
Notation "Ne[ Γ |-[ ta  ] A ]< l >" := (type_ne (ta := ta) l Γ A)
  (at level 0, Γ, l, A at level 50) : typing_scope.
Notation "Nf[ Γ |- t : A ]< l >" := (term_nf l Γ A t)
  (at level 0, Γ, l, t, A at level 50, only parsing) : typing_scope.
Notation "Nf[ Γ |-[ ta  ] t : A ]< l >" := (term_nf (ta := ta) l Γ A t)
  (at level 0, Γ, l, t, A at level 50) : typing_scope.
Notation "Ne[ Γ |- t : A ]< l >" := (term_ne l Γ A t)
  (at level 0, Γ, l, t, A at level 50, only parsing) : typing_scope.
Notation "Ne[ Γ |-[ ta  ] t : A ]< l >" := (term_ne (ta := ta) l Γ A t)
  (at level 0, Γ, l, t, A at level 50) : typing_scope.
(** The term t checks against type A in Γ *)
Notation "[ Γ |- t ◃ A ]< l >" := (check l Γ A t)
  (at level 0, Γ, l, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ◃ A ]< l >" :=
  (check (ta := ta) l Γ A t) (at level 0, ta, Γ, l, t, A at level 50) : typing_scope.
(** The term t infers A in Γ *)
Notation "[ Γ |- t ▹ A ]< l >" := (inferring l Γ A t)
  (at level 0, Γ, l, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ▹ A ]< l >" :=
  (inferring (ta := ta) l Γ A t) (at level 0, ta, Γ, l, t, A at level 50) : typing_scope.
(** The term t infers the reduced A in Γ *)
Notation "[ Γ |- t ▹h A ]< l >" := (infer_red l Γ A t) (at level 0, Γ, l, t, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ▹h A ]< l >" := (infer_red (ta := ta) l Γ A t) (at level 0, ta, Γ, l, t, A at level 50) : typing_scope.
(** Types A and B are convertible in Γ *)
Notation "[ Γ |- A ≅ B ]< l >" := (conv_type l Γ A B)
  (at level 0, Γ, l, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ≅ B ]< l >" := (conv_type (ta := ta) l Γ A B)
  (at level 0, ta, Γ, l, A, B at level 50) : typing_scope.
(** Types in whnf A and B are convertible in Γ *)
Notation "[ Γ |- A '≅h' B ]< l >" := (conv_type_red l Γ A B) (at level 0, Γ, l, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A '≅h' B ]< l >" := (conv_type_red (ta := ta) l Γ A B) (at level 0, ta, Γ, l, A, B at level 50) : typing_scope.
(** Terms t and t' are convertible in Γ *)
Notation "[ Γ |- t ≅ t' : A ]< l >" := (conv_term l Γ A t t')
  (at level 0, Γ, l, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ≅ t' : A ]< l >" := (conv_term (ta := ta) l Γ A t t')
  (at level 0, ta, Γ, l, t, t', A at level 50) : typing_scope.
(** Whnfs t and t' are convertible in Γ *)
Notation "[ Γ |- t '≅h' t' : A ]< l >" := (conv_term_red l Γ A t t') (at level 0, Γ, l, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t '≅h' t' : A ]< l >" := (conv_term_red (ta := ta) l Γ A t t') (at level 0, ta, Γ, l, t, t', A at level 50) : typing_scope.
(** Neutral n and n' are convertible in Γ, inferring the type A *)
Notation "[ Γ |- n ~ n' ▹ A ]< l >" := (conv_neu l Γ A n n')
  (at level 0, Γ, l, n, n', A at level 50, only parsing) : typing_scope. 
Notation "[ Γ |-[ ta  ] n ~ n' ▹ A ]< l >" := (conv_neu (ta := ta) l Γ A n n')
  (at level 0, ta, Γ, l, n, n', A at level 50) : typing_scope.
(** Neutral n and n' are convertible in Γ, inferring the reduced type A *)
Notation "[ Γ |- n '~h' n' ▹ A ]< l >" := (conv_neu_red l Γ A n n') (at level 0, Γ, l, n, n', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] n '~h' n' ▹ A ]< l >" := (conv_neu_red (ta := ta) l Γ A n n') (at level 0, ta, Γ, l, n, n', A at level 50) : typing_scope.
(** Neutral n and n' are convertible in Γ at type A *)
Notation "[ Γ |- n ~ n' : A ]< l >" := (conv_neu_conv l Γ A n n')
  (at level 0, Γ, l, n, n', A at level 50, only parsing) : typing_scope. 
Notation "[ Γ |-[ ta  ] n ~ n' : A ]< l >" := (conv_neu_conv (ta := ta) l Γ A n n')
  (at level 0, ta, Γ, l, n, n', A at level 50) : typing_scope.

(** ** Reductions *)
Class RedType (ta : tag) := red_ty : wfLCon -> context -> term -> term -> Set.
Class OneStepRedTerm (ta : tag) :=
  osred_tm : wfLCon -> context -> term -> term -> term -> Set.
Class RedTerm (ta : tag) := red_tm : wfLCon -> context -> term -> term -> term -> Set.

(** Term t untyped one-step weak-head reduces to term t' *)
Reserved Notation "[ t ⇒ t' ]< l >" (at level 0, l, t, t' at level 50).
(** Term t untyped multi-step weak-head reduces to term t' *)
Reserved Notation "[ t ⇒* t' ]< l >" (at level 0, l, t, t' at level 50).

(** Type A one-step weak-head reduces to type B in Γ *)
Reserved Notation "[ Γ |- A ⇒ B ]< l >" (at level 0, Γ, l, A, B at level 50).
(** Term or type t one-step weak-head reduces to term or type type u as class A in Γ *)
Reserved Notation "[ Γ |- t ⇒ u ∈ A ]< l >" (at level 0, Γ, l, t, u, A at level 50).
(** Term or type t multi-step weak-head reduces to term or type type u as class A in Γ *)
Reserved Notation "[ Γ |- t ⇒* u ∈ A ]< l >" (at level 0, Γ, l, t, u, A at level 50).
(** Term t one-step weak-head reduces to term u at type A in Γ *)
Notation "[ Γ |- t ⇒ u : A ]< l >" := (osred_tm l Γ A t u) (at level 0, Γ, l, t, u, A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ⇒ u : A ]< l >" := (osred_tm (ta:=ta) l Γ A t u) (at level 0, ta,Γ, t, u, A at level 50) : typing_scope.
(** Type A multi-step weak-head reduces to type B in Γ *)
Notation "[ Γ |- A ⇒* B ]< l >" := (red_ty l Γ A B) (at level 0, Γ, l, A, B at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ⇒* B ]< l >" := (red_ty (ta := ta) l Γ A B)
(at level 0, ta, Γ, l, A, B at level 50) : typing_scope.
(** Term t multi-step weak-head reduces to term t' at type A in Γ *)
Notation "[ Γ |- t ⇒* t' : A ]< l >" := (red_tm l Γ A t t')
(at level 0, Γ, l, t, t', A at level 50, only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t ⇒* t' : A ]< l >" := (red_tm (ta := ta) l Γ A t t')
(at level 0, ta, Γ, l, t, t', A at level 50) : typing_scope.
(** Set A weak-head normalizes to B in Γ, ie it multi-step reduces to the weak-head normal form B*)
Reserved Notation "[ Γ |- A ↘ B ]< l >" (at level 0, Γ, l, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A ↘ B ]< l >" (at level 0, ta, Γ, l, A, B at level 50).
(** Term t weak-head normalizes to u at type A in Γ *)
Reserved Notation "[ Γ |- t ↘ u : A ]< l >" (at level 0, Γ, l, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t ↘ u : A ]< l >" (at level 0, ta, Γ, l, t, u, A at level 50).

(** ** Substitutions *)

(** Substitution σ is of type Δ in context Γ*)
Reserved Notation "[ Γ '|-s' σ : Δ ]< l >" (at level 0, Γ, l, σ, Δ at level 50).
Reserved Notation "[ Γ |-[ ta  ']s' σ : Δ ]< l >" (at level 0, ta, Γ, l, σ, Δ at level 50).
(** Substitutions σ and τ are convertible at types Δ in context Γ *)
Reserved Notation "[ Γ '|-s' σ ≅ τ : Δ ]< l >" (at level 0, Γ, l, σ, τ, Δ at level 50).
Reserved Notation "[ Γ |-[ ta  ']s' σ ≅ τ : Δ ]< l >" (at level 0, ta, Γ, l, σ, τ, Δ at level 50).

(** ** Extra typing conditions *)
(** Types A and B are well-formed and convertible in Γ *)
Reserved Notation "[ Γ |- A :≅: B ]< l >" (at level 0, Γ, l, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A :≅: B ]< l >" (at level 0, ta, Γ, l, A, B at level 50).
(** Terms t and u are well-typed and convertible at type A in Γ *)
Reserved Notation "[ Γ |- t :≅: u : A ]< l >" (at level 0, Γ, l, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t :≅: u : A ]< l >" (at level 0, ta, Γ, l, t, u, A at level 50).
(** Set A and B are well-formed and A weak-head reduces to B in Γ *)
Reserved Notation "[ Γ |- A :⇒*: B ]< l >" (at level 0, Γ, l, A, B at level 50).
Reserved Notation "[ Γ |-[ ta  ] A :⇒*: B ]< l >" (at level 0, ta, Γ, l, A, B at level 50).
(** Terms t and u have type A in Γ and t weak-head reduces to u *)
Reserved Notation "[ Γ |- t :⇒*: u : A ]< l >" (at level 0, Γ, l, t, u, A at level 50).
Reserved Notation "[ Γ |-[ ta  ] t :⇒*: u : A ]< l >" (at level 0, ta, Γ, l, t, u, A at level 50).

(** ** Weakenings *)
(** Well-formed weakening *)
Reserved Notation "Γ ≤ Δ" (at level 40).
(** Composition of weakenings *)
Reserved Notation "ρ ∘w ρ'" (at level 50).


(** ** Logical relation *)
(** The universe is reducible in Γ, according to the kit K *)
Reserved Notation "[ K | Γ ||-U ]< l >" (at level 0, K, Γ, l at level 50).
(** The type A is reducible as a Π type in Γ according to the kit K *)
Reserved Notation "[ K | Γ ||-Π A ]< l >" (at level 0, K, Γ, l, A at level 50).
(** The type A is reducible in Γ, according to the kit K *)
Reserved Notation "[ K | Γ ||- A ]< l >"  (at level 0, K, Γ, l, A at level 50).
(** The types A and B are reducibly convertible in Γ, given the proof R than A is reducible, according to the kit K*)
Reserved Notation "[ K | Γ ||- A ≅ B | R ]< l >" (at level 0, K, Γ, l, A, B, R at level 50).
(** The term t is reducible at type A in Γ, given the proof R than A is reducible, according to the kit K *)
Reserved Notation "[ K | Γ ||- t : A | R ]< l >"  (at level 0, K, Γ, l, t, A, R at level 50).
(** The terms t and u are reducibly convertible at type A in Γ, given the proof R than A is reducible, according to the kit K *)
Reserved Notation "[ K | Γ ||- t ≅ u : A | R ]< l >" (at level 0, K, Γ, l, t, u, A, R at level 50).

(** The types A and B are reducibly equal in Γ, according to the pack P for Γ and A *)
Reserved Notation "[ P | Γ ||- A ≅ B ]< l >" (at level 0, P, Γ, l, A, B at level 50).
(** The term t is reducible at type A in Γ, according to the pack P *)
Reserved Notation "[ P | Γ ||- t : A ]< l >" (at level 0, P, Γ, l, t, A at level 50).
(** The terms t and u are reducibly equal at type A in Γ, according to the pack P *)
Reserved Notation "[ P | Γ ||- t ≅ u : A ]< l >" (at level 0, P, Γ, l, t, u, A at level 50).

(** Set level l is (strictly) smaller than type level l' *)
Reserved Notation "l << l'" (at level 70, l' at next level).

(** A is reducible as a neutral in Γ *)
Reserved Notation "[ Γ ||-ne A ]< l >" (at level 0, Γ, l, A at level 50).
(** Set B is reducibly convertible to type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne A ≅ B | neA ]< l >" (at level 0, Γ, l, A, B, neA at level 50).
(** Term t is reducible at type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne t : A | neA ]< l >" (at level 0, Γ, l, t, A, neA at level 50).
(** Terms t and u are reducibly convertible at type A in Γ, given the proof neA that A is reducible as neutral *)
Reserved Notation "[ Γ ||-ne t ≅ u : A | neA ]< l >" (at level 0, Γ, l, t, u, A at level 50).

(** The type U is reducible in Γ at level k *)
Reserved Notation "[ Γ ||-U k ]< l >" (at level 0, Γ, l, k at level 50).
(** The type B is reducibly convertible to U *)
Reserved Notation "[ Γ ||-U≅ B ]< l >" (at level 0, Γ, l, B at level 50).
(** The term t is reducible at the universe U, given the proof R that the universe is reducible and the kits rec at lower levels *)
Reserved Notation "[ rec | Γ ||-U t :U | R ]< l >" (at level 0, rec, Γ, l, t, R at level 50).
(** The terms t and u are reducibly convertible at the universe U, given the same *)
Reserved Notation "[ rec | Γ ||-U t ≅ u :U | R ]< l >" (at level 0, rec, Γ, l, t, u, R at level 50).


(** The type A has the packs of a reducible Π type in Γ *)
Reserved Notation "[ Γ ||-Πd A ]< l >" (at level 0, Γ, l, A at level 50).
(** The type B is reducibly convertible to A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π A ≅ B | ΠA ]< l >" (at level 0, Γ, l, A, B, ΠA at level 50).
(** The term t is reducible at type A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π t : A | ΠA ]< l >" (at level 0, Γ, l, t, A, ΠA at level 50).
(** The terms t and u are reducibly convertible at type A in Γ, given the reducibility pack ΠA *)
Reserved Notation "[ Γ ||-Π t ≅ u : A | ΠA ]< l >" (at level 0, Γ, l, t, u, A, ΠA at level 50).

(** The universe is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-< k >U]< l >" (at level 0, Γ, l, k at level 50).
(** The type A is reducible as a Π type in Γ at level l *)
Reserved Notation "[ Γ ||-< k >Π  A ]< l >" (at level 0, Γ, l, k, A at level 50).
(** The type A is reducible in Γ at level l *)
Reserved Notation "[ Γ ||-< k >  A ]< l >" (at level 0, Γ, l, k, A at level 50).
(** The types A and B are reducibly convertible in Γ at level l, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< k >  A ≅ B | R ]< l >" (at level 0, Γ, l, k, A, B, R at level 50).
(** The term t is reducible at type A and level l in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< k >  t : A | R ]< l >" (at level 0, Γ, l, k, t, A, R at level 50).
(** The terms t and u are reducibly convertible at type A and level l in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-< k > t ≅ u : A | R ]< l >" (at level 0, Γ, l, k, t, u, A, R at level 50).

(** The type A is reducible in Γ at level 0*)
Reserved Notation "[ Γ ||-<0>  A ]< l >" (at level 0, Γ, l, A at level 50).
(** The types A and B are reducibly convertible in Γ at level 0, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-<0>  A ≅ B | R ]< l >" (at level 0, Γ, l, A, B, R at level 50).
(** The term t is reducible at type A and level 0 in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-<0>  t : A | R ]< l >" (at level 0, Γ, l, t, A, R at level 50).
(** The terms t and u are reducibly convertible at type A and level 0 in Γ, given the proof R that A is reducible *)
Reserved Notation "[ Γ ||-<0> t ≅ u : A | R ]< l >" (at level 0, Γ, l, t, u, A, R at level 50).




(** ** Validity notations *)
Reserved Notation "[||-v Γ ]< l >" (at level 0, Γ, l at level 50).
Reserved Notation "[ Δ ||-v σ : Γ | VΓ | wfΔ ]< l >" (at level 0, Δ, σ, Γ, l, VΓ, wfΔ at level 50).
Reserved Notation "[ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ ]< l >" (at level 0, Δ, σ, σ', Γ, l, VΓ, wfΔ, vσ at level 50).
Reserved Notation "[ Γ ||-v< k > A | VΓ ]< l >" (at level 0, Γ, l, k , A, VΓ at level 50).
Reserved Notation "[ P | Δ ||-v σ : Γ | wfΔ ]< l >" (at level 0, P, Δ, σ, Γ, l, wfΔ at level 50).
Reserved Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ]< l >"  (at level 0, P, Δ, σ, σ', Γ, l, wfΔ, vσ at level 50).
Reserved Notation "[ R | ||-v Γ ]< l >"  (at level 0, R, Γ, l at level 50).
Reserved Notation "[ R | Δ ||-v σ : Γ | RΓ | wfΔ ]< l >"  (at level 0, R, Δ, σ, Γ, l, RΓ, wfΔ at level 50).
Reserved Notation "[ R | Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ | vσ ]< l >" (at level 0, R, Δ, σ, σ', Γ, l, RΓ, wfΔ, vσ at level 50).
Reserved Notation "[ P | Γ ||-v< k > A ]< l >"  (at level 0, P, Γ, l, l, k, A at level 50).

(** LCon Notations *)
Notation " ne £ b ::l l" := (wfLCons l ne b) (at level 40).
