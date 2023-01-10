From Coq Require Import Lia.
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped.

Inductive weakening : Set :=
  | wk_id : weakening
  | wk_step (w : weakening) : weakening
  | wk_up (w : weakening) : weakening.

(* Transforms an (intentional) weakening into a renaming *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | wk_id => id
    | wk_step ρ' => (wk_to_ren ρ') >> S
    | wk_up ρ' => up_ren (wk_to_ren ρ')
  end.
Coercion wk_to_ren : weakening >-> Funclass.

#[global] Instance RenWk_term : (Ren1 weakening term term) :=
  fun ρ t => ren_term (wk_to_ren ρ) t.

Inductive well_weakening : weakening -> context -> context -> Type :=
  | well_id (Γ : context) : well_weakening wk_id Γ Γ
  | well_step (Γ Δ : context) (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (wk_step ρ) (Γ,,vass na A) Δ
  | well_up (Γ Δ : context) (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (wk_up ρ) (Γ,,vass na A⟨ρ⟩) (Δ,, vass na A).

Fixpoint wk_compose (ρ ρ' : weakening) : weakening :=
  match ρ, ρ' with
    | wk_id, _ => ρ'
    | wk_step ν , _ => wk_step (wk_compose ν ρ')
    | wk_up ν, wk_id => ρ
    | wk_up ν, wk_step ν' => wk_step (wk_compose ν ν')
    | wk_up ν, wk_up ν' => wk_up (wk_compose ν ν')
  end.

Lemma wk_compose_compose (ρ ρ' : weakening) : wk_to_ren (wk_compose ρ ρ') =1 ρ' >> ρ.
Proof.
  induction ρ in ρ' |- *.
  - reflexivity.
  - cbn.
    rewrite IHρ.
    now fsimpl.
  - destruct ρ'.
    + reflexivity.
    + cbn.
      rewrite IHρ.
      now asimpl.
    + cbn.
      asimpl.
      rewrite IHρ.
      now asimpl.
Qed.

Lemma well_wk_compose {ρ ρ' : weakening} {Δ Δ' Δ'' : context} :
  well_weakening ρ Δ Δ' -> well_weakening ρ' Δ' Δ'' -> well_weakening (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - eassumption.
  - econstructor. auto.
  - inversion H' as [| | ? ? na' A' ν']; subst ; clear H'.
    1-2: now econstructor ; auto.
    asimpl.
    replace (ren_term (ν' >> ν) A') with (ren_term (wk_compose ν ν') A')
      by now rewrite wk_compose_compose.
    econstructor ; auto.
Qed.

#[projections(primitive)]Record wk_well_wk {Γ Δ : context} :=
  { wk :> weakening ; well_wk :> well_weakening wk Γ Δ}.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).

#[global] Hint Resolve well_wk : core.

#[global] Instance RenWlWk_term {Γ Δ : context }: (Ren1 (Γ ≤ Δ) term term) :=
  fun ρ t => ren_term (wk_to_ren ρ.(wk)) t.

Definition wk_well_wk_compose {Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' :=
  {| wk := wk_compose ρ.(wk) ρ'.(wk) ; well_wk := well_wk_compose ρ.(well_wk) ρ'.(well_wk) |}.
Notation "ρ ∘w ρ'" := (wk_well_wk_compose ρ ρ').

Lemma well_length {Γ Δ : context} (ρ : Γ ≤ Δ) : #|Δ| <= #|Γ|.
Proof.
  destruct ρ as [ρ wellρ].
  induction wellρ.
  all: cbn ; lia.
Qed.

(* Testing that the definitions are right *)
Lemma id_ren (Γ : context) (ρ : Γ ≤ Γ) : (wk_to_ren ρ) =1 id.
Proof.
  destruct ρ as [ρ wellρ].
  cbn in *.
  pose proof (@eq_refl _ #|Γ|) as eΓ.
  revert eΓ wellρ.
  generalize Γ at 2 4.
  intros Δ e wellρ.
  induction wellρ in e |- *.
  all: cbn.
  - reflexivity.
  - pose proof (well_length {| wk := ρ ; well_wk := wellρ |}).
    now cbn in * ; lia.
  - asimpl.
    setoid_rewrite IHwellρ.
    2: now cbn in * ; lia.
    now intros [] ; reflexivity.
Qed.


Lemma map_decl_lift (ρ : weakening) d :
  map_decl (ren_term (up_ren ρ)) (map_decl (ren_term shift) d) =
  map_decl (ren_term shift) (map_decl (ren_term ρ) d).
Proof.
  rewrite ! compose_map_decl.
  eapply map_decl_ext.
  intros t.
  asimpl.
  reflexivity.
Qed.

Lemma in_ctx_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
  in_ctx Γ n decl ->
  in_ctx Δ (ρ n) (map_decl (ren_term ρ) decl).
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ] ; cbn.
  induction wfρ in n, decl, Hdecl |- *.
  - cbn.
    rewrite map_decl_id.
    1: eassumption.
    now asimpl.
  - cbn.
    change ((ρ >> S) n) with (S (ρ n)).
    replace (map_decl _ _) with (map_decl (ren_term shift) (map_decl (ren_term ρ) decl))
      by (now rewrite compose_map_decl ; asimpl).
    now econstructor.
  - destruct n ; cbn.
    + cbn.
      inversion Hdecl ; subst ; clear Hdecl.
      unfold ren1, Ren_decl.
      rewrite map_decl_lift.
      now constructor.
    + inversion Hdecl ; subst ; cbn in *.
      rewrite map_decl_lift.
      now econstructor.
  Qed.