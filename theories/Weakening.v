From MetaCoq.PCUIC Require Import PCUICAst PCUICRenameConv PCUICSigmaCalculus PCUICInstConv.
From LogRel Require Import Notations Untyped.

Inductive weakening : Set :=
  | wk_id : weakening
  | wk_step (w : weakening) : weakening
  | wk_lift (w : weakening) : weakening.

(* Transforms an (intentional) weakening into a renaming *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | wk_id => id
    | wk_step ρ' => S ∘ (wk_to_ren ρ')
    | wk_lift ρ' => shiftn 1 (wk_to_ren ρ')
  end.
Coercion wk_to_ren : weakening >-> Funclass.

Inductive well_weakening : weakening -> context -> context -> Type :=
  | well_id (Γ : context) : well_weakening wk_id Γ Γ
  | well_step (Γ Δ : context) (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (wk_step ρ) (Γ,,vass na A) Δ
  | well_lift (Γ Δ : context) (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (wk_lift ρ) (Γ,,vass na (A.[ren ρ])) (Δ,, vass na A).

Fixpoint wk_compose (ρ ρ' : weakening) : weakening :=
  match ρ, ρ' with
    | wk_id, _ => ρ'
    | wk_step ν , _ => wk_step (wk_compose ν ρ')
    | wk_lift ν, wk_id => ρ
    | wk_lift ν, wk_step ν' => wk_step (wk_compose ν ν')
    | wk_lift ν, wk_lift ν' => wk_lift (wk_compose ν ν')
  end.

Lemma wk_compose_compose (ρ ρ' : weakening) : (wk_compose ρ ρ' : nat -> nat) =1 ρ ∘ ρ'.
Proof.
  induction ρ in ρ' |- *.
  - reflexivity.
  - cbn.
    intros ?.
    now rewrite IHρ.
  - destruct ρ'.
    + reflexivity.
    + intros n.
      cbn.
      now rewrite IHρ, Nat.sub_0_r.
    + intros [] ; cbn.
      1: reflexivity.
      repeat rewrite Nat.sub_0_r.
      now rewrite IHρ.
Qed.

Lemma well_wk_compose {ρ ρ' : weakening} {Δ Δ' Δ'' : context} :
  well_weakening ρ Δ Δ' -> well_weakening ρ' Δ' Δ'' -> well_weakening (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - eassumption.
  - now econstructor.
  - inversion H' as [| | ? ? na' A' ν'] ; subst ; clear H'.
    1-2: now econstructor.
    rewrite inst_assoc.
    replace (A'.[ren ν' ∘s ren ν]) with (A'.[ren (wk_compose ν ν')]) by
      now rewrite compose_ren, wk_compose_compose.
    now econstructor.
Qed.

#[projections(primitive)]Record wk_well_wk {Γ Δ : context} :=
  { wk :> weakening ; well_wk :> well_weakening wk Γ Δ}.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).

#[global] Hint Resolve well_wk : core.

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
  - etransitivity.
    2: eapply shiftn_id.
    now rewrite IHwellρ.
Qed.