(** * LogRel.TypeConstructorsInj: injectivity and no-confusion of type constructors, and many consequences, including subject reduction. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance TypeConstructorsInj Normalisation.


Import DeclarativeTypingData.


Lemma no_neutral_empty_ctx {A t} : whne t -> [ε |-[de] t : A] -> False.
Proof.
  intros wh; induction wh in A |- *.
  - intros [? [[? [?? h]]]]%termGen'; inversion h.
  - intros [? [[? [? []]]]]%termGen'; eauto.
  - intros [? [[? []]]]%termGen'; eauto.
  - intros [? [[? []]]]%termGen'; eauto.
  - intros [? [[? [? []]]]]%termGen'; eauto.
  - intros [? [[? [? []]]]]%termGen'; eauto.
  - intros [? [[?]]]%termGen'; eauto.
Qed.

Lemma wty_norm {Γ t A} : [Γ |- t : A] ->
  ∑ wh, [× whnf wh, [Γ |- t ⤳* wh : A]& [Γ |- wh : A]].
Proof.
  intros wtyt.
  pose proof (normalisation wtyt) as [wh red].
  pose proof (h := subject_reduction _ _ _ _ wtyt red).
  assert [Γ |- wh : A] by (destruct h; boundary).
  now eexists.
Qed.

Lemma consistency {t} : [ε |- t : tEmpty] -> False.
Proof.
  intros [wh []]%wty_norm; refold.
  eapply no_neutral_empty_ctx; tea.
  eapply empty_isEmpty; tea.
Qed.


Lemma nat_canonicity {t} : [ε |- t : tNat] -> [ε |- t ≅ tZero : tNat] + ∑ n, [ε |- t ≅ tSucc n : tNat].
Proof.
  intros [wh [whwh [] wtywh]]%wty_norm; refold.
  destruct (nat_isNat _ _ wtywh whwh).
  - now left.
  - right; now eexists.
  - exfalso; now eapply no_neutral_empty_ctx.
Qed.