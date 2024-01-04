(** * LogRel.Consequences: important meta-theoretic consequences of normalization: canonicity of natural numbers and consistency. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  LogicalRelation Fundamental Validity LogicalRelation.Induction Substitution.Escape LogicalRelation.Irrelevance
  GenericTyping DeclarativeTyping DeclarativeInstance TypeConstructorsInj Normalisation.
From LogRel.LogicalRelation Require Weakening Escape.

Module Esc := LogRel.LogicalRelation.Escape.

Import DeclarativeTypingData DeclarativeTypingProperties.

Lemma no_neutral_empty_ctx_mut :
  (forall t, whne t -> forall A, [ε |-[de] t : A] -> False) ×
  (forall l, whne_list l -> forall A, [ε |-[de] l : A] -> False).
Proof.
  apply whne_mut.
  - intros * [? [[? [?? h]]]]%termGen'; inversion h.
  - intros * ?? * [? [[? [? []]]]]%termGen'; eauto.
  - intros * ?? * [? [[? []]]]%termGen'; eauto.
  - intros * ?? * [? [[? []]]]%termGen'; eauto.
  - intros * ?? * [? [[? [? []]]]]%termGen'; eauto.
  - intros * ?? * [? [[? [? []]]]]%termGen'; eauto.
  - intros * ?? * [? [[?]]]%termGen' ; eauto.
  - intros * ?? * [? [[?]]]%termGen'; eauto.
  - intros ** ; eauto.
Qed.


Lemma no_neutral_empty_ctx {A t} : whne t -> [ε |-[de] t : A] -> False.
Proof.
  intros; now eapply (fst no_neutral_empty_ctx_mut).
Qed.

Lemma wty_norm {Γ t A} : [Γ |- t : A] ->
  ∑ wh, [× whnf wh, [Γ |- t ⇒* wh : A]& [Γ |- wh : A]].
Proof.
  intros wtyt.
  pose proof (normalisation wtyt) as [wh red].
  pose proof (h := subject_reduction _ _ _ _ wtyt red).
  assert [Γ |- wh : A] by (destruct h; boundary).
  now eexists.
Qed.

(** *** Consistency: there are no closed proofs of false, i.e. no closed inhabitants of the empty type. *)

Lemma consistency {t} : [ε |- t : tEmpty] -> False.
Proof.
  intros [wh []]%wty_norm; refold.
  eapply no_neutral_empty_ctx; tea.
  eapply empty_isEmpty; tea.
Qed.

Print Assumptions consistency.

(** *** Canonicity: every closed natural number is a numeral, i.e. an iteration of [tSucc] on [tZero]. *)

Section NatCanonicityInduction.

  Let numeral : nat -> term := fun n => Nat.iter n tSucc tZero.

  #[local] Coercion numeral : nat >-> term.

  #[local] Lemma red_nat_empty : [ε ||-Nat tNat].
  Proof.
    repeat econstructor.
  Qed.

  Lemma nat_red_empty_ind :
    (forall t, [ε ||-Nat t : tNat | red_nat_empty] ->
    ∑ n : nat, [ε |- t ≅ n : tNat]) ×
    (forall t, NatProp red_nat_empty t -> ∑ n : nat, [ε |- t ≅ n : tNat]).
  Proof.
    apply NatRedInduction.
    - intros * [? []] ? _ [n] ; refold.
      exists n.
      now etransitivity.
    - exists 0 ; cbn.
      now repeat constructor.
    - intros ? _ [n].
      exists (S n) ; simpl.
      now econstructor.
    - intros ? [? [? _ _]].
      exfalso.
      now eapply no_neutral_empty_ctx.
  Qed.

  Lemma _nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ n : tNat].
  Proof.
    intros Ht.
    assert [LRNat_ one red_nat_empty | ε ||- t : tNat] as ?%nat_red_empty_ind.
    {
      apply Fundamental in Ht as [?? Vt%reducibleTm].
      irrelevance.
    }
    now assumption.
  Qed.

End NatCanonicityInduction.

Lemma nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ Nat.iter n tSucc tZero : tNat].
Proof.
  now apply _nat_canonicity.
Qed.

Section ListNatCanonicityInduction.

  Let numeral: nat -> term := fun n => Nat.iter n tSucc tZero.
  Definition lit : list nat -> term :=
    List.fold_right (fun n tl => tCons tNat (numeral n) tl) (tNil tNat).

  #[local] Coercion numeral : nat >-> term.

  Let RLN : [ε ||-List<one> tList tNat].
  Proof.
    econstructor.
    - eapply redtywf_refl; do 3 constructor.
    - do 2 constructor.
    - repeat constructor.
    - intros; eapply Weakening.wk; tea.
      eapply LRNat_. eapply red_nat_empty.
  Defined.

  Lemma list_nat_red_empty_ind :
    (forall t, [ε ||-<one> t : _ | LRList' RLN ] ->
    ∑ l : list nat, [ε |- t ≅ lit l : tList tNat]) ×
    (forall t, ListProp _ _ RLN t -> ∑ l : list nat, [ε |- t ≅ lit l : tList tNat]).
  Proof.
    apply ListRedInduction.
    - intros * [? []] ? _ [l] ; refold.
      exists l.
      now etransitivity.
    - exists nil ; cbn.
      symmetry.
      econstructor.
      now eapply Esc.escapeEq.
    - intros * ???? [l].
      assert [ε |- P ≅ tNat] by (symmetry; now eapply Esc.escapeEq).
      assert (hdty : [ε |- hd : tNat])  by now eapply Esc.escapeTerm.
      apply nat_canonicity in hdty as [n ?].
      exists (cons n l) ; cbn.
      symmetry; econstructor.
      1: now eapply Esc.escapeEq.
      all: now symmetry.
    - intros ?? [? _].
      exfalso.
      now eapply no_neutral_empty_ctx_mut.
  Qed.

  Lemma _list_nat_canonicity {t} : [ε |- t : tList tNat] ->
  ∑ l : list nat, [ε |- t ≅ lit l : tList tNat].
  Proof.
    intros Ht.
    assert [LRList' RLN | ε ||- t : tList tNat] as ?%list_nat_red_empty_ind.
    {
      apply Fundamental in Ht as [?? Vt%reducibleTm].
      irrelevance.
    }
    now assumption.
  Qed.

End ListNatCanonicityInduction.

Lemma list_nat_canonicity {t} : [ε |- t : tList tNat] ->
  ∑ l : list nat, [ε |- t ≅ lit l : tList tNat].
Proof.
  now apply _list_nat_canonicity.
Qed.
