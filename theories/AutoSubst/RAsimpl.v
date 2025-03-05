(** Autosubst reflective tactic that should be more efficient than asimpl

  Ways to improve:
  - Ideally, we could do much more in one step if we could incude all rules
    pertaining to constructors of the syntax, but this should be generated.
  - shift could be shiftn instead, as we often need those, better than using
    addn manually, and the tactic could handle those easily.

**)

From Coq Require Import Utf8 List.
From LogRel.AutoSubst Require Export core unscoped.
From Coq Require Import Setoid Morphisms Relation_Definitions.
Import ListNotations.

Inductive quoted_nat :=
| qnat_atom (n : nat)
| q0
| qS (n : quoted_nat).

Inductive quoted_ren :=
| qren_atom (ρ : nat → nat)
| qren_comp (r q : quoted_ren)
| qren_cons (n : quoted_nat) (q : quoted_ren)
| qren_id
| qren_shift.

Fixpoint unquote_nat q :=
  match q with
  | qnat_atom n => n
  | q0 => 0
  | qS n => S (unquote_nat n)
  end.

Fixpoint unquote_ren q :=
  match q with
  | qren_atom ρ => ρ
  | qren_comp r q => funcomp (unquote_ren r) (unquote_ren q)
  | qren_cons n q => scons (unquote_nat n) (unquote_ren q)
  | qren_id => id
  | qren_shift => S
  end.

(** Evaluation **)

Fixpoint apply_ren (r : quoted_ren) (n : quoted_nat) : quoted_nat :=
  match r, n with
  | qren_atom ρ, _ => qnat_atom (ρ (unquote_nat n))
  | qren_id, _ => n
  | qren_shift, _ => qS n
  | _, qnat_atom n => qnat_atom (unquote_ren r n)
  | qren_comp r q, _ => apply_ren r (apply_ren q n)
  | qren_cons m q, q0 => m
  | qren_cons m q, qS n => apply_ren q n
  end.

Inductive eval_ren_comp_view : quoted_ren → quoted_ren → Type :=
| eval_ren_id_l q : eval_ren_comp_view qren_id q
| eval_ren_id_r r : eval_ren_comp_view r qren_id
| eval_ren_cons_shift n r : eval_ren_comp_view (qren_cons n r) qren_shift
| eval_ren_comp_r r u v : eval_ren_comp_view r (qren_comp u v)
| eval_ren_cons_r r n q : eval_ren_comp_view r (qren_cons n q)
| eval_ren_comp_other r q : eval_ren_comp_view r q.

Definition eval_ren_comp_c r q : eval_ren_comp_view r q :=
  match r, q with
  | qren_id, q => eval_ren_id_l q
  | r, qren_id => eval_ren_id_r r
  | qren_cons n r, qren_shift => eval_ren_cons_shift n r
  | r, qren_comp u v => eval_ren_comp_r r u v
  | r, qren_cons n q => eval_ren_cons_r r n q
  | r, q =>  eval_ren_comp_other r q
  end.

Fixpoint eval_ren (r : quoted_ren) :=
  match r with
  | qren_comp r q =>
    let r := eval_ren r in
    let q := eval_ren q in
    match eval_ren_comp_c r q with
    | eval_ren_id_l q => q
    | eval_ren_id_r r => r
    | eval_ren_cons_shift n r => r
    | eval_ren_comp_r r u v =>  qren_comp (qren_comp r u) v
    | eval_ren_cons_r r n q =>  qren_cons (apply_ren r n) (qren_comp r q)
    | eval_ren_comp_other r q => qren_comp r q
    end
  | qren_cons q0 qren_shift => qren_id
  | qren_cons n r =>
    let r := eval_ren r in
    qren_cons n r
  | _ => r
  end.

Inductive qren_id_view : quoted_ren → Type :=
| is_qren_id : qren_id_view qren_id
| not_qren_id r : qren_id_view r.

Definition test_qren_id r : qren_id_view r :=
  match r with
  | qren_id => is_qren_id
  | r => not_qren_id r
  end.

(** Correctness **)

Lemma apply_ren_sound :
  ∀ r n,
    unquote_nat (apply_ren r n) = unquote_ren r (unquote_nat n).
Proof.
  intros r n.
  induction r in n |- *.
  all: try reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHr1, IHr2. reflexivity.
    + cbn. rewrite IHr1, IHr2. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + reflexivity.
    + cbn. rewrite IHr. reflexivity.
Qed.

Ltac set_eval_ren na :=
  lazymatch goal with
  | |- context [ eval_ren ?r ] =>
    set (na := eval_ren r) in * ;
    clearbody na
  end.

Ltac set_unquote_ren na :=
  lazymatch goal with
  | |- context [ unquote_ren ?r ] =>
    set (na := unquote_ren r) in * ;
    clearbody na
  end.

Ltac set_unquote_rens :=
  repeat (let n := fresh "r" in set_unquote_ren n).

Lemma eval_ren_sound :
  ∀ r,
    pointwise_relation _ eq (unquote_ren r) (unquote_ren (eval_ren r)).
Proof.
  intros r n.
  induction r in n |- *.
  all: try reflexivity.
  - cbn. set_eval_ren er1. set_eval_ren er2.
    destruct eval_ren_comp_c.
    all: unfold funcomp ; cbn - [apply_ren] in *.
    all: try solve [ rewrite IHr1, IHr2 ; reflexivity ].
    rewrite IHr1, IHr2.
    rewrite apply_ren_sound.
    apply scons_comp'.
  - cbn. destruct n0.
    + cbn. eapply scons_morphism. 1: reflexivity.
      assumption.
    + destruct r. all: try reflexivity.
      * set (rr := eval_ren _) in *.
        etransitivity.
        1:{
          eapply scons_morphism. 1: reflexivity.
          intro. eapply IHr.
        }
        destruct n. all: reflexivity.
      * set (rr := eval_ren _) in *.
        etransitivity.
        1:{
          eapply scons_morphism. 1: reflexivity.
          intro. eapply IHr.
        }
        destruct n. all: reflexivity.
      * cbn. apply scons_eta_id'.
    + cbn. apply scons_morphism. 1: reflexivity.
      assumption.
Qed.

(** Quoting **)

Ltac quote_nat n :=
  lazymatch n with
  | 0 => constr:(q0)
  | var_zero => constr:(q0)
  | S ?n =>
    let q := quote_nat n in
    constr:(qS q)
  | _ => constr:(qnat_atom n)
  end.

Ltac quote_ren r :=
  lazymatch r with
  | funcomp ?r ?r' =>
    let q := quote_ren r in
    let q' := quote_ren r' in
    constr:(qren_comp q q')
  | scons ?n ?r =>
    let qn := quote_nat n in
    let q := quote_ren r in
    constr:(qren_cons qn q)
  | id => constr:(qren_id)
  | λ x, x => constr:(qren_id)
  | shift => constr:(qren_shift)
  | S => constr:(qren_shift)
  (* Instead of minimize *)
  | λ x, ?g (?f x) =>
    let t := constr:(funcomp g f) in
    quote_ren t
  | λ x, ?f x =>
    let t := constr:(f) in
    quote_ren t
  | _ => constr:(qren_atom r)
  end.

(** Main tactic

  To make it user-extensible, we rely on type classes.

**)

Create HintDb asimpl_unfold.

(* Common *)
#[export] Hint Unfold
  Var ids Ren1 ren1 Subst1 subst1 up_ren var_zero
  : asimpl_unfold.

Tactic Notation "aunfold" := autounfold with asimpl_unfold.
Tactic Notation "aunfold" "in" hyp(h) := autounfold with asimpl_unfold in h.
Tactic Notation "aunfold" "in" "*" := autounfold with asimpl_unfold in *.

Declare Reduction asimpl_cbn :=
  cbn [
    test_qren_id
    unquote_ren eval_ren apply_ren eval_ren_comp_c
    unquote_nat
    scons
  ].

Declare Reduction asimpl_unfold :=
  unfold up_ren, var_zero.

Class RenSimplification (r s : nat → nat) := MkSimplRen {
  autosubst_simpl_ren : pointwise_relation _ eq r s
}.

Arguments autosubst_simpl_ren r {s _}.

Hint Mode RenSimplification + - : typeclass_instances.

#[export] Hint Extern 10 (RenSimplification ?r _) =>
  let q := quote_ren r in
  let s := eval asimpl_cbn in (unquote_ren (eval_ren q)) in
  let s := eval asimpl_unfold in s in
  exact (MkSimplRen r s (eval_ren_sound q))
  : typeclass_instances.

(** Triggers

  In order to avoid flooding type class resolution with useless cases, we only
  ever rewrite when there are certain triggers.
  By default those are a term with a substitution or renaming in its head.

  If you want to support other cases such as triggering renaming simplification
  in a certain judgment, then you need to add the corresponding trigger.

  For now, it seems better to have term simplication done using the topdown
  strategy while substitution and renaming simplification performed using the
  the outermost one. We thus use an extra database for the latter.

**)

Create HintDb asimpl.
(* Probably not useful (It may not create a rewrite hint)*)
Create HintDb asimpl_outermost.

(* #[export] Hint Rewrite -> autosubst_simpl_cterm : asimpl. *)
(* #[export] Hint Rewrite -> autosubst_simpl_cterm_ren : asimpl.
#[export] Hint Rewrite -> autosubst_simpl_cterm_subst : asimpl. *)
(* #[export] Hint Rewrite -> autosubst_simpl_ren : asimpl. *)
(* #[export] Hint Rewrite -> autosubst_simpl_csubst : asimpl. *)

Ltac rasimpl' :=
  (rewrite_strat (topdown (hints asimpl))) ; [ | (exact _) ..].

Ltac rasimpl'_outermost :=
  (rewrite_strat (outermost (hints asimpl_outermost))) ; [ | (exact _) ..].

Ltac rasimpl :=
  aunfold ;
  repeat rasimpl' ;
  repeat rasimpl'_outermost.

(* Taken from core.minimize *)
Ltac minimize_in h :=
  repeat first [
    change (λ x, ?f x) with f in h
  | change (λ x, ?g (?f x)) with (funcomp g f) in h
  ].

Tactic Notation "minimize" "in" hyp(h) := minimize_in h.

Ltac rasimpl'_in h :=
  (rewrite_strat (topdown (hints asimpl)) in h) ; [ | (exact _) ..].

Ltac rasimpl'_outermost_in h :=
  (rewrite_strat (outermost (hints asimpl_outermost)) in h) ; [ | (exact _) ..].

Ltac rasimpl_in h :=
  aunfold in h ;
  repeat rasimpl'_in h ;
  repeat rasimpl'_outermost_in h.

Tactic Notation "rasimpl" "in" hyp(h) :=
  rasimpl_in h.
