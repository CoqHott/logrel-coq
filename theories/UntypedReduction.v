(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening.

(** ** Reductions *)

(** *** One-step reduction *)

Inductive OneRedAlg : term -> term -> Type :=
    | termBetaAlg {na A t u} :
      [ tApp (tLambda na A t) u ⇒ t[u..] ]
    | termRedAppAlg {t t' u} :
      [ t ⇒ t' ] ->
      [ tApp t u ⇒ tApp t' u ]
  where "[ t ⇒ t' ]" := (OneRedAlg t t') : typing_scope.

(** *** Multi-step reduction *)

Inductive RedClosureAlg : term -> term -> Type :=
  | redIdAlg {t} :
    [ t ⇒* t ]
  | redSuccAlg {t t' u} :
    [ t ⇒ t'] ->
    [ t' ⇒* u ] ->
    [ t ⇒* u ]
  where "[ t ⇒* t' ]" := (RedClosureAlg t t') : typing_scope.

#[export] Instance RedAlgTrans : PreOrder RedClosureAlg.
  Proof.
    split.
    - now econstructor.
    - intros * ; induction 1.
      1: easy.
      intros.
      now econstructor.
  Qed.

(** ** Properties *)

(** *** Weak-head normal forms do not reduce *)

Lemma whne_nored n u :
  whne n -> [n ⇒ u] -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  all: inversion ne ; subst ; clear ne.
  - eapply neLambda. eassumption.
  - auto.
Qed.

Lemma whnf_nored n u :
  whnf n -> [n ⇒ u] -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  - inversion nf ; subst.
    inversion H ; subst.
    eapply neLambda.
    eassumption.
  - inversion nf ; subst.
    inversion H ; subst.
    eapply IHred.
    now constructor.
Qed.

(** *** Determinism of reduction *)

Lemma ored_det {t u v} :
  [t ⇒ u] -> [t ⇒ v] ->
  u = v.
Proof.
  intros red red'.
  induction red in v, red' |- *.
  - inversion red' ; subst ; clear red'.
    + reflexivity.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
  - inversion red' ; subst ; clear red'.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
    + f_equal.
      eauto.
Qed.

Lemma red_whne t u : [t ⇒* u] -> whne t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whne_nored.
Qed.

Lemma red_whnf t u : [t ⇒* u] -> whnf t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Lemma whred_red_det t u u' :
  whnf u ->
  [t ⇒* u] -> [t ⇒* u'] ->
  [u' ⇒* u].
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - eapply red_whnf in red' as -> ; tea.
    now econstructor.
  - destruct red' as [? | ? ? ? o'].
    + now econstructor.
    + unshelve epose proof (ored_det o o') as <-.
      now eapply IHred.
Qed.

Corollary whred_det t u u' :
  whnf u -> whnf u' ->
  [t ⇒* u] -> [t ⇒* u'] ->
  u = u'.
Proof.
  intros.
  eapply red_whnf ; tea.
  now eapply whred_red_det.
Qed.

(** *** Stability by weakening *)

Lemma oredalg_wk (ρ : nat -> nat) (t u : term) :
[t ⇒ u] ->
[t⟨ρ⟩ ⇒ u⟨ρ⟩].
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  - cbn ; asimpl.
    evar (t' : term).
    replace (subst_term _ t) with t'.
    all: subst t'.
    1: econstructor.
    now asimpl.
  - cbn ; asimpl.
    now econstructor.
Qed.

Lemma credalg_wk (ρ : nat -> nat) (t u : term) :
[t ⇒* u] ->
[t⟨ρ⟩ ⇒* u⟨ρ⟩].
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.
