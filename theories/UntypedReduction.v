From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening.

Inductive OneRedAlg : term -> term -> Type :=
    | termBetaAlg {na A t u} :
      [ tApp (tLambda na A t) u ⇒ t[u..] ]
    | termRedAppAlg {t t' u} :
      [ t ⇒ t' ] ->
      [ tApp t u ⇒ tApp t' u ]
  where "[ t ⇒ t' ]" := (OneRedAlg t t') : typing_scope.

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

(** Whnf do not reduce *)

Lemma whne_nored n u :
  whne n -> [n ⇒ u] -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  - inversion ne ; subst ; clear ne.
    eapply neLambda.
    eassumption.
  - now inversion ne.
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

(** Determinism of reduction *)

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

Lemma oredalg_wk (Γ Δ : context) (ρ : Δ ≤ Γ) (t u : term) :
[t ⇒ u] ->
[t⟨ρ⟩ ⇒ u⟨ρ⟩].
Proof.
  intros Hred.
  induction Hred in Δ, ρ |- *.
  - cbn ; asimpl.
    evar (t' : term).
    replace (subst_term _ t) with t'.
    all: subst t'.
    1: econstructor.
    now asimpl.
  - cbn ; asimpl.
    now econstructor.
Qed.

Lemma credalg_wk (Γ Δ : context) (ρ : Δ ≤ Γ) (t u : term) :
[t ⇒* u] ->
[t⟨ρ⟩ ⇒* u⟨ρ⟩].
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.