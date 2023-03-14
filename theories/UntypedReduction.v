From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped.

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


Section RenWhnf.

  Variable (ρ : nat -> nat).

  Lemma whne_ren t : whne t -> whne (t⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: now econstructor.
  Qed.

  Lemma whnf_ren t : whnf t -> whnf (t⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    all: now eapply whne_ren.
  Qed.
  
  Lemma isType_ren A : isType A -> isType (A⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: try now econstructor.
    econstructor; now eapply whne_ren.
  Qed.

  Lemma isPosType_ren A : isPosType A -> isPosType (A⟨ρ⟩).
  Proof.
    destruct 1 ; cbn.
    all: try now econstructor.
    econstructor; now eapply whne_ren.
  Qed.
  
  Lemma isFun_ren f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

End RenWhnf.

#[global] Hint Resolve whne_ren whnf_ren isType_ren isPosType_ren isFun_ren : gen_typing.


Lemma oredalg_wk (Γ Δ : context) (ρ : nat -> nat) (t u : term) :
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

Lemma credalg_wk (Γ Δ : context) (ρ : nat -> nat) (t u : term) :
[t ⇒* u] ->
[t⟨ρ⟩ ⇒* u⟨ρ⟩].
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.
