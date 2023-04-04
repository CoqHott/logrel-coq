(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening.

(** ** Reductions *)

(** *** One-step reduction. *)

Inductive OneRedAlg {l : wfLCon} : term -> term -> Type :=
| BRed {A a t} :
    [ (tApp (tLambda A t) a) ⇒ t[a..] ]< l >
| appSubst {t u a} :
    [ t ⇒ u ]< l > ->
    [ tApp t a ⇒ tApp u a ]< l >
| natElimSubst {P hz hs n n'} :
    [ n ⇒ n' ]< l > ->
    [ tNatElim P hz hs n ⇒ tNatElim P hz hs n' ]< l >
| natElimZero {P hz hs} :
    [ tNatElim P hz hs tZero ⇒ hz ]< l >
| natElimSucc {P hz hs n} :
  [ tNatElim P hz hs (tSucc n)
      ⇒ tApp (tApp hs n) (tNatElim P hz hs n) ]< l >
| termRedEmptyElimAlg {P e e'} :
    [e ⇒ e']< l > ->
    [tEmptyElim P e ⇒ tEmptyElim P e']< l >        
| boolElimSubst {P hz hs n n'} :
    [ n ⇒ n' ]< l > ->
    [ tBoolElim P hz hs n ⇒ tBoolElim P hz hs n' ]< l >
| boolElimTrue {P ht hf} :
    [ tBoolElim P ht hf tTrue ⇒ ht ]< l >
| boolElimFalse {P ht hf} :
  [ tBoolElim P ht hf tFalse ⇒ hf ]< l >
| alphaSubst {n n'} :
  [ n ⇒ n' ]< l > -> [ tAlpha n ⇒ tAlpha n' ]< l >
| alphaRed {n b} : in_LCon (pi1 l) n b ->
                   [ tAlpha (nat_to_term n) ⇒ bool_to_term b]< l >

where "[ t ⇒ t' ]< l >" := (OneRedAlg (l := l) t t') : typing_scope.

(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Inductive RedClosureAlg {l} : term -> term -> Type :=
  | redIdAlg {t} :
    [ t ⇒* t ]< l >
  | redSuccAlg {t t' u} :
    [ t ⇒ t']< l > ->
    [ t' ⇒* u ]< l > ->
    [ t ⇒* u ]< l >
  where "[ t ⇒* t' ]< l >" := (RedClosureAlg (l := l) t t') : typing_scope.

#[export] Instance RedAlgTrans {l} : PreOrder (RedClosureAlg (l := l)).
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

Ltac inv_whne :=
  match goal with | [ H : whne _ _ |- _ ] => inversion H
             | [ H : alphawhne _ _ |- _ ] => inversion H end.

Lemma whne_nored {l} n u :
  whne l n -> [ n ⇒ u]< l > -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  all: inversion ne ; subst ; clear ne.
  2: auto.
  9: induction n0 ; auto ;  now inversion red.
  all: try now inv_whne.
  clear i ; revert n0 H ; induction n ; cbn in * ; intros.
  - destruct n0.
    * inversion H0 ; subst ; simpl in H ;  rewrite H in H0 ; now inversion H0.
    * change (match nSucc (S n0) t with | tSucc _ => False | _ => True end).
      now rewrite H.
  - induction n0 ; cbn in *.
    * rewrite H in H0 ; inversion H0.
    * apply (IHn n0) ; now apply tSucc_inj.
Qed.

Lemma alphawhne_nored {l} n u :
  alphawhne l n -> [ n ⇒ u]< l > -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  all: inversion ne ; subst ; clear ne.
  2: auto.
  9:{ induction n0 ; now inversion red. }
  all: try now inv_whne.
  - eapply notinLConnotinLCon.
    exact H0.
    rewrite (nattoterminj H) ; exact i.
  - clear i. induction n ; cbn in *.
    + now inv_whne.
    + now inv_whne.
Qed.

Lemma whnf_nored {l} n u :
  whnf l n -> [n ⇒ u]< l > -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  2,3,6,7: inversion nf; subst; inv_whne; subst; apply IHred; now constructor.
  all: inversion nf; subst; try inv_whne; subst; try now inv_whne ; subst.
  - apply IHred. now eapply containsnewhnf.
  - apply IHred.
    now eapply whnfnattoterm.
  - now eapply alphawhne_nored.
  - now eapply containsnenattoterm.
  - eapply notinLConnotinLCon.
    exact H1.
    rewrite (nattoterminj H0).
    exact i.
  - induction n ; now inv_whne.
Qed.

(** *** Determinism of reduction *)

Lemma ored_det {l t u v} :
  [ t ⇒ u]< l > -> [t ⇒ v]< l > ->
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
  - inversion red'; subst.
    2,3: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst.
    f_equal; eauto.
  - inversion red'; subst.
    2,3: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red' ; subst.
    + now rewrite (IHred n'0 H0).
    + exfalso ; eapply whnf_nored ; tea.
      now eapply whnfnattoterm.
  - inversion red' ; subst.
    + exfalso ; eapply whnf_nored ; tea.
      now eapply whnfnattoterm.
    + erewrite (uniqueinLCon (pi2 l) i) ; trivial.
      rewrite (nattoterminj H) in H0 ; assumption.
Qed.

Lemma red_whne {l} t u : [t ⇒* u]< l > -> whne l t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whne_nored.
Qed.

Lemma red_whnf {l} t u : [t ⇒* u]< l > -> whnf l t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Lemma whred_red_det {l} t u u' :
  whnf l u ->
  [t ⇒* u]< l > -> [t ⇒* u']< l > ->
  [u' ⇒* u]< l >.
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

Corollary whred_det {l} t u u' :
  whnf l u -> whnf l u' ->
  [t ⇒* u]< l > -> [t ⇒* u']< l > ->
  u = u'.
Proof.
  intros.
  eapply red_whnf ; tea.
  now eapply whred_red_det.
Qed.

(** *** Stability by weakening *)

Lemma oredalg_wk {l} (ρ : nat -> nat) (t u : term) :
[t ⇒ u]< l > ->
[t⟨ρ⟩ ⇒ u⟨ρ⟩]< l >.
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  2-5,6,7,8,9,10: cbn; asimpl; now econstructor.
  - cbn ; asimpl.
    evar (t' : term).
    replace (subst_term _ t) with t'.
    all: subst t'.
    1: econstructor.
    now asimpl.
  - cbn.
    rewrite <- bool_to_term_ren.
    rewrite <- nat_to_term_ren.
    now apply alphaRed.
Qed.

Lemma credalg_wk {l} (ρ : nat -> nat) (t u : term) :
[t ⇒* u]< l > ->
[t⟨ρ⟩ ⇒* u⟨ρ⟩]< l >.
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.

(** Derived rules *)

Lemma redalg_app {t t' u} : [t ⇒* t'] -> [tApp t u ⇒* tApp t' u].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natElim {P hs hz t t'} : [t ⇒* t'] -> [tNatElim P hs hz t ⇒* tNatElim P hs hz t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natEmpty {P t t'} : [t ⇒* t'] -> [tEmptyElim P t ⇒* tEmptyElim P t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.
