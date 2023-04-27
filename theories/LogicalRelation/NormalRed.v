
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction.

Set Universe Polymorphism.

Section Normalization.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Program Definition normRedΠ0 {wl Γ F G l} (h : [Γ ||-Π<l> tProd F G]< wl >)
  : [Γ ||-Π<l> tProd F G]< wl > :=
  {| PiRedTyPack.dom := F ;
    PiRedTyPack.cod := G |}.
Obligation 1.
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e.
  destruct h as [?????? domRed codRed codExt] ; 
    intros; cbn in *; subst; eassumption + now eapply domRed.
Defined. 
Obligation 2.
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e.
  destruct h as [?????? domRed codRed codExt] ; 
    intros; cbn in *; subst; eassumption + now eapply domRed.
Defined.
Obligation 3.

  intros;
  assert (wΠ : whnf (tProd F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e.
  destruct h as [?????? domRed codRed codExt] ; 
    intros; cbn in *; subst; eassumption + now eapply domRed.
Defined.
Obligation 4.
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e.
  destruct h as [?????? domRed codRed codExt] ; 
    intros; cbn in *; subst; eassumption + now eapply domRed.
Defined.
Obligation 5.
  destruct h as [??????? domRed codRed codExt] ; 
    intros; cbn in *; subst. exact domN.
Defined.
Obligation 6. 
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e.
  destruct h as [??????? domRed codRed codExt] ; 
    intros; cbn in *; subst; try eassumption.
  eapply domRed ; try eassumption.
Defined.
Obligation 7.
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e.
  destruct h as [??????? domRed codomN codRed codExt].
  intros ; cbn in *.
  unshelve eapply codomN ; try eassumption.
  subst.
  now irrelevance.
Defined.
Obligation 8.
  destruct h as [??????? domRed codomN ? codRed codExt] ; 
    intros; cbn in *.
  now eapply codomN_Ltrans.
Defined.

Obligation 9.
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor.
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ).
  symmetry in e; injection e; clear e.
  destruct h as [??????? domRed codomN ? codRed codExt] ; 
    intros; cbn in *.
  subst.
  unshelve eapply codRed ;[exact wl' |..] ; tea.
Defined.

Next Obligation.
  intros;
  assert (wΠ : whnf (tProd F G)) by constructor.
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ).
  symmetry in e; injection e; clear e.
  destruct h as [??????? domRed codomN ? codRed codExt] ; 
    intros; cbn in *.
  subst.
  irrelevance0 ; try reflexivity.
  unshelve eapply codExt ; [exact wl' | ..] ; try eassumption ; tea ; irrelevance.
Qed.

  
Definition normRedΠ {wl Γ F G l} (h : [Γ ||-<l> tProd F G]< wl >)
  : [Γ ||-<l> tProd F G]< wl > :=
  LRPi' (normRedΠ0 (invLRΠ h)).

#[program]
Definition normLambda {wl Γ F F' G t l RΠ} 
  (Rlam : [Γ ||-<l> tLambda F' t : tProd F G | normRedΠ RΠ ]< wl >) :
  [Γ ||-<l> tLambda F' t : tProd F G | normRedΠ RΠ ]< wl > :=
  {| PiRedTm.nf := tLambda F' t |}.
Obligation 5.
  destruct Rlam as [??????? app eqq]; cbn in *; try exact redN.
Defined.
Obligation 6.
  intros;
  pose proof (e := redtmwf_whnf (PiRedTm.red Rlam) whnf_tLambda);
    destruct Rlam as [??????? app eqq]; cbn in *.
  unshelve eapply appN ; try eassumption ; subst ; try eassumption.
Defined.
Obligation 7.
  intros;
    destruct Rlam as  [???????? app eqq].
  unshelve eapply appN_Ltrans ; try assumption.
Defined.

Solve All Obligations with
  intros;
  pose proof (e := redtmwf_whnf (PiRedTm.red Rlam) whnf_tLambda);
  destruct Rlam as [???????? app eqq]; cbn in *; try exact redN ; subst;
first [eapply app ; eassumption | now eapply eqq| eassumption].
  

End Normalization.

(** ** Tactics for normalizing the proof relevant components of a reducible type *)

(* Normalizes a term reducible at a Π type *)

Ltac normRedΠin id X :=
  let g := type of X in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _]< _ > =>
    pose (id := normRedΠ0 (invLRΠ R));
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRPi' id]< _ >) by irrelevance; clear X'
  end.

Goal forall `{GenericTypingProperties} wl Γ A B l R f (Rf : [Γ ||-<l> f : arr A B | R]< wl >), True.
Proof.
  intros.
  normRedΠin ΠAB Rf.
  constructor.
Qed.

(* Normalizes a goal reducible at a Π type *)

Ltac normRedΠ id :=
  let G := fresh "G" in
  set (G := _);
  let g := eval unfold G in G in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _]< _ > =>
    pose (id := normRedΠ0 (invLRΠ R)); subst G;
    enough [_ ||-<_> t : _ | LRPi' id]< _ > by irrelevance
  end.

