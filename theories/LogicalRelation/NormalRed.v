
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction.

Set Universe Polymorphism.

Section Normalization.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Program Definition normRedΠ0 {Γ nF F G l} (h : [Γ ||-Π<l> tProd nF F G])
  : [Γ ||-Π<l> tProd nF F G] :=
  {| PiRedTyPack.na := nF ; 
     PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with 
  intros;
  assert (wΠ : whnf (tProd nF F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e; 
  destruct h as [??????? domRed codRed codExt] ; 
  intros; cbn in *; subst; eassumption + now eapply domRed + 
  (unshelve eapply codRed ; tea ; irrelevance)
  + ( irrelevance0; [reflexivity| unshelve eapply codExt; tea]; irrelevance).

Definition normRedΠ {Γ nF F G l} (h : [Γ ||-<l> tProd nF F G])
  : [Γ ||-<l> tProd nF F G] :=
  LRPi' (normRedΠ0 (invLRΠ h)).

#[program]
Definition normLambda {Γ nF F nF' F' G t l RΠ} 
  (Rlam : [Γ ||-<l> tLambda nF' F' t : tProd nF F G | normRedΠ RΠ ]) :
  [Γ ||-<l> tLambda nF' F' t : tProd nF F G | normRedΠ RΠ ] :=
  {| PiRedTm.nf := tLambda nF' F' t |}.
Solve All Obligations with
  intros;
  pose proof (e := redtmwf_whnf (PiRedTm.red Rlam) whnf_tLambda);
  destruct Rlam as [???? app eqq]; cbn in *; subst;
  first [eapply app | now eapply eqq| eassumption].

End Normalization.

(** ** Tactics for normalizing the proof relevant components of a reducible type *)

(* Normalizes a term reducible at a Π type *)

Ltac normRedΠin id X :=
  let g := type of X in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _] =>
    pose (id := normRedΠ0 (invLRΠ R));
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRPi' id]) by irrelevance; clear X'
  end.

Goal forall `{GenericTypingProperties} Γ A B l R f (Rf : [Γ ||-<l> f : arr A B | R]), True.
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
  | [ LRAd.pack ?R | _ ||- ?t : _] =>
    pose (id := normRedΠ0 (invLRΠ R)); subst G;
    enough [_ ||-<_> t : _ | LRPi' id] by irrelevance
  end.

