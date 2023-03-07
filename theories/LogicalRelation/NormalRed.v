
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation DeclarativeInstance.
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
  LRPi' _ (normRedΠ0 (invLRΠ h)).


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
