
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application Universe NormalRed SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var List.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.




Section ListElimRed.
Context `{GenericTypingProperties}.

(* Definition elimListProp {Γ l} A {RLiA : [Γ ||-List<l> tList A]} 
  (P hnil hcons t : term) (Rt : ListProp Γ _ RLiA t) : term.
Proof.
  destruct Rt as [  | | x ].
  - exact hnil.
  - exact (tApp (tApp (tApp hcons hd) tl) (tListElim A P hnil hcons tl)).
  - exact (tListElim A P hnil hcons x).
Defined. *)

Context {Γ l A P hnil hcons}
  (hP : [Γ,, tList A |- P])
  (RA : [Γ ||-<l> A])
  (RLiA0 : [Γ ||-List<l> tList A])
  (RLiA := normList0 RLiA0)
  (RLA := LRList' RLiA)
  (RP : forall t, [Γ ||-<l> t : _ | RLA] -> [Γ ||-<l> P[t..]])
  (RPeq : forall t u (Rt : [Γ ||-<l> t : _ | RLA]), [Γ ||-<l> u : _ | RLA] -> [Γ ||-<l> t ≅ u : _ | RLA] -> [Γ ||-<l> P[t..] ≅ P[u..]| RP t Rt])
  (Rtynil : [Γ ||-<l> P[(tNil A)..]])
  (Rhnil : [Γ ||-<l> hnil : _ | Rtynil])
  (Rtycons : [Γ ||-<l> elimConsHypTy A P])
  (Rhcons : [Γ ||-<l> hcons : _ | Rtycons]).

Definition listElimProp  t (Rt : ListProp Γ _ RLiA t) : term.
Proof.
  destruct Rt as [  | | x ].
  - exact hnil.
  - exact (tApp (tApp (tApp hcons hd) tl) (tListElim A P hnil hcons tl)).
  - exact (tListElim A P hnil hcons x).
Defined.

Lemma elimListRed : 
  (forall t (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt),
    [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × 
    [Γ ||-<l> tListElim A P hnil hcons t ≅ tListElim A P hnil hcons (ListRedTm.nf Rt) : _ | RPl]) ×
  (forall t (Pt : ListProp Γ _ RLiA t) (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt),
    [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × [Γ ||-<l> tListElim A P hnil hcons t ≅ listElimProp t Pt : _ | RPl]).
Proof.
  eapply ListRedInduction.
  + intros.
    eapply redSubstTerm; cycle 1.
    1: destruct red; escape; now eapply redtm_listelim.
    pose proof (wnf := ListProp_whnf prop).
    set (Rt := Build_ListRedTm _ _ _ _  : [Γ ||-<l> t : _ | RLA]).
    pose proof (redTmFwdConv Rt red wnf) as [Rnf Rtnf].
    eapply LRTmRedConv.
    1: unshelve eapply RPeq; cycle 3; [now eapply LRTmEqSym|..]; tea.
    apply (fst (X _)).
  + intros.
    eapply redSubstTerm; cycle 1.
    1: cbn; escape; now eapply redtm_listElimNil.
    


End ListElimRed.
