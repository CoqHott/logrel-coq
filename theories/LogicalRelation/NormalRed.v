
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction.

Set Universe Polymorphism.

Section Normalization.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Program Definition normRedΠ0 {Γ F G l} (h : [Γ ||-Π<l> tProd F G])
  : [Γ ||-Π<l> tProd F G] :=
  {| PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with 
  intros; pose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tProd);
  symmetry in e; injection e; clear e; 
  destruct h ; intros; cbn in *; subst; eassumption.

Program Definition normRedΣ0 {Γ F G l} (h : [Γ ||-Σ<l> tSig F G])
  : [Γ ||-Σ<l> tSig F G] :=
  {| PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with 
  intros; pose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tSig);
  symmetry in e; injection e; clear e; 
  destruct h ; intros; cbn in *; subst; eassumption.

Definition normRedΠ {Γ F G l} (h : [Γ ||-<l> tProd F G]) : [Γ ||-<l> tProd F G] :=
  LRPi' (normRedΠ0 (invLRΠ h)).

Definition normRedΣ {Γ F G l} (h : [Γ ||-<l> tSig F G]) : [Γ ||-<l> tSig F G] :=
  LRSig' (normRedΣ0 (invLRΣ h)).

#[program]
Definition normEqRedΣ {Γ F F' G G' l} (h : [Γ ||-<l> tSig F G]) 
  (heq : [Γ ||-<l> _ ≅ tSig F' G' | h]) : [Γ ||-<l> _ ≅ tSig F' G' | normRedΣ h] :=
  {|
    PiRedTyEq.dom := F';
    PiRedTyEq.cod := G';
  |}.
Solve All Obligations with
  intros; assert[Γ ||-<l> _ ≅ tSig F' G' | normRedΣ h] as [?? red] by irrelevance;
  pose proof (e := redtywf_whnf red whnf_tSig);
  symmetry in e; injection e; clear e; 
  destruct h ; intros; cbn in *; subst; eassumption.

#[program]
Definition normLambda {Γ F F' G t l RΠ} 
  (Rlam : [Γ ||-<l> tLambda F' t : tProd F G | normRedΠ RΠ ]) :
  [Γ ||-<l> tLambda F' t : tProd F G | normRedΠ RΠ ] :=
  {| PiRedTm.nf := tLambda F' t |}.
Solve All Obligations with
  intros;
  pose proof (e := redtmwf_whnf (PiRedTm.red Rlam) whnf_tLambda);
  destruct Rlam as [????? app eqq]; cbn in *; subst;
  first [eapply app | now eapply eqq| eassumption].

#[program]
Definition normPair {Γ F F' G G' f g l RΣ} 
  (Rp : [Γ ||-<l> tPair F' G' f g : tSig F G | normRedΣ RΣ ]) :
  [Γ ||-<l> tPair F' G' f g : tSig F G | normRedΣ RΣ ] :=
  {| SigRedTm.nf := tPair F' G' f g |}.
Solve All Obligations with
  intros;
  pose proof (e := redtmwf_whnf (SigRedTm.red Rp) whnf_tPair);
  destruct Rp as [????? fstRed sndRed]; cbn in *; subst;
  first [eapply fstRed | irrelevanceRefl; now unshelve eapply sndRed| eassumption].


End Normalization.

(** ** Tactics for normalizing the proof relevant components of a reducible type *)

(* Normalizes a term reducible at a Π type *)

Ltac normRedΠin X :=
  let g := type of X in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRPi' (normRedΠ0 (invLRΠ R))]) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- _ ≅ ?B] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> _ ≅ B | LRPi' (normRedΠ0 (invLRΠ R))]) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t ≅ u : _ | LRPi' (normRedΠ0 (invLRΠ R))]) by irrelevance; clear X'
  end.

Goal forall `{GenericTypingProperties} Γ A B l R f X
  (RABX : [Γ ||-<l> arr A B ≅ X | R])
  (Rf : [Γ ||-<l> f : arr A B | R])
  (Rff : [Γ ||-<l> f ≅ f : arr A B | R])
, True.
Proof.
  intros.
  normRedΠin Rf.
  normRedΠin Rff.
  normRedΠin RABX.
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

(* Normalizes a term reducible at a Π type *)

Ltac normRedΣin X :=
  let g := type of X in
  match g with
  | [ LRAd.pack ?R | _ ||- ?t : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t : _ | LRSig' (normRedΣ0 (invLRΣ R))]) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- _ ≅ ?B] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> _ ≅ B | LRSig' (normRedΣ0 (invLRΣ R))]) by irrelevance; clear X'
  | [ LRAd.pack ?R | _ ||- ?t ≅ ?u : _] =>
    let X' := fresh X in
    rename X into X' ;
    assert (X : [_ ||-<_> t ≅ u : _ | LRSig' (normRedΣ0 (invLRΣ R))]) by irrelevance; clear X'
  end.
