(* From Coq.Classes Require Import CRelationClasses. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity Universe Escape Irrelevance.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redSubst {Γ A B l} :
  [Γ ||-<l> B] ->
  [Γ |- A :⇒*: B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros RB; revert A; pattern l, Γ, B, RB; apply LR_rect_TyUr; clear l Γ B RB; intros l Γ.
  - intros ? [] ? redA. unshelve eexists.
    + apply LRU_; econstructor; tea; etransitivity; tea.
    + now constructor.
  - intros B [t] A ?. unshelve eexists.
    + apply LRne_; exists t; tea; etransitivity; tea.
    + exists t; tea.
  - intros B [na dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRPi'; unshelve eexists na dom cod _ _; tea; etransitivity; tea.
    + unshelve eexists na dom cod; tea; cbn.
      1,2: intros; apply LRTyEqRefl_.
Qed.

Lemma redSubstTerm {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t :⇒*: u : A ] ->
  [Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  revert t u; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA; intros l Γ.
  - intros ? h ?? ru' redtu; pose (ru := ru'); destruct ru' as [T].
    assert [Γ |- A ≅ U] by (destruct h; gen_typing).
    assert (redtu' : [Γ |-[ ta ] t :⇒*: u]) by gen_typing.
    destruct (redSubst (A:=t) (RedTyRecFwd h rel) redtu') as [rTyt0].
    pose proof (rTyt := RedTyRecBwd h rTyt0).
    unshelve refine (let rt : [LRU_ h | Γ ||- t : A]:= _ in _).
    1: exists T; tea; etransitivity; gen_typing.
    split; tea; exists rt ru rTyt; tea.
    apply TyEqRecFwd; irrelevance.
  - intros ???? ru' ?; pose (ru := ru'); destruct ru' as [n].
    assert [Γ |-[ ta ] t :⇒*: u : neRedTy.ty neA]. {
      eapply redtmwf_conv; tea. 
      destruct neA; cbn in *.
      eapply convty_exp.
       2: apply redtywf_refl; gen_typing.
       2: apply convty_term; now apply convtm_convneu.
       gen_typing.
    }
    unshelve refine (let rt : [LRne_ l neA | Γ ||- t : A] := _ in _).
    1: exists n; tea; etransitivity; tea.
    split; tea; exists n n; tea; etransitivity; tea. 
  - intros ? ΠA ihdom ihcod ?? ru' ?; pose (ru := ru'); destruct ru' as [f].
    assert [Γ |-[ ta ] t :⇒*: u : PiRedTyPack.prod ΠA].
    1: {
      eapply redtmwf_conv; tea. 
      destruct ΠA as [??? []]. cbn in *.
      eapply convty_exp; tea.
      now apply redtywf_refl.
    }
    unshelve refine (let rt : [LRPi' ΠA | Γ ||- t : A] := _ in _).
    1: exists f; tea; etransitivity; tea.
    split; tea; exists rt ru; tea.
    intros; cbn. apply eq; tea.
    now apply LREqTermRefl_.
Qed.


(* KM: We do not have a 1 step typed reduction relation, so I'm not sure whether
  the following lemma would make sense (and I don't see how to prove it)
*)
(* Lemma redSubst1 {Γ A B l} :
  [A ⇒ B] ->
  [Γ |- A] ->
  [Γ ||-<l> B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros ? wfA RB.
  apply redSubst; tea; constructor; tea.
  (* Stuck: no way to turn a one step untyped reduction to a typed one *)
  *)

End Reduction.