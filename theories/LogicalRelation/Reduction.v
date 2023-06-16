(* From Coq.Classes Require Import CRelationClasses. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Universe Escape Irrelevance.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma redSubst {Γ A B l} :
  [Γ ||-<l> B] ->
  [Γ |- A ⇒* B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros RB; revert A; pattern l, Γ, B, RB; apply LR_rect_TyUr; clear l Γ B RB; intros l Γ.
  - intros ? [] ? redA. unshelve eexists.
    + apply LRU_; econstructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [t] A ?. unshelve eexists.
    + apply LRne_; exists t; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + exists t; tea.
  - intros B [dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRPi'; unshelve eexists dom cod; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + unshelve eexists dom cod; tea; cbn.
      unshelve econstructor;intros; apply LRTyEqRefl_.
  - intros B [red] A ?; unshelve eexists.
    + apply LRNat_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [red] A ?; unshelve eexists.
    + apply LREmpty_; constructor; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + now constructor.
  - intros B [dom cod] A ? ihdom ihcod; cbn in *; unshelve eexists.
    + apply LRSig'; unshelve eexists dom cod; tea; etransitivity; tea.
      constructor; tea; gen_typing.
    + unshelve eexists dom cod; tea; cbn.
      unshelve econstructor;intros; apply LRTyEqRefl_.
  - intros B [par] ih ? ?; cbn in *; unshelve eexists.
    + apply LRList'; exists par; tea; etransitivity; tea; constructor; tea; gen_typing.
    + exists par; tea; cbn; intros; apply LRTyEqRefl_.
Qed.


Lemma redwfSubst {Γ A B l} :
  [Γ ||-<l> B] ->
  [Γ |- A :⇒*: B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros ? []; now eapply redSubst.
Qed.

Lemma redSubstTerm {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t ⇒* u : A ] ->
  [Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  revert t u; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA; intros l Γ.
  - intros ? h ?? ru' redtu; pose (ru := ru'); destruct ru' as [T].
    assert [Γ |- A ≅ U] by (destruct h; gen_typing).
    assert [Γ |- t : U] by (eapply ty_conv; [gen_typing| now escape]).
    assert (redtu' : [Γ |-[ ta ] t ⇒* u]) by gen_typing.
    destruct (redSubst (A:=t) (RedTyRecFwd h rel) redtu') as [rTyt0].
    pose proof (rTyt := RedTyRecBwd h rTyt0).
    unshelve refine (let rt : [LRU_ h | Γ ||- t : A]:= _ in _).
    + exists T; tea; constructor; destruct red; tea.
      etransitivity; tea; eapply redtm_conv; tea; now escape.
    + split; tea; exists rt ru rTyt; tea.
      apply TyEqRecFwd; irrelevance.
  - intros ???? ru' ?; pose (ru := ru'); destruct ru' as [n].
    assert [Γ |- A ≅ neRedTy.ty neA]. 1:{
      destruct neA; cbn in *.
      gen_typing.
    }
    assert [Γ |-[ ta ] t ⇒* u : neRedTy.ty neA] by (eapply redtm_conv; tea). 
    assert [Γ |-[ ta ] t : neRedTy.ty neA] by (eapply ty_conv; tea; gen_typing). 
    unshelve refine (let rt : [LRne_ l neA | Γ ||- t : A] := _ in _).
    + exists n; tea; destruct red; constructor; tea; now etransitivity.
    + split; tea; exists n n; tea; destruct red; constructor; tea; now etransitivity. 
  - intros ? ΠA ihdom ihcod ?? ru' ?; pose (ru := ru'); destruct ru' as [f].
    assert [Γ |- A ≅ ΠA.(outTy)]. 1:{
      destruct ΠA as [?? []]. cbn in *.
      eapply convty_exp; tea.
      now apply redtywf_refl.
    }
    assert [Γ |-[ ta ] t ⇒* u : ΠA.(outTy)] by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : ΠA.(outTy)] by (eapply ty_conv; gen_typing).
    unshelve refine (let rt : [LRPi' ΠA | Γ ||- t : A] := _ in _).
    1: exists f; tea; constructor; destruct red; tea; etransitivity; tea.
    split; tea; exists rt ru; tea.
    intros; cbn. apply eq; tea.
    now apply LREqTermRefl_.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tNat] by (destruct NA; gen_typing).
    assert [Γ |- t :⇒*: nf : tNat]. 1:{
      constructor. 1: gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    split; econstructor; tea.
    now eapply reflNatRedTmEq.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tEmpty] by (destruct NA; gen_typing).
    assert [Γ |- t :⇒*: nf : tEmpty]. 1:{
      constructor. 
      1: eapply ty_conv; gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    split; econstructor; tea.
    now eapply reflEmptyRedTmEq.
    Unshelve. 2: tea.
  - intros ? PA ihdom ihcod ?? ru' ?; pose (ru := ru'); destruct ru' as [p].
    assert [Γ |- A ≅ PA.(outTy)]. 1:{
      destruct PA as [?? []]. cbn in *.
      eapply convty_exp; tea.
      now apply redtywf_refl.
    }
    assert [Γ |-[ ta ] t ⇒* u : PA.(outTy)] by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : PA.(outTy)] by (eapply ty_conv; gen_typing).
    unshelve refine (let rt : [LRSig' PA | Γ ||- t : A] := _ in _).
    1: unshelve eexists p _; tea; constructor; destruct red; tea; etransitivity; tea.
    split; tea; exists rt ru; tea; intros; cbn; now apply LREqTermRefl_.
  - intros ? LA ih ? ? ru ?.
    assert ([Γ |- A ≅ tList (ListRedTy.par LA)]) by (destruct LA; cbn in *; gen_typing).
    inversion ru; subst.
    unshelve epose (Rt := _ : [LRList' LA | Γ ||- t : A]).
    { eexists; cycle 1; tea; etransitivity; tea; eapply redtmwf_conv; tea.
      constructor; tea; now escape. }
    split.
    + assumption.
    + unshelve eexists.
      * assumption.
      * now econstructor.
      * cbn. eassumption.
      * cbn. now eapply ListRedTmEqRefl.
Qed.

Lemma redwfSubstTerm {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t :⇒*: u : A ] ->
  [Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  intros ? []; now eapply redSubstTerm.
Qed.


Lemma redFwd {Γ l A B} : [Γ ||-<l> A] -> [Γ |- A :⇒*: B] -> whnf B -> [Γ ||-<l> B].
Proof.
  intros RA; revert B; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ??? [??? red] ? red' ?. 
    eapply LRU_.  unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor. econstructor; tea. eapply redtywf_refl; gen_typing.
  - intros ??? [? red] ? red' ?.
    eapply LRne_.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [?? red] ?? ? red' ?.
    eapply LRPi'. 
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [red] ? red' ?.
    eapply LRNat_.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [red] ? red' ?.
    eapply LREmpty_.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [?? red] ?? ? red' ?.
    eapply LRSig'. 
    econstructor; tea.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor.
    eapply redtywf_refl; gen_typing.
  - intros ??? [? red] ?? red' ?.
    eapply LRList'.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
Qed.

Lemma redFwdConv {Γ l A B} (RA : [Γ ||-<l> A]) : [Γ |- A :⇒*: B] -> whnf B -> [Γ ||-<l> B] × [Γ ||-<l> A ≅ B | RA].
Proof.
  intros red wh. pose (RB := redFwd RA red wh).
  destruct (redwfSubst RB red).
  split; tea; irrelevance.
Qed.

Lemma redTmFwd {Γ l A t u} {RA : [Γ ||-<l> A]} : 
  [Γ ||-<l> t : A | RA] -> [Γ |- t :⇒*: u : A] -> whnf u -> [Γ ||-<l> u : A | RA].
Proof.
  revert t u; pattern l,Γ,A,RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ?????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: now eapply isType_whnf.
    econstructor; tea.
    1: eapply redtmwf_refl; gen_typing.
    eapply RedTyRecBwd. eapply redFwd. 
    2,3: gen_typing.
    now eapply RedTyRecFwd.
  - intros ??? ??? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ???????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: now eapply isFun_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ?????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: now eapply NatProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ?????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: now eapply EmptyProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    Unshelve. 2: tea.
  - intros ???????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: now eapply isPair_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ??????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ red' red); tea.
    1: now eapply ListProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
Qed.

Lemma redTmFwdConv {Γ l A t u} {RA : [Γ ||-<l> A]} : 
  [Γ ||-<l> t : A | RA] -> [Γ |- t :⇒*: u : A] -> whnf u -> [Γ ||-<l> u : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  intros Rt red wh. pose (Ru := redTmFwd Rt red wh).
  destruct (redwfSubstTerm RA Ru red); now split.
Qed.

End Reduction.
