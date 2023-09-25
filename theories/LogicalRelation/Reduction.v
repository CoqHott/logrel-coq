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
  [Γ |- A ⤳* B] ->
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
      unshelve econstructor;intros; apply reflLRTyEq.
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
      unshelve econstructor;intros; apply reflLRTyEq.
  - intros ? [ty lhs rhs] ih _ X redX; unshelve eexists.
    + apply LRId'; unshelve eexists ty lhs rhs _ _; tea.
      etransitivity; tea; constructor; tea; gen_typing.
    + exists ty lhs rhs; tea; eapply reflLRTyEq.
Qed.


Lemma redwfSubst {Γ A B l} :
  [Γ ||-<l> B] ->
  [Γ |- A :⤳*: B] ->
  ∑ (RA : [Γ ||-<l> A]), [Γ ||-<l> A ≅ B | RA].
Proof.
  intros ? []; now eapply redSubst.
Qed.

Lemma redSubstTerm {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t ⤳* u : A ] ->
  [Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  revert t u; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA; intros l Γ.
  - intros ? h ?? ru' redtu; pose (ru := ru'); destruct ru' as [T].
    assert [Γ |- A ≅ U] by (destruct h; gen_typing).
    assert [Γ |- t : U] by (eapply ty_conv; [gen_typing| now escape]).
    assert (redtu' : [Γ |-[ ta ] t ⤳* u]) by gen_typing.
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
      eapply convty_exp.
       2: apply redtywf_refl; gen_typing.
       2: apply convty_term; now apply convtm_convneu.
       gen_typing.
    }
    assert [Γ |-[ ta ] t ⤳* u : neRedTy.ty neA] by (eapply redtm_conv; tea). 
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
    assert [Γ |-[ ta ] t ⤳* u : ΠA.(outTy)] by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : ΠA.(outTy)] by (eapply ty_conv; gen_typing).
    unshelve refine (let rt : [LRPi' ΠA | Γ ||- t : A] := _ in _).
    1: exists f; tea; constructor; destruct red; tea; etransitivity; tea.
    split; tea; exists rt ru; tea.
    intros; cbn. apply eq; tea.
    now apply reflLRTmEq.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tNat] by (destruct NA; gen_typing).
    assert [Γ |- t :⤳*: nf : tNat]. 1:{
      constructor. 1: gen_typing.
      etransitivity. 2: gen_typing.
      now eapply redtm_conv.
    }
    split; econstructor; tea.
    now eapply reflNatRedTmEq.
  - intros ? NA t ? Ru red; inversion Ru; subst.
    assert [Γ |- A ≅ tEmpty] by (destruct NA; gen_typing).
    assert [Γ |- t :⤳*: nf : tEmpty]. 1:{
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
    assert [Γ |-[ ta ] t ⤳* u : PA.(outTy)] by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : PA.(outTy)] by (eapply ty_conv; gen_typing).
    unshelve refine (let rt : [LRSig' PA | Γ ||- t : A] := _ in _).
    1: unshelve eexists p _; tea; constructor; destruct red; tea; etransitivity; tea.
    split; tea; exists rt ru; tea; intros; cbn; now apply reflLRTmEq.
  - intros ? IA ih _ t u [nf ?? prop] redt.
    assert [Γ |- A ≅ IA.(IdRedTy.outTy)] by (destruct IA; unfold IdRedTy.outTy; cbn; gen_typing).
    assert [Γ |-[ ta ] t ⤳* u : IA.(IdRedTy.outTy)] by now eapply redtm_conv. 
    assert [Γ |-[ ta ] t : IA.(IdRedTy.outTy)] by (eapply ty_conv; gen_typing).
    assert [Γ |-[ ta ] t :⤳*: nf : IA.(IdRedTy.outTy)].
    1: constructor; [apply red|etransitivity; tea; apply red].
    split; eexists; tea.
    now eapply reflIdPropEq.
Qed.

Lemma redSubstTerm' {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t ⤳* u : A ] ->
  [Γ ||-<l> t : A | RA] ×  
  [Γ ||-<l> u : A | RA] ×
  [Γ ||-<l> t ≅ u : A | RA].
Proof.
  intros. assert ([Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA]) by now eapply redSubstTerm.
  now repeat split.
Qed.


Lemma redwfSubstTerm {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t :⤳*: u : A ] ->
  [Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  intros ? []; now eapply redSubstTerm.
Qed.


Lemma redFwd {Γ l A B} : [Γ ||-<l> A] -> [Γ |- A :⤳*: B] -> whnf B -> [Γ ||-<l> B].
Proof.
  intros RA; revert B; pattern l, Γ, A, RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ??? [??? red] ? red' ?. 
    eapply LRU_.  unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor. econstructor; tea. eapply redtywf_refl; gen_typing.
  - intros ??? [? red] ? red' ?.
    eapply LRne_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [?? red] ?? ? red' ?.
    eapply LRPi'. 
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor.
    + eapply redtywf_refl; gen_typing.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros ??? [red] ? red' ?.
    eapply LRNat_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [red] ? red' ?.
    eapply LREmpty_.
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor; tea.
    eapply redtywf_refl; gen_typing.
  - intros ??? [?? red] ?? ? red' ?.
    eapply LRSig'. 
    unshelve erewrite (redtywf_det _ _ red' red); tea.
    1: constructor.
    econstructor.
    + eapply redtywf_refl; gen_typing.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros ??? [???? red] _ _ ? red' ?.
    eapply LRId'; unshelve erewrite (redtywf_det _ _ red' red); tea; [constructor|].
    econstructor; tea. eapply redtywf_refl; gen_typing.
Qed.

Lemma redFwdConv {Γ l A B} (RA : [Γ ||-<l> A]) : [Γ |- A :⤳*: B] -> whnf B -> [Γ ||-<l> B] × [Γ ||-<l> A ≅ B | RA].
Proof.
  intros red wh. pose (RB := redFwd RA red wh).
  destruct (redwfSubst RB red).
  split; tea; irrelevance.
Qed.

Lemma IdProp_whnf {Γ l A} (IA : [Γ ||-Id<l> A]) t : IdProp IA t -> whnf t.
Proof. intros []; constructor; destruct r; now eapply convneu_whne. Qed.

Lemma redTmFwd {Γ l A t u} {RA : [Γ ||-<l> A]} : 
  [Γ ||-<l> t : A | RA] -> [Γ |- t :⤳*: u : A] -> whnf u -> [Γ ||-<l> u : A | RA].
Proof.
  revert t u; pattern l,Γ,A,RA; apply LR_rect_TyUr; clear l Γ A RA.
  - intros ?????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply isType_whnf.
    econstructor; tea.
    1: eapply redtmwf_refl; gen_typing.
    eapply RedTyRecBwd. eapply redFwd. 
    2,3: gen_typing.
    now eapply RedTyRecFwd.
  - intros ??? ??? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: constructor; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ???????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: eapply isFun_whnf; destruct isfun; constructor; tea; now eapply convneu_whne.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ?????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply NatProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ?????? Rt red' ?; inversion Rt; subst.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply EmptyProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
    Unshelve. 2: tea.
  - intros ???????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply isPair_whnf, isWfPair_isPair.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
  - intros ???????? [? red] red' ?.
    unshelve erewrite (redtmwf_det _ _ red' red); tea.
    1: now eapply IdProp_whnf.
    econstructor; tea.
    eapply redtmwf_refl; gen_typing.
Qed.

Lemma redTmFwdConv {Γ l A t u} {RA : [Γ ||-<l> A]} : 
  [Γ ||-<l> t : A | RA] -> [Γ |- t :⤳*: u : A] -> whnf u -> [Γ ||-<l> u : A | RA] × [Γ ||-<l> t ≅ u : A | RA].
Proof.
  intros Rt red wh. pose (Ru := redTmFwd Rt red wh).
  destruct (redwfSubstTerm RA Ru red); now split.
Qed.

End Reduction.
