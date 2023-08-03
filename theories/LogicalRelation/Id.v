From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Weakening Neutral Escape Reflexivity NormalRed Reduction Transitivity Universe.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section IdRed.
  Context `{GenericTypingProperties}.

  Lemma mkIdRedTy {Γ l A} :
    forall (ty lhs rhs  : term)
      (tyRed : [Γ ||-<l> ty]),
      [Γ |- A :⇒*: tId ty lhs rhs] ->
      [tyRed | Γ ||- lhs : _] ->
      [tyRed | Γ ||- rhs : _] ->
      [Γ ||-Id<l> A].
  Proof.
    intros; unshelve econstructor; cycle 3; tea.
    1: intros; now eapply wk.
    2,3: now eapply reflLRTmEq.
    2: apply perLRTmEq.
    - eapply  convty_Id. 
      1: eapply escapeEq; now eapply reflLRTyEq.
      1,2: eapply escapeEqTerm; now eapply reflLRTmEq.
    - cbn; intros; irrelevance0; [|now eapply wkEq].
      bsimpl; rewrite H11; now bsimpl.
      Unshelve. all:tea.
    - cbn; intros; irrelevance0; [| now eapply wkTerm].
      bsimpl; rewrite H11; now bsimpl.
      Unshelve. all:tea.
    - cbn; intros; irrelevance0; [| now eapply wkTermEq].
      bsimpl; rewrite H11; now bsimpl.
      Unshelve. all:tea.
  Defined.

  Lemma IdRed0 {Γ l A t u} (RA : [Γ ||-<l> A]) :
      [RA | Γ ||- t : _] ->
      [RA | Γ ||- u : _] ->
      [Γ ||-Id<l> tId A t u].
  Proof.
    intros; eapply mkIdRedTy.
    1: eapply redtywf_refl; escape; gen_typing.
    all: tea.
  Defined.
  
  Lemma IdRed {Γ l A t u} (RA : [Γ ||-<l> A]) :
      [RA | Γ ||- t : _] ->
      [RA | Γ ||- u : _] ->
      [Γ ||-<l> tId A t u].
  Proof. intros; apply LRId'; now eapply IdRed0. Defined.
  
  Lemma IdRedTy_inv {Γ l A t u} (RIA : [Γ ||-Id<l> tId A t u]) :
    [× A = RIA.(IdRedTy.ty), t = RIA.(IdRedTy.lhs) & u = RIA.(IdRedTy.rhs)].
  Proof.
    pose proof (redtywf_whnf RIA.(IdRedTy.red) whnf_tId) as e; injection e; now split.
  Qed.

  Lemma IdCongRed {Γ l A A' t t' u u'} 
    (RA : [Γ ||-<l> A])
    (RIA : [Γ ||-<l> tId A t u]) :
    [Γ |- tId A' t' u'] ->
    [RA | _ ||- _ ≅ A'] ->
    [RA | _ ||- t ≅ t' : _] ->
    [RA | _ ||- u ≅ u' : _] ->
    [RIA | _ ||- _ ≅ tId A' t' u'].
  Proof.
    intros.
    enough [LRId' (invLRId RIA) | _ ||- _ ≅ tId A' t' u'] by irrelevance.
    pose proof (IdRedTy_inv (invLRId (RIA))) as [ety elhs erhs].
    econstructor.
    + now eapply redtywf_refl.
    + unfold_id_outTy; rewrite <- ety, <- elhs, <- erhs; eapply convty_Id; now escape.
    + irrelevance.
    + cbn; rewrite <- elhs; irrelevance.
    + cbn; rewrite <- erhs; irrelevance.
  Qed. 
    
  Lemma IdRedU@{i j k l} {Γ l A t u}
      (RU : [LogRel@{i j k l} l | Γ ||- U])
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A]) :
      [RU | Γ ||- A : U] ->
      [RA | Γ ||- t : _] ->
      [RA | Γ ||- u : _] ->
      [RU | Γ ||- tId A t u : U].
  Proof.
    intros RAU Rt Ru.
    enough [LRU_ RU' | _ ||- tId A t u : U] by irrelevance.
    econstructor.
    - eapply redtmwf_refl; escape; now eapply ty_Id.
    - constructor.
    - eapply convtm_Id; eapply escapeEq + eapply escapeEqTerm; now eapply reflLRTmEq + eapply reflLRTyEq.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
    Unshelve. irrelevanceCum.
  Qed.
  
  Lemma IdCongRedU@{i j k l} {Γ l A A' t t' u u'} 
      (RU : [LogRel@{i j k l} l | Γ ||- U])
      (RU' := invLRU RU)
      (RA : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A])
      (RA' : [LogRel@{i j k l} (URedTy.level RU') | Γ ||- A']) :
    [RU | Γ ||- A : U] ->
    [RU | Γ ||- A' : U] ->
    [RU | _ ||- A ≅ A' : U] ->
    [RA | _ ||- t : _] ->
    [RA' | _ ||- t' : _] ->
    [RA | _ ||- t ≅ t' : _] ->
    [RA | _ ||- u : _] ->
    [RA' | _ ||- u' : _] ->
    [RA | _ ||- u ≅ u' : _] ->
    [RU | _ ||- tId A t u ≅ tId A' t' u' : U].
  Proof.
    intros RAU RAU' RAAU' Rt Rt' Rtt' Ru Ru' Ruu'.
    enough [LRU_ RU' | _ ||- tId A t u ≅ tId A' t' u': U] by irrelevance.
    opector.
    - change [LRU_ RU' | _ ||- tId A t u : _].
      enough [RU | _ ||- tId A t u : _] by irrelevance. 
      now unshelve eapply IdRedU.
    - change [LRU_ RU' | _ ||- tId A' t' u' : _]. 
      enough [RU | _ ||- tId A' t' u' : _] by irrelevance. 
      now unshelve eapply IdRedU.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
      Unshelve. clear dependent RA'; irrelevanceCum.
    - pose proof (redtmwf_whnf (URedTm.red u0) whnf_tId) as <-.
      pose proof (redtmwf_whnf (URedTm.red u1) whnf_tId) as <-.
      eapply convtm_Id; now escape.
    - eapply RedTyRecBwd. eapply IdRed; irrelevanceCum.
      Unshelve. irrelevanceCum.
    - eapply TyEqRecFwd.
      eapply LRTyEqIrrelevantCum.
      unshelve eapply IdCongRed; tea.
      + escape; gen_typing.
      + now eapply UnivEqEq.
      Unshelve. now eapply IdRed.
  Qed.



Lemma reflRed {Γ l A x} (RA : [Γ ||-<l> A]) (Rx : [RA | _ ||- x : _]) (RIA : [Γ ||-<l> tId A x x]) :
  [RIA | _ ||- tRefl A x : _].
Proof.
  set (RIA' := invLRId RIA).
  enough [LRId' RIA' | _ ||- tRefl A x : _] by irrelevance.
  pose proof (IdRedTy_inv RIA') as [eA ex ex'].
  assert (e : tId (IdRedTy.ty RIA') (IdRedTy.lhs RIA') (IdRedTy.rhs RIA') = tId A x x).
  1: f_equal; now symmetry.
  econstructor; unfold_id_outTy; cbn; rewrite ?e.
  + eapply redtmwf_refl; eapply ty_refl; now escape.
  + eapply convtm_refl; [eapply escapeEq; eapply reflLRTyEq|eapply escapeEqTerm; now eapply reflLRTmEq].
  + constructor; cbn; irrelevance0; tea.
    1: eapply reflLRTyEq.
    * rewrite <- ex; now eapply reflLRTmEq.
    * rewrite <- ex'; now eapply reflLRTmEq.
  Unshelve.  all: tea.
Qed.

Lemma reflCongRed {Γ l A A' x x'} 
  (RA : [Γ ||-<l> A])
  (TA' : [Γ |- A'])
  (RAA' : [RA | _ ||- _ ≅ A'])
  (Rx : [RA | _ ||- x : _]) 
  (Tx' : [Γ |- x' : A'])
  (Rxx' : [RA | _ ||- x ≅ x' : _]) 
  (RIA : [Γ ||-<l> tId A x x]) :
  [RIA | _ ||- tRefl A x ≅ tRefl A' x' : _].
Proof.
  set (RIA' := invLRId RIA).
  enough [LRId' RIA' | _ ||- tRefl A x ≅ tRefl A' x' : _] by irrelevance.
  pose proof (IdRedTy_inv RIA') as [eA ex ex'].
  assert (e : tId (IdRedTy.ty RIA') (IdRedTy.lhs RIA') (IdRedTy.rhs RIA') = tId A x x).
  1: f_equal; now symmetry.
  assert [Γ |- tId A x x ≅ tId A' x' x'] by (escape ; gen_typing).
  econstructor; unfold_id_outTy; cbn; rewrite ?e.
  1,2: eapply redtmwf_refl.
  1: escape; gen_typing.
  - eapply ty_conv; [| now symmetry]; now eapply ty_refl.
  - eapply convtm_refl; now escape.
  - constructor; cbn; irrelevance0; tea.
    1: apply reflLRTyEq.
    1,2: rewrite <- ex; tea; now eapply reflLRTmEq.
    1,2: rewrite <- ex'; tea; now eapply reflLRTmEq.
  Unshelve. all: tea.
Qed.

