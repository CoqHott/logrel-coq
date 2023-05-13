From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance.

Set Universe Polymorphism.

Section Transitivity.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.


Lemma transPolyRedEq@{i j k l} {Γ sA sB sC pA pB pC lA lB lC} 
  (RA : PolyRed@{i j k l} Γ lA sA pA)
  (RB : PolyRed@{i j k l} Γ lB sB pB)
  (RC : PolyRed@{i j k l} Γ lC sC pC)
  (RAB : PolyRedEq RA sB pB) 
  (RBC : PolyRedEq RB sC pC)
  (ihdom: forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ])
    (lB : TypeLevel) (B : term) (pB : LRPack@{k} Δ B)
    (lrB : LogRel@{i j k l} lB Δ B (LRPack.eqTy pB) (LRPack.redTm pB) (LRPack.eqTm pB))
    (lC : TypeLevel) (C : term) (pC : LRPack@{k} Δ C)
    (lrC : LogRel@{i j k l} lC Δ C (LRPack.eqTy pC) (LRPack.redTm pC) (LRPack.eqTm pC))
    (RAB : [PolyRed.shpRed RA ρ h | Δ ||- _ ≅ B])
    (RBC : [pB | Δ ||- B ≅ C]), [PolyRed.shpRed RA ρ h | Δ ||- _ ≅ C])
  (ihcod: forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ])
    (ha : [PolyRed.shpRed RA ρ h | Δ ||- a : _])
    (lB : TypeLevel) (B : term) (pB : LRPack@{k} Δ B)
    (lrB : LogRel@{i j k l} lB Δ B (LRPack.eqTy pB) (LRPack.redTm pB) (LRPack.eqTm pB))
    (lC : TypeLevel) (C : term) (pC : LRPack@{k} Δ C)
    (lrC : LogRel@{i j k l} lC Δ C (LRPack.eqTy pC) (LRPack.redTm pC) (LRPack.eqTm pC))
    (RAB : [PolyRed.posRed RA ρ h ha | Δ ||- _ ≅ B])
    (RBC : [pB | Δ ||- B ≅ C]),
  [PolyRed.posRed RA ρ h ha | Δ ||- _ ≅ C])
   :
  PolyRedEq RA sC pC.
Proof.
  assert (RsAC : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
    [PolyRed.shpRed (RA : PolyRed Γ lA sA pA) ρ h | Δ ||- sA⟨ρ⟩ ≅ sC⟨ρ⟩]).
  1:{
    intros; eapply (ihdom _ _ _ _ sB⟨ρ⟩).
    1,2: unshelve eapply LRAd.adequate; now eapply PolyRed.shpRed.
    + eapply (PolyRedEq.shpRed RAB). 
    + eapply (PolyRedEq.shpRed RBC).
  }
  unshelve econstructor; intros.
  1: eapply RsAC.
  unshelve eapply (ihcod _ _ _ _ _ _ pB[a .: ρ >> tRel]).
  5,6: unshelve eapply LRAd.adequate; unshelve eapply PolyRed.posRed.
  4,5,7,8: tea.
  1,2: eapply LRTmRedConv; tea.
  + eapply (PolyRedEq.shpRed RAB). 
  + eapply RsAC.
  + eapply (PolyRedEq.posRed RAB).
  + irrelevanceRefl; unshelve eapply (PolyRedEq.posRed RBC); tea.
    eapply LRTmRedConv; tea; eapply (PolyRedEq.shpRed RAB).
Qed.

Ltac inv_red red red' :=
  let eq := fresh "eq" in
  unshelve epose proof (eq := redtywf_det _ _ _ _ _ _ red red');
  [constructor| constructor|]; injection eq; intros ??; clear eq;  subst.

Lemma transEq@{i j k l} {Γ A B C lA lB lC} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]}
  {RB : [LogRel@{i j k l} lB | Γ ||- B]}
  {RC : [LogRel@{i j k l} lC | Γ ||- C]}
  (RAB : [Γ ||-<lA> A ≅ B | RA])
   (RBC : [Γ ||-<lB> B ≅ C | RB]) :
  [Γ ||-<lA> A ≅ C | RA].
Proof.
  destruct RA as [pA lrA], RB as [pB lrB], RC as [pC lrC]; cbn in *.
  set (sv := combine _ _ _ _ lrA lrB lrC (ShapeViewConv _ _ RAB) (ShapeViewConv _ _ RBC)).
  revert lB B pB lrB lC C pC lrC RAB RBC sv.
  induction lrA as [| |?? ΠA ΠAad ihdom ihcod| | |?? PA PAad ihdom ihcod]; intros ??? lrB;
  induction lrB as [|?? neB|?? ΠB ΠBad _ _| | | ?? PB PBad _ _]; intros ??? lrC;
  induction lrC as [| |?? ΠC ΠCad _ _| | | ?? PC PCad _ _]; intros RAB RBC [].
  - easy.
  - destruct RAB as [tB red], RBC as [tC]; exists tC. 1,2: assumption.
    etransitivity. 1: eassumption. destruct neB as [? red']. cbn in *.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red red').
    1,2 : eapply whnf_whne, ty_ne_whne. all: eassumption.
  - destruct RAB as [?? redB ??], RBC as [?? redC ??].
    destruct ΠB as [??? redB' ??], ΠC as [domC codC ? redC' ??].
    inv_red redB redB'; inv_red redC redC'.
    exists domC codC.
    + eassumption.
    + etransitivity; eassumption.
    + eapply (transPolyRedEq@{i j k l} (PolyRed.from ΠAad) (PolyRed.from ΠBad) (PolyRed.from ΠCad)); cbn; tea.
      * intros * ; eapply ihdom; now eapply (PolyRedPack.shpRed ΠA).
      * intros *; eapply ihcod; eapply (PolyRedPack.posRed ΠA); tea.
  - destruct RBC; now constructor.
  - destruct RBC; now constructor.
  - destruct RAB as [?? redB ??], RBC as [?? redC ??].
    destruct PB as [??? redB' ??], PC as [domC codC ? redC' ??].
    inv_red redB redB'; inv_red redC redC'.
    exists domC codC.
    + eassumption.
    + etransitivity; eassumption.
    + eapply (transPolyRedEq@{i j k l} (PolyRed.from PAad) (PolyRed.from PBad) (PolyRed.from PCad)); cbn; tea.
      * intros * ; eapply ihdom; now eapply (PolyRedPack.shpRed PA).
      * intros *; eapply ihcod; eapply (PolyRedPack.posRed PA); tea.
Qed.


Lemma transEqTermU@{h i j k} {Γ l UU t u v} {h : [Γ ||-U<l> UU]} :
  [LogRelRec@{i j k} l | Γ ||-U t ≅ u : UU| h] ->
  [LogRelRec@{i j k} l | Γ ||-U u ≅ v : UU| h] ->
  [LogRelRec@{i j k} l | Γ ||-U t ≅ v : UU| h].
Proof.
  intros [rL ?? redL] [? rR] ; exists rL rR redL; tea.
  + etransitivity; tea.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ (URedTm.red redR) (URedTm.red redL0))  ; tea.
    all: apply isType_whnf; apply URedTm.type.
  + apply TyEqRecFwd; unshelve eapply transEq@{h i j k}.
    6,7: now apply (TyEqRecFwd h). 
    2: apply (RedTyRecFwd h); tea.
Qed.

Lemma transEqTermNeu {Γ A t u v} {RA : [Γ ||-ne A]} :
  [Γ ||-ne t ≅ u : A | RA] ->
  [Γ ||-ne u ≅ v : A | RA] ->
  [Γ ||-ne t ≅ v : A| RA].
Proof.
  intros [tL] [? tR]; exists tL tR; tea.
  etransitivity; tea.
  unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ redR redL0); tea.
  all: now eapply whnf_whne, tm_ne_whne.
Qed.


Lemma transEqTermΠ {Γ lA A t u v} {ΠA : [Γ ||-Π<lA> A]}
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (t u v : term),
    [PolyRed.shpRed ΠA ρ h | Δ ||- t ≅ u : _] ->
    [PolyRed.shpRed ΠA ρ h | Δ ||- u ≅ v : _] ->
    [PolyRed.shpRed ΠA ρ h | Δ ||- t ≅ v : _])
  (ihcod : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a : _]) (t u v : term),
    [PolyRed.posRed ΠA ρ h ha | Δ ||- t ≅ u : _] ->
    [PolyRed.posRed ΠA ρ h ha | Δ ||- u ≅ v : _] ->
    [PolyRed.posRed ΠA ρ h ha | Δ ||- t ≅ v : _]) :
  [Γ ||-Π t ≅ u : A | ΠA ] ->
  [Γ ||-Π u ≅ v : A | ΠA ] ->
  [Γ ||-Π t ≅ v : A | ΠA ].
Proof.
  intros [tL] [? tR];
  unshelve epose proof (e := redtmwf_det _ _ _ _ _ _ _ _ (PiRedTm.red redR) (PiRedTm.red redL)); tea.
  1,2: apply isFun_whnf; apply PiRedTm.isfun.
  exists tL tR.
  + etransitivity; tea. now rewrite e.
  + intros. eapply ihcod.
    1: eapply eqApp.
    rewrite e; apply eqApp0.
Qed.

Lemma transEqTermΣ {Γ lA A t u v} {ΣA : [Γ ||-Σ<lA> A]}
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (t u v : term),
    [PolyRed.shpRed ΣA ρ h | Δ ||- t ≅ u : _] ->
    [PolyRed.shpRed ΣA ρ h | Δ ||- u ≅ v : _] ->
    [PolyRed.shpRed ΣA ρ h | Δ ||- t ≅ v : _])
  (ihcod : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΣA ρ h | Δ ||- a : _]) (t u v : term),
    [PolyRed.posRed ΣA ρ h ha | Δ ||- t ≅ u : _] ->
    [PolyRed.posRed ΣA ρ h ha | Δ ||- u ≅ v : _] ->
    [PolyRed.posRed ΣA ρ h ha | Δ ||- t ≅ v : _]) :
  [Γ ||-Σ t ≅ u : A | ΣA ] ->
  [Γ ||-Σ u ≅ v : A | ΣA ] ->
  [Γ ||-Σ t ≅ v : A | ΣA ].
Proof.
  intros [tL ?? eqfst eqsnd] [? tR ? eqfst' eqsnd'];
  unshelve epose proof (e := redtmwf_det _ _ _ _ _ _ _ _ (SigRedTm.red redR) (SigRedTm.red redL)); tea.
  1,2: apply isPair_whnf; apply SigRedTm.isfun.
  exists tL tR.
  + etransitivity; tea. now rewrite e.
  + intros; eapply ihdom ; [eapply eqfst| rewrite e; eapply eqfst'].
  + intros; eapply ihcod; [eapply eqsnd|].
    rewrite e. eapply LRTmEqRedConv.
    2: eapply eqsnd'.
    eapply PolyRed.posExt.
    1: eapply (SigRedTm.fstRed tL).
    eapply LRTmEqSym. rewrite <- e.
    eapply eqfst.
    Unshelve. tea.
Qed.


Lemma transNeNfEq {Γ t u v A} :
  [Γ ||-NeNf t ≅ u : A] ->
  [Γ ||-NeNf u ≅ v : A] ->
  [Γ ||-NeNf t ≅ v : A].
Proof.
  intros [] []; econstructor; tea; now etransitivity.
Qed.

Lemma transEqTermNat {Γ A} (NA : [Γ ||-Nat A]) :
  (forall t u, 
    [Γ ||-Nat t ≅ u : A | NA] -> forall v,
    [Γ ||-Nat u ≅ v : A | NA] ->  
    [Γ ||-Nat t ≅ v : A | NA]) ×
  (forall t u,
    NatPropEq NA t u -> forall v,
    NatPropEq NA u v ->
    NatPropEq NA t v).
Proof.
  apply NatRedEqInduction.
  - intros * ???? ih ? uv; inversion uv; subst.
    destruct (NatPropEq_whnf prop), (NatPropEq_whnf prop0). 
    unshelve epose proof (redtmwf_det _ u _ _ _ _ _ _ redR redL0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    now eapply ih.
  - easy.
  - intros * ? ih ? uv.
    inversion uv ; subst.
    + econstructor; now eapply ih.
    + match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; apply tm_ne_whne in neL; inv_whne end.
  - intros ?? tu ? uv; inversion uv; subst.
    1,2: destruct tu; apply tm_ne_whne in neR; inv_whne.
    econstructor; now eapply transNeNfEq.
Qed.

Lemma and_two P Q : Q -> (Q -> P) -> (P × Q).
Proof.
  firstorder.
Qed.

Lemma transEqTermEmpty {Γ A} (NA : [Γ ||-Empty A]) :
  (forall t u, 
    [Γ ||-Empty t ≅ u : A | NA] -> forall v,
    [Γ ||-Empty u ≅ v : A | NA] ->  
    [Γ ||-Empty t ≅ v : A | NA]) ×
  (forall t u,
    EmptyPropEq Γ t u -> forall v,
    EmptyPropEq Γ u v ->
    EmptyPropEq Γ t v).
Proof.
  eapply and_two.
  - intros ?? tu ? uv; inversion uv; subst.
    destruct tu.
    econstructor; now eapply transNeNfEq.
  - intros HH.
    intros t u tu v uv. inversion uv; subst.
    inversion tu; subst.
    unshelve eapply EmptyPropEq_whnf in prop as HH1. 2: tea. destruct HH1.
    unshelve eapply EmptyPropEq_whnf in prop0 as HH2. 2: tea. destruct HH2.
    unshelve epose proof (redtmwf_det _ u _ _ _ _ _ _ redL redR0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    eapply HH; eauto.
Qed.

Lemma transEqTerm@{h i j k l} {Γ lA A t u v} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]} :
  [Γ ||-<lA> t ≅ u : A | RA] ->
  [Γ ||-<lA> u ≅ v : A | RA] ->
  [Γ ||-<lA> t ≅ v : A | RA].
Proof. 
  revert t u v; pattern lA, Γ, A, RA; apply LR_rect_TyUr; clear lA Γ A RA; intros l Γ.
  - intros *; apply transEqTermU@{h i j k}.
  - intros *; apply transEqTermNeu.
  - intros * ?????. apply transEqTermΠ; tea.
  - intros ? NA **; now eapply (fst (transEqTermNat NA)).
  - intros ? NA **; now eapply (fst (transEqTermEmpty NA)).
  - intros * ?????; apply transEqTermΣ; tea.
Qed.

Lemma LREqTermSymConv {Γ t u G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG] -> 
  [Γ ||-<l> G' ≅ G | RG'] ->
  [Γ ||-<l> u ≅ t : G' | RG'].
Proof.
  intros Rtu RGG'.
  eapply LRTmEqSym; eapply LRTmEqRedConv; tea.
  now eapply LRTyEqSym.
Qed.  

Lemma LREqTermHelper {Γ t t' u u' G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG] -> 
  [Γ ||-<l> t' ≅ u' : G' | RG'] -> 
  [Γ ||-<l> G ≅ G' | RG] ->
  [Γ ||-<l> u ≅ u' : G | RG] -> 
  [Γ ||-<l> t ≅ t' : G | RG].
Proof.
  intros Rtu Rtu' RGG' Ruu'.
  do 2  (eapply transEqTerm; tea).
  now eapply LREqTermSymConv.
Qed.  

End Transitivity.
