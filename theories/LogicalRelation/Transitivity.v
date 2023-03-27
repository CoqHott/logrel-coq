From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance.

Set Universe Polymorphism.

Section Transitivity.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.

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
  induction lrA as [| |?? ΠA ΠAad ihdom ihcod| |]; intros ??? lrB;
  induction lrB as [|?? neB|?? ΠB ΠBad _ _| |]; intros ??? lrC;
  induction lrC as [| |?? ΠC ΠCad _ _| |]; intros RAB RBC [].
  - easy.
  - destruct RAB as [tB red], RBC as [tC]; exists tC. 1,2: assumption.
    etransitivity. 1: eassumption. destruct neB as [? red']. cbn in *.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red red').
    1,2 : eapply whnf_whne, ty_ne_whne. all: eassumption.
  - destruct RAB as [domB codB redB ? domRedEq codRedEq], RBC as [domC codC redC ? domRedEq' codRedEq'].
    destruct ΠB as [?? redB' ??? domRedB codRedB], ΠC as [?? redC' ??? domRedC codRedC], ΠBad as [domAdB codAdB], ΠCad as [domAdC codAdC]; cbn in *.
    unshelve epose proof (eqΠB := redtywf_det _ _ _ _ _ _ redB' redB).  1,2 : constructor.
    injection eqΠB; intros eqcod eqdom; clear eqΠB;  subst. 
    unshelve epose proof (eqΠC := redtywf_det _ _ _ _ _ _ redC' redC).  1,2 : constructor.
    injection eqΠC; intros eqcod eqdom; clear eqΠC;  subst. 
    assert (domRedAC : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
      [PiRedTy.domRed ΠA ρ h | Δ ||- (PiRedTy.dom ΠA)⟨ρ⟩ ≅ domC⟨ρ⟩]).
    { intros. unshelve eapply ihdom.
      10: now unshelve apply domRedEq'.
      7: apply domRedEq.
      6: now unshelve apply domAdC.
      3: apply domAdB.
      now apply (PiRedTy.domRed ΠA).
    }
    exists domC codC.
    + eassumption.
    + etransitivity; eassumption.
    + apply domRedAC.
    + intros. unshelve eapply ihcod.
      10:{ 
        unshelve apply codRedEq'. 1: assumption. 
        eapply RedTmConv.
        4: exact ha.
        * apply (PiRedTy.domAd ΠAad).
        * apply domAdB.
        * apply domRedEq.
      }
      7: unshelve apply codRedEq.
      6:{ unshelve apply codAdC. 1: assumption.
        eapply RedTmConv.
        4: exact ha.
        * apply (PiRedTy.domAd ΠAad).
        * apply domAdC.
        * apply domRedAC.
      }
      3: apply codAdB.
      now eapply (PiRedTy.codRed ΠA).
  - destruct RBC; now constructor.
  - destruct RBC; now constructor.
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
  [PiRedTyPack.domRed ΠA ρ h | Δ ||- t ≅ u : (PiRedTyPack.dom ΠA)⟨ρ⟩] ->
  [PiRedTyPack.domRed ΠA ρ h | Δ ||- u ≅ v : (PiRedTyPack.dom ΠA)⟨ρ⟩] ->
  [PiRedTyPack.domRed ΠA ρ h | Δ ||- t ≅ v : (PiRedTyPack.dom ΠA)⟨ρ⟩])
  (ihcod : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
   (ha : [PiRedTyPack.domRed ΠA ρ h | Δ ||- a : (PiRedTyPack.dom ΠA)⟨ρ⟩])
   (t u v : term),
  [PiRedTyPack.codRed ΠA ρ h ha | Δ ||- t ≅ u : (PiRedTyPack.cod ΠA) [a .: ρ >> tRel]] ->
  [PiRedTyPack.codRed ΠA ρ h ha | Δ ||- u ≅ v : (PiRedTyPack.cod ΠA) [a .: ρ >> tRel]] ->
  [PiRedTyPack.codRed ΠA ρ h ha | Δ ||- t ≅ v : (PiRedTyPack.cod ΠA) [a .: ρ >> tRel]]) :
  [Γ ||-Π t ≅ u : A | PiRedTyPack.toPiRedTy ΠA ] ->
  [Γ ||-Π u ≅ v : A | PiRedTyPack.toPiRedTy ΠA ] ->
  [Γ ||-Π t ≅ v : A | PiRedTyPack.toPiRedTy ΠA ].
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
