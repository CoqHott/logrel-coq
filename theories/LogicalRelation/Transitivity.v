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
  induction lrA as [| |?? ΠA ΠAad ihdom ihcod]; intros ??? lrB;
  induction lrB as [|?? neB|?? ΠB ΠBad _ _]; intros ??? lrC;
  induction lrC as [| |?? ΠC ΠCad _ _]; intros RAB RBC [].
  - easy.
  - destruct RAB as [tB red], RBC as [tC]; exists tC. 1,2: assumption.
    etransitivity. 1: eassumption. destruct neB as [? red']. cbn in *.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ red red').
    1,2 : apply whnf_whne. all: assumption.
  - destruct RAB as [nB domB codB redB ? domRedEq codRedEq], RBC as [nC domC codC redC ? domRedEq' codRedEq'].
    destruct ΠB as [??? redB' ??? domRedB codRedB], ΠC as [??? redC' ??? domRedC codRedC], ΠBad as [domAdB codAdB], ΠCad as [domAdC codAdC]; cbn in *.
    unshelve epose proof (eqΠB := redtywf_det _ _ _ _ _ _ redB' redB).  1,2 : constructor.
    injection eqΠB; intros eqcod eqdom eqna; clear eqΠB;  subst. 
    unshelve epose proof (eqΠC := redtywf_det _ _ _ _ _ _ redC' redC).  1,2 : constructor.
    injection eqΠC; intros eqcod eqdom eqna; clear eqΠC;  subst. 
    assert (domRedAC : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
      [PiRedTy.domRed ΠA ρ h | Δ ||- (PiRedTy.dom ΠA)⟨ρ⟩ ≅ domC⟨ρ⟩]).
    { intros. unshelve eapply ihdom.
      10: now unshelve apply domRedEq'.
      7: apply domRedEq.
      6: now unshelve apply domAdC.
      3: apply domAdB.
      now apply (PiRedTy.domRed ΠA).
    }
    exists nC domC codC.
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
  all: now apply whnf_whne.
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