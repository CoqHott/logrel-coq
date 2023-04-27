Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance.

Set Universe Polymorphism.

Section Transitivity.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.

Lemma transEq@{i j k l} {wl Γ A B C lA lB lC} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]< wl >}
  {RB : [LogRel@{i j k l} lB | Γ ||- B]< wl >}
  {RC : [LogRel@{i j k l} lC | Γ ||- C]< wl >}
  (RAB : [Γ ||-<lA> A ≅ B | RA]< wl >)
   (RBC : [Γ ||-<lB> B ≅ C | RB]< wl >) :
  [Γ ||-<lA> A ≅ C | RA]< wl >.
Proof.
  destruct RA as [pA lrA], RB as [pB lrB], RC as [pC lrC]; cbn in *.
  set (sv := combine _ _ _ _ _ lrA lrB lrC (ShapeViewConv _ _ RAB) (ShapeViewConv _ _ RBC)).
  revert lB B pB lrB lC C pC lrC RAB RBC sv.
  induction lrA as [| |??? ΠA ΠAad ihdom ihcod| | |]; intros ??? lrB;
  induction lrB as [|??? neB|??? ΠB ΠBad _ _| | |]; intros ??? lrC;
  induction lrC as [| |??? ΠC ΠCad _ _| | |]; intros RAB RBC [].
  - easy.
  - destruct RAB as [tB red], RBC as [tC]; exists tC. 1,2: assumption.
    etransitivity. 1: eassumption. destruct neB as [? red']. cbn in *.
    unshelve erewrite (redtywf_det _ _ _ _ _ _ _ red red').
    1,2 : eapply whnf_whne, ty_ne_whne. all: eassumption.
  - destruct RAB as [domB codB redB ? domRedEqN domRedEq codRedEqN codRedEqN_Ltrans codRedEq], RBC as [domC codC redC ? domRedN' domRedEq' codRedN' codRedN_Ltrans' codRedEq'].
    destruct ΠB as [?? redB' ??? domRedBN domRedB codRedBN codRedBN_Ltrans codRedB],
        ΠC as [?? redC' ??? domRedCN domRedC codRedCN codRedCN_Ltrans codRedC],
          ΠBad as [domAdB codAdB], ΠCad as [domAdC codAdC]; cbn in *.
    unshelve epose proof (eqΠB := redtywf_det _ _ _ _ _ _ _ redB' redB) ;
    [ constructor | constructor | .. ].
    injection eqΠB; intros eqcod eqdom; clear eqΠB;  subst. 
    unshelve epose proof (eqΠC := redtywf_det _ _ _ _ _ _ _ redC' redC).
    1,2 : constructor.
    injection eqΠC; intros eqcod eqdom; clear eqΠC;  subst. 
    assert (domRedAC : forall (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ Γ)
                              (τ : wl' ≤ε wl)
                              (Ninfl : AllInLCon (PiRedTy.domN ΠA) wl')
                              (Ninfl' : AllInLCon domRedBN wl')
                              (Ninfl'' : AllInLCon domRedN' wl')
                              (Ninfl''' : AllInLCon domRedCN wl')
                              (Ninfl''' : AllInLCon domRedEqN wl')
                              (h : [ |-[ ta ] Δ]< wl' >),
      [PiRedTy.domRed ΠA ρ τ Ninfl h | Δ ||- (PiRedTy.dom ΠA)⟨ρ⟩ ≅ domC⟨ρ⟩]< wl' >).
    { intros. unshelve eapply ihdom.
      10: now unshelve apply domRedEq'.
      7: apply domRedEq.
      6: now unshelve apply domAdC.
      3: apply domAdB.
      now apply (PiRedTy.domRed ΠA).
      assumption.
    }
    unshelve econstructor.
    + exact domC.
    + exact codC.
    + exact (max (max domRedBN domRedN') (max domRedCN domRedEqN)).
    + intros.
      unshelve eapply (max (max _ _) (max _ _)).
      1:{ unshelve eapply codRedBN ; try assumption.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
          * eapply RedTmConv.
            now eapply (PiRedTy.domAd ΠAad).
            3: eassumption.
            eapply domAdB.
            eapply domRedEq.
            eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_r ; eapply Nat.max_lub_r. }
      { unshelve eapply codRedN' ; try assumption.
        + eapply AllInLCon_le ; try eassumption.
          now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
        + eapply AllInLCon_le ; try eassumption.
          now eapply Nat.max_lub_r ; eapply Nat.max_lub_l.
        + eapply RedTmConv.
          now eapply (PiRedTy.domAd ΠAad).
          3: eassumption.
          eapply domAdB.
          eapply domRedEq.
          eapply AllInLCon_le ; try eassumption.
          now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
      }
      { unshelve eapply codRedEqN ; try assumption ;
          eapply AllInLCon_le ; try eassumption.
        now eapply Nat.max_lub_r ; eapply Nat.max_lub_r. }
      { unshelve eapply codRedCN ; try assumption.
        + eapply AllInLCon_le ; try eassumption.
          now eapply Nat.max_lub_l ; eapply Nat.max_lub_r.
        + eapply RedTmConv.
          now eapply (PiRedTy.domAd ΠAad).
          3: eassumption.
          eapply domAdC.
          eapply domRedAC.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_r ; eapply Nat.max_lub_l.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_l ; eapply Nat.max_lub_r.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
        }
    + eassumption.
    + etransitivity; eassumption.
    + intros ; eapply domRedAC ; eapply AllInLCon_le ; try eassumption.
      * now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
      * now eapply Nat.max_lub_r ; eapply Nat.max_lub_l.
      * now eapply Nat.max_lub_l ; eapply Nat.max_lub_r.
      * now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
    + intros ; cbn in *.
      unshelve eapply Nat.max_le_compat.
      * unshelve eapply Nat.max_le_compat.
        -- now eapply codRedBN_Ltrans.
        -- now eapply codRedN_Ltrans'.
      * unshelve eapply Nat.max_le_compat.
        -- now eapply codRedEqN_Ltrans.
        -- now eapply codRedCN_Ltrans.        
    + intros. unshelve eapply ihcod.
      10:{ unshelve eapply codRedEq' ; [exact l' | ..] ; try assumption.
           3-5 : eapply AllInLCon_le ; try eassumption.
           + eapply AllInLCon_le ; try eassumption.
             now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
           + eapply RedTmConv.
             4: exact ha.
             * apply (PiRedTy.domAd ΠAad).
             * apply domAdB.
             * apply domRedEq.
               eapply AllInLCon_le ; try eassumption.
               now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
           + now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
           + now eapply Nat.max_lub_r ; eapply Nat.max_lub_l.
           + now eapply Nat.max_lub_r ; eapply Nat.max_lub_l.
      }
      7:{ unshelve eapply codRedEq.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
          * eapply AllInLCon_le ; try eassumption.
            now eapply Nat.max_lub_l; eapply Nat.max_lub_r. }
      6:{ unshelve apply codAdC. 1: exact l'.
          assumption.
(*          now eapply wfLCon_le_trans.*)
          cbn in Minfl'.
(*          etransitivity.*)
          eapply AllInLCon_le ; try eassumption.
          now eapply Nat.max_lub_l ; eapply Nat.max_lub_r.
          assumption.
           { eapply RedTmConv.
            4: exact ha.
            + apply (PiRedTy.domAd ΠAad).
            + apply domAdC.
            + apply domRedAC.
              all: eapply AllInLCon_le ; try eassumption.
            * now eapply Nat.max_lub_l ; eapply Nat.max_lub_l.
            * now eapply Nat.max_lub_r ; eapply Nat.max_lub_l.
            * now eapply Nat.max_lub_l ; eapply Nat.max_lub_r.
            * now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
           }
           assumption.
           eapply AllInLCon_le ; try eassumption.
           now eapply Nat.max_lub_r ; eapply Nat.max_lub_r.
      }
      3: apply codAdB.
      now eapply (PiRedTy.codRed ΠA).
  - destruct RBC; now constructor.
  - destruct RBC; now constructor.
  - destruct RBC; now constructor.
Qed.

Lemma WtransEq@{i j k l} {wl Γ A B C lA lB lC} 
  {RA : WLogRel@{i j k l} lA wl Γ A}
  {RB : WLogRel@{i j k l} lB wl Γ B}
  {RC : WLogRel@{i j k l} lC wl Γ C}
  (RAB : W[Γ ||-< lA > A ≅ B | RA]< wl >)
   (RBC : W[Γ ||-< lB > B ≅ C | RB]< wl >) :
  W[Γ ||-<lA> A ≅ C | RA]< wl >.
Proof.
  destruct RAB as [WNAB WRedEqAB].
  destruct RBC as [WNBC WRedEqBC].
  exists (max (max RB.(WN) RC.(WN)) (max WNAB WNBC)).
  intros.
  eapply (transEq (B := B)).
  - unshelve eapply WRedEqAB.
    eapply AllInLCon_le.
    eapply Nat.max_lub_l ; now eapply Nat.max_lub_r.
    eassumption.
  - unshelve eapply WRedEqBC ; try assumption.
    + eapply AllInLCon_le.
      eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
      eassumption.
    + eapply AllInLCon_le.
      eapply Nat.max_lub_r ; now eapply Nat.max_lub_r.
      eassumption.
      Unshelve.
      * exact lC.
      * unshelve eapply RC.(WRed) ; try assumption.
        eapply AllInLCon_le.
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
        eassumption.
Qed.    

  

  
Lemma transEqTermU@{h i j k} {wl Γ l UU t u v} {h : [Γ ||-U<l> UU]< wl >} :
  [LogRelRec@{i j k} l | Γ ||-U t ≅ u : UU| h]< wl > ->
  [LogRelRec@{i j k} l | Γ ||-U u ≅ v : UU| h]< wl > ->
  [LogRelRec@{i j k} l | Γ ||-U t ≅ v : UU| h]< wl >.
Proof.
  intros [rL ?? redL] [? rR] ; exists rL rR redL; tea.
  + etransitivity; tea.
    unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ _ (URedTm.red redR) (URedTm.red redL0))  ; tea.
    all: apply isType_whnf; apply URedTm.type.
  + apply TyEqRecFwd; unshelve eapply transEq@{h i j k}.
    6,7: now apply (TyEqRecFwd h). 
    2: apply (RedTyRecFwd h); tea.
Qed.

Lemma transEqTermNeu {wl Γ A t u v} {RA : [Γ ||-ne A]< wl >} :
  [Γ ||-ne t ≅ u : A | RA]< wl > ->
  [Γ ||-ne u ≅ v : A | RA]< wl > ->
  [Γ ||-ne t ≅ v : A| RA]< wl >.
Proof.
  intros [tL] [? tR]; exists tL tR; tea.
  etransitivity; tea.
  unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ _ redR redL0); tea.
  all: now eapply whnf_whne, tm_ne_whne.
Qed.

Lemma transEqTermΠ {wl Γ lA A t u v} {ΠA : [Γ ||-Π<lA> A]< wl >}
  (ihdom : forall (Δ : context) wl' (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                  (Ninfl : AllInLCon (PiRedTyPack.domN ΠA) wl')
                  (h : [ |-[ ta ] Δ]< wl' >) (t u v : term),
  [PiRedTyPack.domRed ΠA ρ τ Ninfl h | Δ ||- t ≅ u : (PiRedTyPack.dom ΠA)⟨ρ⟩]< wl' > ->
  [PiRedTyPack.domRed ΠA ρ τ Ninfl h  | Δ ||- u ≅ v : (PiRedTyPack.dom ΠA)⟨ρ⟩]< wl' > ->
  [PiRedTyPack.domRed ΠA ρ τ Ninfl h  | Δ ||- t ≅ v : (PiRedTyPack.dom ΠA)⟨ρ⟩]< wl' >)
  (ihcod : forall (Δ : context) wl' (a : term) (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                  (Ninfl : AllInLCon (PiRedTyPack.domN ΠA) wl')
                  (h : [ |-[ ta ] Δ]< wl' >)
                  (ha : [PiRedTyPack.domRed ΠA ρ τ Ninfl h | Δ ||- a : (PiRedTyPack.dom ΠA)⟨ρ⟩]< wl' >)
                  {wl''} (τ' : wl'' ≤ε wl')
                  (Minfl : AllInLCon _ wl'')
                  (t u v : term),
  [PiRedTyPack.codRed ΠA ρ τ Ninfl h ha τ' Minfl | Δ ||- t ≅ u : (PiRedTyPack.cod ΠA) [a .: ρ >> tRel]]< wl'' > ->
  [PiRedTyPack.codRed ΠA ρ τ Ninfl h ha τ' Minfl | Δ ||- u ≅ v : (PiRedTyPack.cod ΠA) [a .: ρ >> tRel]]< wl'' > ->
  [PiRedTyPack.codRed ΠA ρ τ Ninfl h ha τ' Minfl | Δ ||- t ≅ v : (PiRedTyPack.cod ΠA) [a .: ρ >> tRel]]< wl'' >) :
  [Γ ||-Π t ≅ u : A | PiRedTyPack.toPiRedTy (Γ := Γ) ΠA ]< wl > ->
  [Γ ||-Π u ≅ v : A | PiRedTyPack.toPiRedTy ΠA ]< wl > ->
  [Γ ||-Π t ≅ v : A | PiRedTyPack.toPiRedTy ΠA ]< wl >.
Proof.
  intros [tL] [? tR];
  unshelve epose proof (e := redtmwf_det _ _ _ _ _ _ _ _ _ (PiRedTm.red redR) (PiRedTm.red redL)); tea.
  1,2: apply isFun_whnf; apply PiRedTm.isfun.
  unshelve econstructor.
  - exact tL.
  - exact tR.
  - exact (max eqN eqN0).
  - intros.
    unshelve refine (max _ _).
    + unshelve eapply eqappN ; try assumption.
      eapply AllInLCon_le ; try eassumption.
      now eapply Nat.max_lub_l.
    + unshelve eapply eqappN0 ; try assumption.
      eapply AllInLCon_le ; try eassumption.
      now eapply Nat.max_lub_r.
  - etransitivity; tea.
    now rewrite e.
  - intros.
    unshelve eapply Nat.max_le_compat.
    + now eapply eqappN_Ltrans.
    + now eapply eqappN_Ltrans0.
  - intros. eapply ihcod.
    1: eapply eqApp.
    + eapply AllInLCon_le ; try eassumption.
      now eapply Nat.max_lub_l.
    + rewrite e.
      unshelve eapply eqApp0.
      * eapply AllInLCon_le ; try eassumption.
        now eapply Nat.max_lub_r.
      * eapply AllInLCon_le ; try eassumption.
        now eapply Nat.max_lub_r.
Qed.

Lemma transNeNfEq {wl Γ t u v A} :
  [Γ ||-NeNf t ≅ u : A]< wl > ->
  [Γ ||-NeNf u ≅ v : A]< wl > ->
  [Γ ||-NeNf t ≅ v : A]< wl >.
Proof.
  intros [] []; econstructor; tea; now etransitivity.
Qed.

Lemma transEqTermNat {wl Γ A} (NA : [Γ ||-Nat A]< wl >) :
  (forall t u, 
    [Γ ||-Nat t ≅ u : A | NA]< wl > -> forall v,
    [Γ ||-Nat u ≅ v : A | NA]< wl > ->  
    [Γ ||-Nat t ≅ v : A | NA]< wl >) ×
  (forall t u,
    NatPropEq NA t u -> forall v,
    NatPropEq NA u v ->
    NatPropEq NA t v).
Proof.
  apply NatRedEqInduction.
  - intros * ???? ih ? uv; inversion uv; subst.
    destruct (NatPropEq_whnf prop), (NatPropEq_whnf prop0). 
    unshelve epose proof (redtmwf_det _ _ u _ _ _ _ _ _ redR redL0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    now eapply ih.
  - easy.
  - intros * ? ih ? uv.
    inversion uv ; subst.
    + econstructor; now eapply ih.
    + match goal with H : [_ ||-NeNf _ ≅ _ : _ ]< _ > |- _ => destruct H; apply tm_ne_whne in neL; inv_whne end.
  - intros ?? tu ? uv; inversion uv; subst.
    1,2: destruct tu; apply tm_ne_whne in neR; inv_whne.
    econstructor; now eapply transNeNfEq.
Qed.

Lemma and_two P Q : Q -> (Q -> P) -> (P × Q).
Proof.
  firstorder.
Qed.

Lemma transEqTermBool {wl Γ A} (NA : [Γ ||-Bool A]< wl >) :
  (forall t u, 
    [Γ ||-Bool t ≅ u : A | NA]< wl > -> forall v,
    [Γ ||-Bool u ≅ v : A | NA]< wl > ->  
    [Γ ||-Bool t ≅ v : A | NA]< wl >) ×
  (forall t u,
    BoolPropEq NA t u -> forall v,
    BoolPropEq NA u v ->
    BoolPropEq NA t v).
Proof.
  eapply and_two.
  - intros ?? tu ? uv ; inversion uv ; subst ; try assumption.
    destruct tu ; try now econstructor.
    econstructor.
    now eapply transNeNfEq.
  - intros HH t u tu v uv.
    inversion uv ; subst.
    inversion tu ; subst.
    unshelve eapply BoolPropEq_whnf in prop as HH1. destruct HH1.
    unshelve eapply BoolPropEq_whnf in prop0 as HH2. destruct HH2.
    unshelve epose proof (redtmwf_det _ _ u _ _ _ _ _ _ redL redR0); tea; subst.
    econstructor ; tea.
    now etransitivity.
    now eapply HH.
Qed.

Lemma transEqTermEmpty {wl Γ A} (NA : [Γ ||-Empty A]< wl >) :
  (forall t u, 
    [Γ ||-Empty t ≅ u : A | NA]< wl > -> forall v,
    [Γ ||-Empty u ≅ v : A | NA]< wl > ->  
    [Γ ||-Empty t ≅ v : A | NA]< wl >) ×
  (forall t u,
    EmptyPropEq (l := wl) Γ t u -> forall v,
    EmptyPropEq (l := wl) Γ u v ->
    EmptyPropEq (l := wl) Γ t v).
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
    unshelve epose proof (redtmwf_det _ _ u _ _ _ _ _ _ redL redR0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    eapply HH; eauto.
Qed.

Lemma transEqTerm@{h i j k l} {wl Γ lA A t u v} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]< wl >} :
  [Γ ||-<lA> t ≅ u : A | RA]< wl > ->
  [Γ ||-<lA> u ≅ v : A | RA]< wl > ->
  [Γ ||-<lA> t ≅ v : A | RA]< wl >.
Proof. 
  revert t u v; pattern lA, wl, Γ, A, RA; apply LR_rect_TyUr; clear lA wl Γ A RA; intros l Γ.
  - intros *; apply transEqTermU@{h i j k}.
  - intros *; apply transEqTermNeu.
  - intros * ?????. apply transEqTermΠ; tea.
  - intros ?? NA ** ; now eapply (fst (transEqTermNat NA)).
  - intros ?? NA **; now eapply (fst (transEqTermBool NA)).
  - intros ?? NA **; now eapply (fst (transEqTermEmpty NA)).
Qed.

Lemma LREqTermSymConv {wl Γ t u G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG]< wl > -> 
  [Γ ||-<l> G' ≅ G | RG']< wl > ->
  [Γ ||-<l> u ≅ t : G' | RG']< wl >.
Proof.
  intros Rtu RGG'.
  eapply LRTmEqSym; eapply LRTmEqRedConv; tea.
  now eapply LRTyEqSym.
Qed.  

Lemma LREqTermHelper {wl Γ t t' u u' G G' l RG RG'} :
  [Γ ||-<l> t ≅ u : G | RG]< wl > -> 
  [Γ ||-<l> t' ≅ u' : G' | RG']< wl > -> 
  [Γ ||-<l> G ≅ G' | RG]< wl > ->
  [Γ ||-<l> u ≅ u' : G | RG]< wl > -> 
  [Γ ||-<l> t ≅ t' : G | RG]< wl >.
Proof.
  intros Rtu Rtu' RGG' Ruu'.
  do 2  (eapply transEqTerm; tea).
  now eapply LREqTermSymConv.
Qed.  

End Transitivity.
