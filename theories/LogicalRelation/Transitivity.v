From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance.

Set Universe Polymorphism.

Section Transitivity.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Set Printing Universes.

 Lemma transEq@{i j k l} {Γ A B C lA lB} 
  {RA : [LogRel@{i j k l} lA | Γ ||- A]}
  {RB : [LogRel@{i j k l} lB | Γ ||- B]}
  (RAB : [Γ ||-<lA> A ≅ B | RA])
   (RBC : [Γ ||-<lB> B ≅ C | RB]) :
  [Γ ||-<lA> A ≅ C | RA].
Proof. now eapply LRTransEq. Qed.

Lemma transEqTermU@{h i j k} {Γ l UU t u v} {h : [Γ ||-U<l> UU]} :
  [LogRelRec@{i j k} l | Γ ||-U t ≅ u : UU| h] ->
  [LogRelRec@{i j k} l | Γ ||-U u ≅ v : UU| h] ->
  [LogRelRec@{i j k} l | Γ ||-U t ≅ v : UU| h].
Proof.
  intros [rL ?? redL] [? rR] ; exists rL rR redL; tea.
  + etransitivity; tea.
    unshelve erewrite (redtmwf_det _ _ (URedTm.red redR) (URedTm.red redL0))  ; tea.
    all: apply isType_whnf; apply URedTm.type.
  + apply TyEqRecFwd; unshelve eapply transEq@{h i j k}.
    4,5: now apply (TyEqRecFwd h). 
Qed.

Lemma transEqTermNeu {Γ A t u v} {RA : [Γ ||-ne A]} :
  [Γ ||-ne t ≅ u : A | RA] ->
  [Γ ||-ne u ≅ v : A | RA] ->
  [Γ ||-ne t ≅ v : A| RA].
Proof.
  intros [tL] [? tR]; exists tL tR; tea.
  etransitivity; tea.
  unshelve erewrite (redtmwf_det _ _ redR redL0); tea.
  all: eapply whnf_whne, convneu_whne; first [eassumption|symmetry; eassumption].
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
  intros [tL] [? tR].
  assert (forall t (red : [Γ ||-Π t : _ | ΠA]), whnf (PiRedTm.nf red)).
  { intros ? [? ? isfun]; simpl; destruct isfun; constructor; tea.
    now eapply convneu_whne. }
  unshelve epose proof (e := redtmwf_det _ _ (PiRedTm.red redR) (PiRedTm.red redL)); tea.
  1,2: now eauto.
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
  intros [tL ?? eqfst eqsnd] [? tR ? eqfst' eqsnd'].
  assert (forall t (red : [Γ ||-Σ t : _ | ΣA]), whnf (SigRedTm.nf red)).
  { intros ? [? ? ispair]; simpl; destruct ispair; constructor; tea.
    now eapply convneu_whne. }
  unshelve epose proof (e := redtmwf_det _ _ (SigRedTm.red redR) (SigRedTm.red redL)); tea.
  1,2: now eauto.
  exists tL tR.
  + etransitivity; tea. now rewrite e.
  + intros; eapply ihdom ; [eapply eqfst| rewrite e; eapply eqfst'].
  + intros; eapply ihcod; [eapply eqsnd|].
    rewrite e. 
    eapply LRTmEqRedConv.
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
    unshelve epose proof (redtmwf_det _ _ redR redL0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    now eapply ih.
  - easy.
  - intros * ? ih ? uv.
    inversion uv ; subst.
    + econstructor; now eapply ih.
    + match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; apply convneu_whne in conv; inv_whne end.
  - intros ?? tu ? uv; inversion uv; subst.
    1,2: destruct tu; symmetry in conv; apply convneu_whne in conv; inv_whne.
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
    unshelve epose proof (redtmwf_det _ _ redL redR0); tea; subst.
    econstructor; tea.
    1: now etransitivity.
    eapply HH; eauto.
Qed.

Lemma transIdPropEq {Γ l A} (IA : [Γ ||-Id<l> A]) t u v :
  IdPropEq IA t u -> IdPropEq IA u v -> IdPropEq IA t v.
Proof.
  intros [] h; inversion h; subst.
  - now econstructor.
  - match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; apply convneu_whne in conv; inv_whne end.
  - match goal with H : [_ ||-NeNf _ ≅ _ : _ ] |- _ => destruct H; symmetry in conv; apply convneu_whne in conv; inv_whne end.
  - econstructor; now eapply transNeNfEq.
Qed.

Lemma IdPropEq_whnf {Γ l A} (IA : [Γ ||-Id<l> A]) t u : IdPropEq IA t u -> whnf t × whnf u.
Proof.
  intros []; split; constructor; destruct r; eapply convneu_whne; tea; now symmetry.
Qed.

Lemma transTmEqId {Γ l A} (IA : [Γ ||-Id<l> A]) t u v :
  [Γ ||-Id<l> t ≅ u : _ | IA] -> [Γ ||-Id<l> u ≅ v : _| IA] -> [Γ ||-Id<l> t ≅ v : _| IA].
Proof.
  intros [??? red ? prop] [?? red' ?? prop'].
  pose proof prop as [_ wh]%IdPropEq_whnf.
  pose proof prop' as [wh' _]%IdPropEq_whnf.
  pose proof (redtmwf_det wh wh' red red'); subst.
  unshelve econstructor; cycle 2; tea.
  1: now etransitivity.
  now eapply transIdPropEq.
Qed.


Lemma transTmEqW {Γ l A} (WA : [Γ ||-W<l> A]) 
        (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (t u v : term),
          [PolyRed.shpRed WA ρ h | Δ ||- t ≅ u : (ParamRedTy.dom WA)⟨ρ⟩] ->
          [PolyRed.shpRed WA ρ h | Δ ||- u ≅ v : (ParamRedTy.dom WA)⟨ρ⟩] ->
          [PolyRed.shpRed WA ρ h | Δ ||- t ≅ v : (ParamRedTy.dom WA)⟨ρ⟩]) :
  WRedInductionConcl WA
      (fun Δ ρ wfΔ t _ => True) 
      (fun Δ ρ wfΔ t _ => True)
      (fun Δ ρ wfΔ t u _ => forall v, WRedTmEq WA ρ wfΔ u v -> WRedTmEq WA ρ wfΔ t v)
      (fun Δ ρ wfΔ t u _ => forall v, WPropEq WA ρ wfΔ u v -> WPropEq WA ρ wfΔ t v).
Proof.
  apply WRedInduction; try solve [intros; exact I].
  - intros * ? red ? []%WRedTmEq.to_whnf ih ? Ruv; inversion Ruv; subst.
    unshelve epose proof (redtmwf_det _ _ red _).
    3,5: tea.
    1: eapply fst;  now eapply WRedTmEq.to_whnf.
    econstructor; tea.
    + subst; now etransitivity.
    + eapply ih; now subst.
  - intros * ?????????? Ra Ra' Raa' Rkk' Rk Rk' ih1 ih2 ih3 ih4 ih5 ih6 ih7 ? Puv.
    inversion Puv; subst.
    2:{ 
      unshelve epose proof (h := NeNf.conv _); cycle 4; tea. 
      eapply convneu_whne in h; inv_whne.
    }
    econstructor; tea.
    + intros. eapply RB'aeq0.
      eapply ihdom; tea.
      eapply LRTmEqSym; eauto.
      Unshelve. eauto.
    + intros. eapply RBa'eq.
      eapply ihdom; tea; eauto.
    + intros; eapply ihdom; eauto.
    + destruct Rkk' as [? redR], Rkk'0 as [redL0].
      assert (e: PiRedTm.nf redR = PiRedTm.nf redL0).
      1:{
        eapply redtmwf_det.
        1,2: eapply isLRFun_whnf, PiRedTm.isfun.
        1,2: now eapply PiRedTm.red.
      }
     unshelve econstructor; tea.
      * eapply funRedTm_conv_irrelevance; tea.
        intros. eapply LRTmEqSym; eauto.
      * cbn; etransitivity; tea.
        rewrite e; eapply convtm_conv; tea.
        symmetry; now eapply supContTy_inst_conv.
      * cbn in *; intros.
        eapply ih7; tea.
        rewrite e; eapply eqApp0.
        eapply instWCodRed_conv_irrelevance.
        2: tea.
        intros; eapply LRTmEqSym; eauto.
  - intros ??? k k' nekk' v hk'v.
    assert (whne k') by (eapply convneu_whne; symmetry; now destruct nekk').
    inversion hk'v; subst; [inv_whne|].
    constructor; now eapply transNeNfEq.
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
  - intros; now eapply transTmEqId.
  - intros; now eapply transTmEqW.
Qed.


#[global]
Instance perLRTmEq@{i j k l} {Γ l A} (RA : [LogRel@{i j k l} l | Γ ||- A]):
  PER (fun t u => [RA | _ ||- t ≅ u : _]).
Proof.
  econstructor.
  - intros ???; now eapply LRTmEqSym.
  - intros ???; now eapply transEqTerm.
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
