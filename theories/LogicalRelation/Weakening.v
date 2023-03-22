From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms UntypedValues Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance.

Set Universe Polymorphism.

Section Weakenings.
  Context `{GenericTypingProperties}.

  Lemma wkU {Γ Δ l A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (h : [Γ ||-U<l> A]) : [Δ ||-U<l> A⟨ρ⟩].
  Proof. destruct h; econstructor; tea; change U with U⟨ρ⟩; gen_typing. Defined.

  Lemma wkΠ  {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A])
    (ihdom : forall Δ' (ρ' : Δ' ≤ Δ), [ |- Δ'] -> [Δ' ||-< l > (PiRedTyPack.dom ΠA)⟨ρ⟩⟨ρ'⟩])
    (ihcod : forall (a : term), [PiRedTyPack.domRed ΠA ρ wfΔ | _ ||- a : _] ->
      forall Δ' (ρ' : Δ' ≤ Δ), [ |- Δ'] ->
      [Δ' ||-< l > (PiRedTyPack.cod ΠA)[a .: ρ >> tRel]⟨ρ'⟩]) :
    [Δ ||-Π< l > A⟨ρ⟩].
  Proof.
    destruct ΠA as[na dom cod];  cbn in *.
    assert (domRed' : forall Δ' (ρ' : Δ' ≤ Δ), [|- Δ'] -> [Δ' ||-< l > dom⟨ρ⟩⟨ρ'⟩ ]).
    {
      intros ? ρ' ?; replace (_⟨_⟩) with (dom⟨ρ' ∘w ρ⟩) by now bsimpl.
      econstructor; now unshelve eapply domRed.
    }
    set (cod' := cod⟨wk_up na dom ρ⟩).
    assert (codRed' : forall Δ' a (ρ' : Δ' ≤ Δ) (h : [|- Δ']),
      [domRed' Δ' ρ' h | _ ||- a : _] -> [Δ' ||-< l > cod'[a .: ρ' >> tRel]]).
    {
      intros ? a ρ' ?.
      replace (cod'[a .: ρ' >> tRel]) with (cod[ a .: (ρ' ∘w ρ) >> tRel]) by (unfold cod'; now bsimpl).
      econstructor; unshelve eapply codRed; [assumption|].
      irrelevance.
    }
    exists na (dom ⟨ρ⟩) cod' domRed' codRed'.
    + unfold cod'; change (tProd ?na _ _) with ((tProd na dom cod)⟨ρ⟩);  gen_typing.
    + gen_typing.
    + unfold cod'; set (ρ1 := wk_up na (dom) ρ); eapply wft_wk; gen_typing.
    + unfold cod'; change (tProd ?na _ _) with ((tProd na dom cod)⟨ρ⟩);  gen_typing.
    + intros Δ' a b ρ' wfΔ' ???. 
      replace (cod'[b .: ρ' >> tRel]) with (cod[ b .: (ρ' ∘w ρ) >> tRel]) by (unfold cod'; now bsimpl).
      subst cod'; unshelve epose (codExt Δ' a b (ρ' ∘w ρ) wfΔ' _ _ _); irrelevance.
  Defined.

  Lemma wkNat {Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Nat A] -> [Δ ||-Nat A⟨ρ⟩].
  Proof. 
    intros []; constructor.
    change tNat with tNat⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wk@{i j k l} {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    [LogRel@{i j k l} l | Γ ||- A] -> [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩].
  Proof.
    intros lrA. revert Δ ρ wfΔ . pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr@{i j k l l}; clear l Γ A lrA.
    - intros **. apply LRU_. now eapply wkU.
    - intros ???[ty]???. apply LRne_.
      exists (ty⟨ρ⟩); [|now apply ty_ne_wk|change U with U⟨ρ⟩] ;gen_typing.
    - intros ??? ? ihdom ihcod ???. apply LRPi'; eapply (wkΠ ρ wfΔ ΠA).
      + intros; now apply ihdom.
      + intros; now eapply ihcod.
    - intros; eapply LRNat_; now eapply wkNat.
  Defined.

  Definition wkΠ' {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) :=
    let ihdom Δ' (ρ' : Δ' ≤ Δ) (h : [ |- Δ']) := wk ρ' h (PiRedTyPack.domRed ΠA ρ wfΔ) in
    let ihcod a (ha : [PiRedTyPack.domRed ΠA ρ wfΔ | _ ||- a : _]) Δ' (ρ' : Δ' ≤ Δ) (h : [ |- Δ']) :=
      wk ρ' h (PiRedTyPack.codRed ΠA ρ wfΔ ha) 
    in
    wkΠ ρ wfΔ ΠA ihdom ihcod.

  Lemma wkΠ_eq {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) :
    wk ρ wfΔ (LRPi' ΠA) = LRPi' (wkΠ' ρ wfΔ ΠA).
  Proof. reflexivity. Qed.

  Set Printing Primitive Projection Parameters.

  Lemma wkEq@{i j k l} {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (lrA : [Γ ||-<l> A]) : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA] ->
    [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩ | wk ρ wfΔ lrA].
  Proof.
    revert B Δ ρ wfΔ. pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros ?? ????? ? [] ; constructor; change U with U⟨ρ⟩; gen_typing.
    - intros * [ty].
      exists ty⟨ρ⟩.
      2: now apply ty_ne_wk, ne.
      1: gen_typing.
      cbn ; change U with U⟨ρ⟩; eapply convneu_wk; assumption.
    - intros * ihdom ihcod * [na dom cod]. rewrite wkΠ_eq. set (X := wkΠ' _ _ _).
      exists na (dom⟨ρ⟩) (cod⟨wk_up na dom ρ⟩). cbn in *.
      + change (tProd ?na _ _) with ((tProd na dom cod)⟨ρ⟩);  gen_typing.
      + change (tProd na _ _) with ((tProd na dom cod)⟨ρ⟩).
        replace (tProd _ _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩) by now bsimpl.
        eapply convty_wk; assumption.
      + intros; irrelevanceRefl.
        unshelve eapply ihdom; try eassumption; eapply domRed.
      + intros ? a ρ' ??.
        replace (_[_ .: ρ' >> tRel]) with (cod[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
        irrelevance0.
        2: unshelve eapply codRed; [eassumption|]; subst X; irrelevance.
        subst X; bsimpl; try rewrite scons_comp'; reflexivity.
    - intros * []; constructor.
      change tNat with tNat⟨ρ⟩; gen_typing.
  Qed.
    

  (* TODO: use program or equivalent to have only the first field non-opaque *)
  Lemma wkΠTerm {Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) 
    (ΠA' := wkΠ' ρ wfΔ ΠA) : 
    [Γ||-Π u : A | PiRedTyPack.toPiRedTy ΠA] -> 
    [Δ ||-Π u⟨ρ⟩ : A⟨ρ⟩ | PiRedTyPack.toPiRedTy ΠA' ].
  Proof.
    intros [t].
    exists (t⟨ρ⟩); try change (tProd ?na _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩).
    + destruct red; unshelve econstructor.
      eapply ty_wk; eassumption.
      eapply ty_wk; eassumption.
      eapply redtm_wk; eassumption.
    + apply isFun_ren; assumption.
    + now apply tm_nf_wk.
    + eapply convtm_wk; eassumption.
    + intros ? a ρ' ??.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve apply app; [eassumption|]; subst ΠA'; irrelevance. 
      subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
    + intros ??? ρ' ????.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve apply eq; [eassumption|..]; subst ΠA'; irrelevance.
      subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
  Defined.

  Lemma wkNeNf {Γ Δ k A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) : 
    [Γ ||-NeNf k : A] -> [Δ ||-NeNf k⟨ρ⟩ : A⟨ρ⟩].
  Proof.
    intros []; constructor; gen_typing.
  Qed.  

  Lemma wkTerm {Γ Δ t A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (lrA : [Γ ||-<l> A]) : 
    [Γ ||-<l> t : A | lrA] -> [Δ ||-<l> t⟨ρ⟩ : A⟨ρ⟩ | wk ρ wfΔ lrA].
  Proof.
    revert t Δ ρ wfΔ. pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros ?????? ρ ? [te]; exists te⟨ρ⟩;  try change U with U⟨ρ⟩.
      1, 4: gen_typing.
      apply isType_ren; assumption.
      now apply tm_nf_wk.
      apply RedTyRecBwd ; apply wk; [assumption|]; now apply (RedTyRecFwd h).
    - intros ?????? ρ ? [te]. exists te⟨ρ⟩; cbn.
      + destruct red; unshelve econstructor.
        eapply ty_wk; eassumption.
        eapply ty_wk; eassumption.
        eapply redtm_wk; eassumption.
      + apply tm_ne_wk; assumption.
      + eapply convneu_wk; eassumption.
    - intros ???? ihdom ihcod ?? ρ ?; apply wkΠTerm. 
    - intros??? NA t ? ρ wfΔ; revert t; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, NatProp NA t -> NatProp NA' t⟨ρ⟩)) by apply h.
      subst G; apply NatRedInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNf.
  Qed.

  Lemma wkUTerm {Γ Δ l A t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (h : [Γ ||-U<l> A]) :
    [LogRelRec l| Γ ||-U t : A | h ] -> [LogRelRec l | Δ||-U t⟨ρ⟩ : A⟨ρ⟩ | wkU ρ wfΔ h].
  Proof.
    intros [te]. exists te⟨ρ⟩; change U with U⟨ρ⟩.
    1, 4: gen_typing.
    apply isType_ren; assumption.
    now apply tm_nf_wk.
    destruct l; [destruct (elim (URedTy.lt h))|cbn].
    eapply (wk (l:=zero)); eassumption.
  Defined.

  Lemma wkNeNfEq {Γ Δ k k' A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) : 
    [Γ ||-NeNf k ≅ k' : A] -> [Δ ||-NeNf k⟨ρ⟩ ≅ k'⟨ρ⟩ : A⟨ρ⟩].
  Proof.
    intros []; constructor; gen_typing.
  Qed.  

  Lemma wkTermEq {Γ Δ t u A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (lrA : [Γ ||-<l> A]) : 
    [Γ ||-<l> t ≅ u : A | lrA] -> [Δ ||-<l> t⟨ρ⟩ ≅ u⟨ρ⟩: A⟨ρ⟩ | wk ρ wfΔ lrA].
  Proof.
    revert t u Δ ρ wfΔ. pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros ??????? ρ ? [rL rR].
      unshelve econstructor.
      + exact (wkUTerm ρ wfΔ h rL).
      + exact (wkUTerm ρ wfΔ h rR).
      + apply RedTyRecBwd; apply wk; [assumption|]; now apply (RedTyRecFwd h).
      + cbn. change U with U⟨ρ⟩. 
        now eapply convtm_wk.
      + apply RedTyRecBwd; apply wk; [assumption|]; now apply (RedTyRecFwd h).
      + apply TyEqRecBwd. eapply wkEq. now apply TyEqRecFwd.
    - intros ??????? ρ ? [tL tR].
      exists (tL⟨ρ⟩) (tR⟨ρ⟩); cbn.
      + destruct redL; unshelve econstructor.
        1,2: eapply ty_wk; eassumption.
        eapply redtm_wk; eassumption.
      + destruct redR; unshelve econstructor.
        1,2: eapply ty_wk; eassumption.
        eapply redtm_wk; eassumption.
      + apply tm_ne_wk; assumption.
      + apply tm_ne_wk; assumption.
      + now eapply convneu_wk.
    - intros ??? ΠA ihdom ihcod t u ? ρ ? [redL redR].
      rewrite wkΠ_eq. set (X := wkΠ' _ _ _).
      unshelve econstructor; try change (tProd ?na _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩).
      1,2: now eapply wkΠTerm.
      + now eapply convtm_wk.
      + intros ? a ρ' ? ?. 
        replace (_ ⟨ ρ' ⟩) with (PiRedTm.nf redL) ⟨ρ' ∘w ρ⟩ by now bsimpl.
        replace (_ ⟨ ρ' ⟩) with (PiRedTm.nf redR) ⟨ρ' ∘w ρ⟩ by now bsimpl.
        irrelevance0.  2: unshelve eapply eqApp; [assumption|].
        2: irrelevance; subst X; now bsimpl.
        subst X; bsimpl; now try rewrite scons_comp'.
    - intros??? NA t u ? ρ wfΔ; revert t u; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA' t⟨ρ⟩ u⟨ρ⟩)) by apply h.
      subst G; apply NatRedEqInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNfEq.
  Qed.
End Weakenings.
