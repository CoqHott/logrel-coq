From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms UntypedValues Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance.

Set Universe Polymorphism.

Section Weakenings.
  Context `{GenericTypingProperties}.

  Lemma wkU {Γ Δ l A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (h : [Γ ||-U<l> A]) : [Δ ||-U<l> A⟨ρ⟩].
  Proof. destruct h; econstructor; tea; change U with U⟨ρ⟩; gen_typing. Defined.

  Lemma wkPoly {Γ l shp pos Δ}  (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : 
    PolyRed Γ l shp pos -> 
    PolyRed Δ l shp⟨ρ⟩ pos⟨wk_up shp ρ⟩.
  Proof.
    intros []; opector.
    - intros ? ρ' ?; replace (_⟨_⟩) with (shp⟨ρ' ∘w ρ⟩) by now bsimpl.
      now eapply shpRed.
    - intros ? a ρ' **. 
      replace (pos⟨_⟩[a .: ρ' >> tRel]) with (pos[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
      econstructor; unshelve eapply posRed; tea; irrelevance.
    - now eapply wft_wk.
    - eapply wft_wk; tea; eapply wfc_cons; tea; now eapply wft_wk.
    - intros ? a b ρ'  wfΔ' **.
      replace (_[b .: ρ' >> tRel]) with (pos[ b .: (ρ' ∘w ρ) >> tRel]) by (now bsimpl).
      unshelve epose (posExt _ a b (ρ' ∘w ρ) wfΔ' _ _ _); irrelevance.
  Qed.

  Lemma wkΠ  {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) :
    [Δ ||-Π< l > A⟨ρ⟩].
  Proof.
    destruct ΠA; econstructor.
    3: now eapply wkPoly.
    1,2: rewrite wk_prod; now eapply redtywf_wk + now eapply convty_wk.
  Defined.

  Lemma wkΣ  {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΣA : [Γ ||-Σ< l > A]) :
    [Δ ||-Σ< l > A⟨ρ⟩].
  Proof.
    destruct ΣA; econstructor.
    3: now eapply wkPoly.
    1,2: rewrite wk_sig; now eapply redtywf_wk + now eapply convty_wk.
  Defined.

  Lemma wkNat {Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Nat A] -> [Δ ||-Nat A⟨ρ⟩].
  Proof. 
    intros []; constructor.
    change tNat with tNat⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkEmpty {Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Empty A] -> [Δ ||-Empty A⟨ρ⟩].
  Proof. 
    intros []; constructor.
    change tEmpty with tEmpty⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkList  {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ])
    (LA : [Γ ||-List< l > A]) :
    [Δ ||-List< l > A⟨ρ⟩].
  Proof.
    destruct LA as [ty].
    exists (ty ⟨ρ⟩).
    + change (tList _) with ((tList ty)⟨ρ⟩) ; gen_typing.
    + gen_typing.
    + change (tList _) with ((tList ty)⟨ρ⟩) ; gen_typing.
    + intros; rewrite wk_comp_ren_on; now apply parRed.
  Defined.

  Lemma wk@{i j k l} {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    [LogRel@{i j k l} l | Γ ||- A] -> [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩].
  Proof.
    intros lrA. revert Δ ρ wfΔ . pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr@{i j k l l}; clear l Γ A lrA.
    - intros **. apply LRU_. now eapply wkU.
    - intros ???[ty]???. apply LRne_.
      exists (ty⟨ρ⟩).
      + gen_typing.
      + change U with U⟨ρ⟩; apply convneu_wk; gen_typing.
    - intros; apply LRPi'; now eapply wkΠ.
    - intros; eapply LRNat_; now eapply wkNat.
    - intros; eapply LREmpty_; now eapply wkEmpty.
    - intros; apply LRSig'; now eapply wkΣ.
    - intros ??? ? ih ???. apply LRList'. eapply (wkList ρ wfΔ LA).
  Defined.

  (* Sanity checks for Π and Σ: we do compute correctly with wk *)
  #[local]
  Lemma wkΠ_eq {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) :
    wk ρ wfΔ (LRPi' ΠA) = LRPi' (wkΠ ρ wfΔ ΠA).
  Proof. reflexivity. Qed.
  
  #[local]
  Lemma wkΣ_eq {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Σ< l > A]) :
    wk ρ wfΔ (LRSig' ΠA) = LRSig' (wkΣ ρ wfΔ ΠA).
  Proof. reflexivity. Qed.

  Set Printing Primitive Projection Parameters.

  Lemma wkPolyEq {Γ l shp shp' pos pos' Δ}  (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (PA : PolyRed Γ l shp pos) : 
    PolyRedEq PA shp' pos' -> PolyRedEq (wkPoly ρ wfΔ PA) shp'⟨ρ⟩ pos'⟨wk_up shp' ρ⟩.
  Proof.
    intros []; opector.
    - intros ? ρ' wfΔ'; replace (_⟨_⟩) with (shp'⟨ρ' ∘w ρ⟩) by now bsimpl.
      pose (shpRed _ (ρ' ∘w ρ) wfΔ'); irrelevance.
    - intros ?? ρ' wfΔ' ha.
      replace (_[_ .: ρ' >> tRel]) with (pos'[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
      irrelevance0.
      2: unshelve eapply posRed; tea; irrelevance.
      now bsimpl.
  Qed.

  Lemma wkEq@{i j k l} {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (lrA : [Γ ||-<l> A]) : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA] ->
    [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩ | wk ρ wfΔ lrA].
  Proof.
    revert B Δ ρ wfΔ. pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros ?? ????? ? [] ; constructor; change U with U⟨ρ⟩; gen_typing.
    - intros * [ty].
      exists ty⟨ρ⟩.
      1: gen_typing.
      cbn ; change U with U⟨ρ⟩; eapply convneu_wk; assumption.
    - intros * ?? * []; rewrite wkΠ_eq ; eexists.
      3: now eapply wkPolyEq.
      + rewrite wk_prod;  gen_typing.
      + rewrite wk_prod.
        replace (tProd _ _) with (ΠA.(outTy)⟨ρ⟩) by (cbn; now bsimpl).
        now eapply convty_wk.
    - intros * []; constructor.
      change tNat with tNat⟨ρ⟩; gen_typing.
    - intros * []; constructor.
      change tEmpty with tEmpty⟨ρ⟩; gen_typing.
    - intros * ?? * []; rewrite wkΣ_eq ; eexists.
      3: now eapply wkPolyEq.
      + rewrite wk_sig;  gen_typing.
      + rewrite wk_sig.
        replace (tSig _ _) with (ΠA.(outTy)⟨ρ⟩) by (cbn; now bsimpl).
        now eapply convty_wk.
    - intros * ih * [ty].
      exists (ty⟨ρ⟩).
      + change (tList _) with ((tList ty)⟨ρ⟩) ; gen_typing.
      + cbn.
        change (tList ?ty⟨ρ⟩) with ((tList ty)⟨ρ⟩).
        now eapply convty_wk.
      + cbn in *.
        intros; irrelevanceRefl.
        now unshelve apply ih.
  Qed.

  (* TODO: use program or equivalent to have only the first field non-opaque *)
  Lemma wkΠTerm {Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) 
    (ΠA' := wkΠ ρ wfΔ ΠA) : 
    [Γ||-Π u : A | ΠA] -> 
    [Δ ||-Π u⟨ρ⟩ : A⟨ρ⟩ | ΠA' ].
  Proof.
    intros [t].
    exists (t⟨ρ⟩); try change (tProd _ _) with (ΠA.(outTy)⟨ρ⟩).
    + now eapply redtmwf_wk.
    + apply isFun_ren; assumption.
    + now apply convtm_wk.
    + intros ? a ρ' ??.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve apply app; [eassumption|]; subst ΠA'; irrelevance. 
      subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
    + intros ??? ρ' ?????.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve apply eq; [eassumption|..]; subst ΠA'; irrelevance.
      subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
  Defined.

  Lemma wkNeNf {Γ Δ k A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) : 
    [Γ ||-NeNf k : A] -> [Δ ||-NeNf k⟨ρ⟩ : A⟨ρ⟩].
  Proof.
    intros []; constructor. all: gen_typing.
  Qed.  
  
  Lemma wkΣTerm {Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Σ< l > A]) 
    (ΠA' := wkΣ ρ wfΔ ΠA) : 
    [Γ||-Σ u : A | ΠA] -> 
    [Δ ||-Σ u⟨ρ⟩ : A⟨ρ⟩ | ΠA' ].
  Proof.
    intros [t]. 
    unshelve eexists (t⟨ρ⟩) _; try (cbn; rewrite wk_sig).
    + intros ? ρ' wfΔ'; rewrite wk_comp_ren_on; irrelevance0.
      2: now unshelve eapply fstRed.
      cbn; symmetry; apply wk_comp_ren_on.
    + now eapply redtmwf_wk.
    + apply isPair_ren; assumption.
    + eapply convtm_wk; eassumption.
    + intros ? ρ' ?;  irrelevance0.
      2: rewrite wk_comp_ren_on; now unshelve eapply sndRed.
      rewrite <- wk_comp_ren_on; cbn; now rewrite <- wk_up_ren_subst.
  Defined.

  Lemma wkList_map_inv {Γ Δ A l n} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (LA : [Γ ||-List< l > A])
    (LA' := wkList ρ wfΔ LA) :
    ListRedTm.map_inv LA n -> ListRedTm.map_inv LA' n⟨ρ⟩.
  Proof.
    destruct n; try easy.
    intros []; unshelve econstructor; cbn; refold.
    1-2: now eapply wft_wk.
    all: rewrite ?wk_arr, ?wk_list.
    1,2: now eapply ty_wk.
    1,2: now eapply convty_wk.
    + now eapply convneu_wk.
    + intros. irrelevance0; rewrite wk_comp_ren_on.
      1: reflexivity. 
      apply redfn; now rewrite <- wk_comp_ren_on.
      Unshelve. tea.
  Qed.

  Lemma wkListTerm {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (LA : [Γ ||-List< l > A])
      (ih : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (t : term) (Δ' : context) (ρ' : Δ' ≤ Δ) (wfΔ' : [ |-[ ta ] Δ']),
        [ListRedTy.parRed LA ρ wfΔ | Δ ||- t : (ListRedTy.par LA)⟨ρ⟩] ->
        [wk ρ' wfΔ' (ListRedTy.parRed LA ρ wfΔ) | Δ' ||- t⟨ρ'⟩ : (ListRedTy.par LA)⟨ρ⟩⟨ρ'⟩])
    (LA' := wkList ρ wfΔ LA) :
    (forall u, [Γ ||-<l> u : A | LRList' LA] ->
          [Δ ||-<l> u⟨ρ⟩ : A⟨ρ⟩ | LRList' LA' ])
      × (forall u, ListProp Γ A LA u -> ListProp Δ A⟨ρ⟩ LA' u⟨ρ⟩).
  Proof.
    eapply ListRedInduction.
    - intros. econstructor.
      + cbn. change (tList ?e⟨ρ⟩) with ((tList e)⟨ρ⟩).
        now eapply redtmwf_wk.
      + cbn. change (tList ?e⟨ρ⟩) with ((tList e)⟨ρ⟩).
        now eapply convtm_wk.
      + assumption.
    - intros. unshelve econstructor; tea.
      + now eapply wft_wk.
      + cbn; now eapply convty_wk.
    - intros. unshelve econstructor; tea.
      + now eapply wft_wk.
      + cbn; now eapply convty_wk.
      + fold ren_term. 
        irrelevance0.
        2: now apply ih.
        now rewrite 2!wk_id_ren_on.
        Unshelve. tea.
    - intros. econstructor.
      + cbn; change (tList ?e⟨ρ⟩) with ((tList e)⟨ρ⟩).
        now eapply ty_wk.
      + now eapply convneulist_wk.
      + now apply wkList_map_inv.
  Defined.

  Lemma wkTerm {Γ Δ t A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (lrA : [Γ ||-<l> A]) : 
    [Γ ||-<l> t : A | lrA] -> [Δ ||-<l> t⟨ρ⟩ : A⟨ρ⟩ | wk ρ wfΔ lrA].
  Proof.
    revert t Δ ρ wfΔ. pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros ?????? ρ ? [te]; exists te⟨ρ⟩;  try change U with U⟨ρ⟩.
      + gen_typing.
      + apply isType_ren; assumption.
      + now apply convtm_wk.
      + apply RedTyRecBwd ; apply wk; [assumption|]; now apply (RedTyRecFwd h).
    - intros ?????? ρ ? [te]. exists te⟨ρ⟩; cbn.
      + now eapply redtmwf_wk.
      + apply convneu_wk; assumption.
    - intros; now apply wkΠTerm. 
    - intros??? NA t ? ρ wfΔ; revert t; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, NatProp NA t -> NatProp NA' t⟨ρ⟩)) by apply h.
      subst G; apply NatRedInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNf.
    - intros??? NA t ? ρ wfΔ; revert t; pose (NA' := wkEmpty ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, EmptyProp Γ t -> EmptyProp Δ t⟨ρ⟩)) by apply h.
      subst G.
      split.
      2:{ intros t Ht. inversion Ht. subst. econstructor.
          change tEmpty with tEmpty⟨ρ⟩.
          now eapply wkNeNf. }
      intros t Ht. induction Ht. econstructor.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + destruct prop. econstructor.
        change tEmpty with tEmpty⟨ρ⟩.
        now eapply wkNeNf.
    - intros; now apply wkΣTerm. 
    - intros * ih *. now eapply wkListTerm.
  Qed.


  Lemma wkListTerm' {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (LA : [Γ ||-List< l > A])
    (LA' := wkList ρ wfΔ LA) :
    (forall u, [Γ ||-<l> u : A | LRList' LA] ->
          [Δ ||-<l> u⟨ρ⟩ : A⟨ρ⟩ | LRList' LA' ])
      × (forall u, ListProp Γ A LA u -> ListProp Δ A⟨ρ⟩ LA' u⟨ρ⟩).
  Proof.
    apply wkListTerm.
    intros. now apply wkTerm.
  Defined.

  Lemma wkUTerm {Γ Δ l A t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (h : [Γ ||-U<l> A]) :
    [LogRelRec l| Γ ||-U t : A | h ] -> [LogRelRec l | Δ||-U t⟨ρ⟩ : A⟨ρ⟩ | wkU ρ wfΔ h].
  Proof.
    intros [te]. exists te⟨ρ⟩; change U with U⟨ρ⟩.
    - gen_typing.
    - apply isType_ren; assumption.
    - now apply convtm_wk.
    - destruct l; [destruct (elim (URedTy.lt h))|cbn].
      eapply (wk (l:=zero)); eassumption.
  Defined.

  Lemma wkNeNfEq {Γ Δ k k' A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) : 
    [Γ ||-NeNf k ≅ k' : A] -> [Δ ||-NeNf k⟨ρ⟩ ≅ k'⟨ρ⟩ : A⟨ρ⟩].
  Proof.
    intros []; constructor. gen_typing.
  Qed.  

  Lemma not_map_into_view {Γ Δ} (ρ : Δ ≤ Γ) l :
    ~~ Map.is_map l -> ∑ p, Map.into_view l⟨ρ⟩ = Map.IsNotMap p.
  Proof.
    destruct l; try discriminate; eexists; reflexivity.
  Qed.

  Lemma wkListRedTmEq_map_inv_eq {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (LA : [Γ ||-List< l > A])
    (LA' := wkList ρ wfΔ LA) m n :
    ListRedTmEq.map_inv_eq LA m n ->
    ListRedTmEq.map_inv_eq LA' m⟨ρ⟩ n⟨ρ⟩.
  Proof.
    unfold ListRedTmEq.map_inv_eq.
    do 2 (destruct (Map.into_view _); cbn).
    + intros []; split.
      1,2: now eapply convty_wk.
      1: cbn; refold; rewrite wk_list; now eapply convneu_wk.
      intros; irrelevance0.
      2: refold; rewrite 2!wk_comp_ren_on; apply convredfn; now rewrite <- wk_comp_ren_on.
      now rewrite <- wk_comp_ren_on.
      Unshelve. tea.
    + eapply not_map_into_view in i as [? ->].
      intros []; split.
      * now eapply convty_wk.
      * refold; rewrite wk_list; now eapply convneu_wk.
      * intros; irrelevance0.
        2: refold; rewrite wk_comp_ren_on; apply convredfn_id ; now rewrite <- wk_comp_ren_on.
        now rewrite <- wk_comp_ren_on.
      Unshelve. tea.
    + eapply not_map_into_view in i as [? ->].
      intros []; split.
      * now eapply convty_wk.
      * refold; rewrite wk_list; now eapply convneu_wk.
      * intros; irrelevance0.
        2: refold; rewrite wk_comp_ren_on; apply convredfn_id ; now rewrite <- wk_comp_ren_on.
        now rewrite <- wk_comp_ren_on.
      Unshelve. tea.
    + eapply not_map_into_view in i as [? ->].
      eapply not_map_into_view in i0 as [? ->].
      easy.
  Qed.


  Lemma wkListTermEq {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (LA : [Γ ||-List< l > A])
    (ih : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) 
      (t u : term) (Δ' : context) (ρ' : Δ' ≤ Δ) (wfΔ' : [ |-[ ta ] Δ']),
      [ListRedTy.parRed LA ρ wfΔ | Δ ||- t ≅ u : (ListRedTy.par LA)⟨ρ⟩] ->
      [wk ρ' wfΔ' (ListRedTy.parRed LA ρ wfΔ) | Δ' ||- t⟨ρ'⟩ ≅ u⟨ρ'⟩ : (ListRedTy.par LA)⟨ρ⟩⟨ρ'⟩])
    (LA' := wkList ρ wfΔ LA) :
    (forall u t, [Γ ||-<l> u ≅ t : A | LRList' LA] ->
          [Δ ||-<l> u⟨ρ⟩ ≅ t⟨ρ⟩ : A⟨ρ⟩ | LRList' LA' ])
      × (forall u t, ListPropEq Γ A LA u t -> ListPropEq Δ A⟨ρ⟩ LA' u⟨ρ⟩ t⟨ρ⟩).
  Proof.
    eapply ListRedEqInduction.
    - intros.
      unshelve eexists.
      1-2: now apply wkListTerm'.
      + cbn.
        destruct Rt, Ru.
        cbn.
        change (tList ?e⟨ρ⟩) with ((tList e)⟨ρ⟩).
        now eapply convtm_wk.
      + destruct Rt, Ru.
        cbn.
        assumption.
    - intros. unshelve econstructor; tea.
      + now eapply wft_wk.
      + cbn; now eapply convty_wk.
      + now eapply wft_wk.
      + cbn; now eapply convty_wk.
    - intros. unshelve econstructor; tea.
      + now eapply wft_wk.
      + cbn; now eapply convty_wk.
      + now eapply wft_wk.
      + cbn; now eapply convty_wk.
      + irrelevance0.
        2: now apply ih.
        now rewrite 2! wk_id_ren_on.
        Unshelve. tea.
    - intros. constructor.
      2, 3: apply wkList_map_inv; tea; intros; now eapply wkTerm.
      2: now eapply wkListRedTmEq_map_inv_eq.
      cbn; change (tList ?e⟨ρ⟩) with ((tList e)⟨ρ⟩).
      now eapply convneulist_wk.
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
      1,2: now eapply redtmwf_wk.
      now eapply convneu_wk.
    - intros * ?? * []; rewrite wkΠ_eq. 
      unshelve econstructor; cbn; try rewrite wk_prod.
      1,2: now eapply wkΠTerm.
      + now eapply convtm_wk.
      + intros; cbn; do 2 rewrite wk_comp_ren_on.
        irrelevance0.  2: unshelve eapply eqApp; [assumption|].
        2: irrelevance.
        now rewrite <- wk_up_ren_subst.
    - intros??? NA t u ? ρ wfΔ; revert t u; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA' t⟨ρ⟩ u⟨ρ⟩)) by apply h.
      subst G; apply NatRedEqInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNfEq.
    - intros??? NA t u ? ρ wfΔ; revert t u; pose (NA' := wkEmpty ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t u, EmptyPropEq Γ t u -> EmptyPropEq Δ t⟨ρ⟩ u⟨ρ⟩)) by apply h.
      subst G. split.
      2:{ intros t u Ht. inversion Ht. subst. econstructor.
          change tEmpty with tEmpty⟨ρ⟩.
          now eapply wkNeNfEq. }
      intros t u Ht. induction Ht. econstructor.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + destruct prop. econstructor.
        change tEmpty with tEmpty⟨ρ⟩.
        now eapply wkNeNfEq.
    - intros * ?? * []; rewrite wkΣ_eq. 
      unshelve econstructor; cbn; try rewrite wk_sig.
      1,2: now eapply wkΣTerm.
      + now eapply convtm_wk.
      + intros; cbn; do 2 rewrite wk_comp_ren_on.
        irrelevance0. 2: now unshelve eapply eqFst.
        now rewrite wk_comp_ren_on.
      + intros; cbn; irrelevance0.
        2: do 2 rewrite wk_comp_ren_on; now unshelve eapply eqSnd.
        rewrite wk_comp_ren_on; now rewrite <- wk_up_ren_subst.
    - intros. now eapply wkListTermEq.
  Qed.
End Weakenings.
