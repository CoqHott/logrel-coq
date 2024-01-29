From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms UntypedValues Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance.

Set Universe Polymorphism.

Section Weakenings.
  Context `{GenericTypingProperties}.

  Lemma wkU {wl Γ Δ l A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (h : [Γ ||-U<l> A]< wl >) : [Δ ||-U<l> A⟨ρ⟩]< wl >.
  Proof. destruct h; econstructor; tea; change U with U⟨ρ⟩; gen_typing. Defined.

  Lemma wkΠ  {wl Γ Δ A l}
    (ΠA : [Γ ||-Π< l > A]< wl >)
    (ρ : Δ ≤ Γ)
    (wfΔ : [|- Δ]< wl >) :
    [Δ ||-Π< l > A⟨ρ⟩]< wl >.
  Proof.
    destruct ΠA as[dom cod];  cbn in *.
    unshelve refine (let domRed' : forall Δ' wl' (ρ' : Δ' ≤ Δ) (τ : wl' ≤ε wl)
                             (Ninfl : AllInLCon domN wl'),
               [|- Δ']< wl' > -> [Δ' ||-< l > dom⟨ρ⟩⟨ρ'⟩ ]< wl' > := _ in _).
    {
      intros ? ? ρ' ??.
      replace (_⟨_⟩) with (dom⟨ρ' ∘w ρ⟩) by now bsimpl.
      econstructor.
      now unshelve eapply domRed.
    }
    set (cod' := cod⟨wk_up dom ρ⟩).
    unshelve refine
      (let codomN' : forall Δ' a wl' (ρ' : Δ' ≤ Δ) (τ : wl' ≤ε wl)
                             (Ninfl : AllInLCon domN wl')
                             (h : [|- Δ']< wl' >)
                             (ha : [domRed' Δ' wl' ρ' τ Ninfl h | _ ||- a : _]< wl' >),
               nat := _ in _).
    { intros.
      unshelve eapply (codomN Δ' a wl' (ρ' ∘w ρ) τ Ninfl h).
      irrelevance.
    }
    cbn in *.
    assert (codRed' : forall Δ' a wl' (ρ' : Δ' ≤ Δ) (τ : wl' ≤ε wl)
                             (Ninfl : AllInLCon domN wl')
                             (h : [|- Δ']< wl' >)
                             (ha : [domRed' Δ' wl' ρ' τ Ninfl h | _ ||- a : _]< wl' >)
                             (wl'' : wfLCon)
                             (τ' : wl'' ≤ε wl'),
               AllInLCon (codomN' Δ' a wl' _ τ Ninfl h ha) wl'' ->
               [Δ' ||-< l > cod'[a .: ρ' >> tRel]]< wl'' >).
    {
      intros ? a wl' ρ' ??? ? ? ?.
      replace (cod'[a .: ρ' >> tRel]) with (cod[ a .: (ρ' ∘w ρ) >> tRel])
        by (unfold cod'; now bsimpl).
      econstructor; unshelve eapply codRed.
      - exact wl'.
      - assumption.
      - assumption.
      - assumption.
      - irrelevance.
      - assumption.
      - assumption.
    }
    exists (dom ⟨ρ⟩) cod' domN domRed' codomN' codRed'.
    + unfold cod'; change (tProd _ _) with ((tProd dom cod)⟨ρ⟩);  gen_typing.
    + gen_typing.
    + unfold cod'; set (ρ1 := wk_up (dom) ρ); eapply wft_wk; gen_typing.
    + unfold cod'; change (tProd _ _) with ((tProd dom cod)⟨ρ⟩);  gen_typing.
    + intros Δ' a b wl' ρ' ? ? wfΔ' ??? *. 
      replace (cod'[b .: ρ' >> tRel]) with (cod[ b .: (ρ' ∘w ρ) >> tRel]) by (unfold cod'; now bsimpl).
      subst cod'; unshelve epose (codExt Δ' a b wl' (ρ' ∘w ρ) τ Ninfl wfΔ' _ _ _ _ _ _) ; try irrelevance ; try assumption.
  Defined.

  Lemma wkNat {wl Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : [Γ ||-Nat A]< wl > -> [Δ ||-Nat A⟨ρ⟩]< wl >.
  Proof. 
    intros []; constructor.
    change tNat with tNat⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkBool {wl Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : [Γ ||-Bool A]< wl > -> [Δ ||-Bool A⟨ρ⟩]< wl >.
  Proof. 
    intros []; constructor.
    change tBool with tBool⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wkEmpty {wl Γ A Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) : [Γ ||-Empty A]< wl > -> [Δ ||-Empty A⟨ρ⟩]< wl >.
  Proof. 
    intros []; constructor.
    change tEmpty with tEmpty⟨ρ⟩.
    gen_typing. 
  Qed.

  Lemma wk@{i j k l} {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) :
    [LogRel@{i j k l} l | Γ ||- A]< wl > -> [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩]< wl >.
  Proof.
    intros lrA. revert Δ ρ wfΔ . pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr@{i j k l l}; clear l wl Γ A lrA.
    - intros **. apply LRU_. now eapply wkU.
    - intros ????[ty]???. apply LRne_.
      exists (ty⟨ρ⟩); [|now apply ty_ne_wk|change U with U⟨ρ⟩] ;gen_typing.
    - intros ????? ihdom ihcod ???. apply LRPi'; eapply (wkΠ ΠA ρ wfΔ).
    - intros; eapply LRNat_; now eapply wkNat.
    - intros; eapply LRBool_; now eapply wkBool.
    - intros; eapply LREmpty_; now eapply wkEmpty.
  Defined.

  Corollary Wwk@{i j k l} {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) :
    WLogRel@{i j k l} l wl Γ A ->
    WLogRel@{i j k l} l wl Δ A⟨ρ⟩.
  Proof.
    intros [].
    exists WN ; intros.
    eapply wk.
    - now eapply wfc_Ltrans.
    - now eapply WRed.
  Defined.
  
  Definition wkΠ' {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Π< l > A]< wl >) :=
    (*let ihdom Δ' (ρ' : Δ' ≤ Δ) (h : [ |- Δ']) := wk ρ' h (PiRedTyPack.domRed ΠA ρ wfΔ) in
    let ihcod a (ha : [PiRedTyPack.domRed ΠA ρ wfΔ | _ ||- a : _]) Δ' (ρ' : Δ' ≤ Δ) (h : [ |- Δ']) :=
      wk ρ' h (PiRedTyPack.codRed ΠA ρ wfΔ ha) 
    in*)
    wkΠ ΠA ρ wfΔ.

  Lemma wkΠ_eq {wl Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Π< l > A]< wl >) :
    wk ρ wfΔ (LRPi' ΠA) = LRPi' (wkΠ' ρ wfΔ ΠA).
  Proof. reflexivity. Qed.

  Set Printing Primitive Projection Parameters.

  Lemma wkEq@{i j k l} {wl Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >)
    (lrA : [Γ ||-<l> A]< wl >) : 
    [LogRel@{i j k l} l | Γ ||- A ≅ B | lrA]< wl > ->
    [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩ | wk ρ wfΔ lrA]< wl >.
  Proof.
    revert B Δ ρ wfΔ. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l wl Γ A lrA.
    - intros ??? ????? ? [] ; constructor; change U with U⟨ρ⟩; gen_typing.
    - intros * [ty].
      exists ty⟨ρ⟩.
      2: now apply ty_ne_wk, ne.
      1: gen_typing.
      cbn ; change U with U⟨ρ⟩; eapply convneu_wk; assumption.
    - intros * ihdom ihcod * [dom cod]. rewrite wkΠ_eq. set (X := wkΠ' _ _ _).
      unshelve econstructor.
      + exact (dom⟨ρ⟩).
      + exact (cod⟨wk_up dom ρ⟩).
      + exact domN.
      + unfold wkΠ'.
        intros ; unshelve eapply (codomN Δ0 a l' (ρ0 ∘w ρ) τ Ninfl Ninfl' h).
        subst X.
        irrelevance.
      + change (tProd _ _) with ((tProd dom cod)⟨ρ⟩);  gen_typing.
      + change (tProd dom⟨_⟩ _) with ((tProd dom cod)⟨ρ⟩).
        replace (tProd _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩) by now bsimpl.
        eapply convty_wk; assumption.
      + intros; irrelevanceRefl.
        unshelve eapply ihdom; try eassumption.
        * now eapply wfc_Ltrans.
        * now eapply domRed.
      + intros ? a wl' ρ' ?????????.
        replace (_[_ .: ρ' >> tRel]) with (cod[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
        irrelevance0.
        2: unshelve eapply codRed ; [exact wl'|..] ; subst X ; try irrelevance ; assumption.
        subst X; bsimpl; try rewrite scons_comp'; reflexivity.
    - intros * []; constructor.
      change tNat with tNat⟨ρ⟩; gen_typing.
    - intros * []; constructor.
      change tBool with tBool⟨ρ⟩; gen_typing.
    - intros * []; constructor.
      change tEmpty with tEmpty⟨ρ⟩; gen_typing.
  Qed.

  Lemma WwkEq@{i j k l} {wl Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >)
    (lrA : WLogRel@{i j k l} l wl Γ A) : 
    W[ Γ ||-< l > A ≅ B | lrA]< wl > ->
    W[ Δ ||-< l > A⟨ρ⟩ ≅ B⟨ρ⟩ | Wwk@{i j k l} ρ wfΔ lrA]< wl >.
  Proof.
    intros [].
    exists WNEq.
    intros.
    unshelve eapply wkEq.
    now eapply WRedEq.
  Qed.

  
  (* TODO: use program or equivalent to have only the first field non-opaque *)
  Lemma wkΠTerm {wl Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]< wl >) (ΠA : [Γ ||-Π< l > A]< wl >) 
    (ΠA' := wkΠ' ρ wfΔ ΠA) : 
    [Γ||-Π u : A | PiRedTyPack.toPiRedTy ΠA]< wl > -> 
    [Δ ||-Π u⟨ρ⟩ : A⟨ρ⟩ | PiRedTyPack.toPiRedTy ΠA' ]< wl >.
  Proof.
    intros [t]. 
    unshelve econstructor ;  try change (tProd _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩).
    - exact (t⟨ρ⟩).
    - exact redN.
    - intros ; unshelve eapply appN ; try assumption.
      exact (ρ0 ∘w ρ).
      subst ΠA'. 
      irrelevance.
    - now eapply redtmwf_wk.
    - apply isFun_ren; assumption.
    - now apply tm_nf_wk.
    - eapply convtm_wk; eassumption.
    - intros ? a ? ρ' * ?.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve eapply app;  [exact l'|..]; subst ΠA'; try irrelevance ; assumption. 
      subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
    - intros ???? ρ' ???????????.
      replace ((t ⟨ρ⟩)⟨ ρ' ⟩) with (t⟨ρ' ∘w ρ⟩) by now bsimpl.
      irrelevance0.
      2: unshelve eapply eq;  [exact l'|..]; subst ΠA'; try irrelevance ; assumption.
      subst ΠA'; bsimpl; try rewrite scons_comp'; reflexivity.
  Defined.

  Lemma wkNeNf {wl Γ Δ k A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) : 
    [Γ ||-NeNf k : A]< wl > -> [Δ ||-NeNf k⟨ρ⟩ : A⟨ρ⟩]< wl >.
  Proof.
    intros []; constructor. 1:apply tm_ne_wk. all: gen_typing.
  Qed.  

  Lemma wkTerm {wl Γ Δ t A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (lrA : [Γ ||-<l> A]< wl >) : 
    [Γ ||-<l> t : A | lrA]< wl > -> [Δ ||-<l> t⟨ρ⟩ : A⟨ρ⟩ | wk ρ wfΔ lrA]< wl >.
  Proof.
    revert t Δ ρ wfΔ. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l wl Γ A lrA.
    - intros ??????? ρ ? [te]; exists te⟨ρ⟩;  try change U with U⟨ρ⟩.
      1, 4: gen_typing.
      apply isType_ren; assumption.
      now apply tm_nf_wk.
      apply RedTyRecBwd ; apply wk; [assumption|]; now apply (RedTyRecFwd h).
    - intros ??????? ρ ? [te]. exists te⟨ρ⟩; cbn.
      + now eapply redtmwf_wk.
      + apply tm_ne_wk; assumption.
      + eapply convneu_wk; eassumption.
    - intros ????? ihdom ihcod ?? ρ ?; apply wkΠTerm. 
    - intros ???? NA t ? ρ wfΔ; revert t; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t, NatProp NA t -> NatProp NA' t⟨ρ⟩)) by apply h.
      subst G; apply NatRedInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNf.
    - intros ???? NA t ? ρ wfΔ.
      intros Ht ; induction Ht.
      econstructor.
      + change tBool with tBool⟨ρ⟩. gen_typing.
      + change tBool with tBool⟨ρ⟩. gen_typing.
      + clear red eq. inversion prop ; subst ; try now econstructor.
          constructor.
          change tBool with tBool⟨ρ⟩.
          now eapply wkNeNf.
    - intros ???? NA t ? ρ wfΔ.
      intro Ht ; induction Ht ; econstructor.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + inversion prop ; subst ; econstructor.
        change tEmpty with tEmpty⟨ρ⟩.
        now eapply wkNeNf.
  Qed.

  Lemma WwkTerm@{i j k l} {wl Γ Δ t A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >)
    (lrA : WLogRel@{i j k l} l wl Γ A) : 
    W[ Γ ||-< l > t : A | lrA]< wl > ->
    W[ Δ ||-< l > t⟨ρ⟩ : A⟨ρ⟩ | Wwk@{i j k l} ρ wfΔ lrA]< wl >.
  Proof.
    intros [].
    exists WNTm.
    intros.
    eapply wkTerm.
    now eapply WRedTm.
  Qed.
  
  Lemma wkUTerm {wl Γ Δ l A t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (h : [Γ ||-U<l> A]< wl >) :
    [LogRelRec l| Γ ||-U t : A | h ]< wl > -> [LogRelRec l | Δ||-U t⟨ρ⟩ : A⟨ρ⟩ | wkU ρ wfΔ h]< wl >.
  Proof.
    intros [te]. exists te⟨ρ⟩; change U with U⟨ρ⟩.
    1, 4: gen_typing.
    apply isType_ren; assumption.
    now apply tm_nf_wk.
    destruct l; [destruct (elim (URedTy.lt h))|cbn].
    eapply (wk (l:=zero)); eassumption.
  Defined.

  Lemma wkNeNfEq {wl Γ Δ k k' A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) : 
    [Γ ||-NeNf k ≅ k' : A]< wl > -> [Δ ||-NeNf k⟨ρ⟩ ≅ k'⟨ρ⟩ : A⟨ρ⟩]< wl >.
  Proof.
    intros []; constructor. 1,2: apply tm_ne_wk. all: gen_typing.
  Qed.  

  Lemma wkTermEq {wl Γ Δ t u A l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]< wl >) (lrA : [Γ ||-<l> A]< wl >) : 
    [Γ ||-<l> t ≅ u : A | lrA]< wl > -> [Δ ||-<l> t⟨ρ⟩ ≅ u⟨ρ⟩: A⟨ρ⟩ | wk ρ wfΔ lrA]< wl >.
  Proof.
    revert t u Δ ρ wfΔ. pattern l, wl, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l wl Γ A lrA.
    - intros ???????? ρ ? [rL rR].
      unshelve econstructor.
      + exact (wkUTerm ρ wfΔ h rL).
      + exact (wkUTerm ρ wfΔ h rR).
      + apply RedTyRecBwd; apply wk; [assumption|]; now apply (RedTyRecFwd h).
      + cbn. change U with U⟨ρ⟩. 
        now eapply convtm_wk.
      + apply RedTyRecBwd; apply wk; [assumption|]; now apply (RedTyRecFwd h).
      + apply TyEqRecBwd. eapply wkEq. now apply TyEqRecFwd.
    - intros ???????? ρ ? [tL tR].
      exists (tL⟨ρ⟩) (tR⟨ρ⟩); cbn.
      1,2: now eapply redtmwf_wk. 
      1,2: apply tm_ne_wk; assumption.
      now eapply convneu_wk.
    - intros ???? ΠA ihdom ihcod t u ? ρ ? [redL redR].
      rewrite wkΠ_eq. set (X := wkΠ' _ _).
      unshelve econstructor; try change (tProd _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩).
      1,2: now eapply wkΠTerm.
      + assumption.
      + intros ; unshelve eapply eqappN ; try assumption.
        exact (ρ0 ∘w ρ).
        subst X. 
        irrelevance.
      + now eapply convtm_wk.
      + intros ? a ? ρ' * ?. 
        replace (_ ⟨ ρ' ⟩) with (PiRedTm.nf redL) ⟨ρ' ∘w ρ⟩ by now bsimpl.
        replace (_ ⟨ ρ' ⟩) with (PiRedTm.nf redR) ⟨ρ' ∘w ρ⟩ by now bsimpl.
        irrelevance0.  2: unshelve eapply eqApp; [exact l'|..]; subst X; try irrelevance ; assumption. 
        subst X; bsimpl; now try rewrite scons_comp'.
    - intros ???? NA t u ? ρ wfΔ; revert t u; pose (NA' := wkNat ρ wfΔ NA).
      set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA' t⟨ρ⟩ u⟨ρ⟩)) by apply h.
      subst G; apply NatRedEqInduction.
      + intros; econstructor; tea; change tNat with tNat⟨ρ⟩; gen_typing.
      + constructor.
      + now constructor.
      + intros; constructor. 
        change tNat with tNat⟨ρ⟩.
        now eapply wkNeNfEq.
    - intros ???? NA t u ? ρ wfΔ Ht.
      induction Ht ; econstructor.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + change tBool with tBool⟨ρ⟩; gen_typing.
      + inversion prop ; subst ; econstructor.
        change tBool with tBool⟨ρ⟩.
          now eapply wkNeNfEq.
    - intros ???? NA t u ? ρ wfΔ Ht.
      induction Ht ; econstructor.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + change tEmpty with tEmpty⟨ρ⟩; gen_typing.
      + inversion prop ; subst ; econstructor.
        change tEmpty with tEmpty⟨ρ⟩.
        now eapply wkNeNfEq.
  Qed.
End Weakenings.
