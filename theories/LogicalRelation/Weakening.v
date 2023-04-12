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
  
   (* (ihdom : forall Δ' wl' (ρ' : Δ' ≤ Δ)
                    (τ : wl' ≤ε wl)
                    (Ninfl : (PiRedTyPack.domN ΠA) <= length wl'),
        [ |- Δ']< wl' > ->
        [Δ' ||-< l > (PiRedTyPack.dom ΠA)⟨ρ⟩⟨ρ'⟩]< wl' >)
    (ihcod : forall wl' (a : term)
                    (τ : wl' ≤ε wl)
                    (Ninfl : (PiRedTyPack.domN ΠA) <= length wl')
                    (wfΔ' : [|- Δ]< wl' >),
        [PiRedTyPack.domRed ΠA ρ τ Ninfl wfΔ' | _ ||- a : _]< wl' > ->
      forall Δ' (ρ' : Δ' ≤ Δ), [ |- Δ']< wl' > ->
      [Δ' ||-< l > (PiRedTyPack.cod ΠA)[a .: ρ >> tRel]⟨ρ'⟩]< wl' >)*)
  Proof.
    destruct ΠA as[dom cod];  cbn in *.
    assert (domRed' : forall Δ' wl' (ρ' : Δ' ≤ Δ) (τ : wl' ≤ε wl)
                             (Ninfl : domN <= length wl'),
               [|- Δ']< wl' > -> [Δ' ||-< l > dom⟨ρ⟩⟨ρ'⟩ ]< wl' >).
    {
      intros ? ? ρ' ??; replace (_⟨_⟩) with (dom⟨ρ' ∘w ρ⟩) by now bsimpl.
      econstructor; now unshelve eapply domRed.
    }
    set (cod' := cod⟨wk_up dom ρ⟩).
    unshelve refine
      (let codomN' : forall Δ' a wl' (ρ' : Δ' ≤ Δ) (τ : wl' ≤ε wl)
                             (Ninfl : domN <= length wl')
                             (h : [|- Δ']< wl' >)
                             (ha : [domRed' Δ' wl' ρ' τ Ninfl h | _ ||- a : _]< wl' >),
               nat := _ in _).
    { intros.
      unshelve eapply (codomN Δ' a wl' (ρ' ∘w ρ) τ Ninfl h).
      irrelevance.
    }
    cbn in *.
    assert (codRed' : forall Δ' a wl' (ρ' : Δ' ≤ Δ) (τ : wl' ≤ε wl)
                             (Ninfl : domN <= length wl')
                             (h : [|- Δ']< wl' >)
                             (ha : [domRed' Δ' wl' ρ' τ Ninfl h | _ ||- a : _]< wl' >)
                             (wl'' : wfLCon)
                             (τ' : wl'' ≤ε wl'),
               codomN' Δ' a wl' _ τ Ninfl h ha <= #|wl''| ->
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
    - intros * ihdom ihcod * [dom cod]. rewrite wkΠ_eq. set (X := wkΠ' _ _ _).
      exists (dom⟨ρ⟩) (cod⟨wk_up dom ρ⟩). cbn in *.
      + change (tProd _ _) with ((tProd dom cod)⟨ρ⟩);  gen_typing.
      + change (tProd dom⟨_⟩ _) with ((tProd dom cod)⟨ρ⟩).
        replace (tProd _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩) by now bsimpl.
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
    - intros * []; constructor.
      change tEmpty with tEmpty⟨ρ⟩; gen_typing.
  Qed.
    

  (* TODO: use program or equivalent to have only the first field non-opaque *)
  Lemma wkΠTerm {Γ Δ u A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) 
    (ΠA' := wkΠ' ρ wfΔ ΠA) : 
    [Γ||-Π u : A | PiRedTyPack.toPiRedTy ΠA] -> 
    [Δ ||-Π u⟨ρ⟩ : A⟨ρ⟩ | PiRedTyPack.toPiRedTy ΠA' ].
  Proof.
    intros [t].
    exists (t⟨ρ⟩); try change (tProd _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩).
    + now eapply redtmwf_wk.
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
    intros []; constructor. 1:apply tm_ne_wk. all: gen_typing.
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
      + now eapply redtmwf_wk.
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
    intros []; constructor. 1,2: apply tm_ne_wk. all: gen_typing.
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
      1,2: apply tm_ne_wk; assumption.
      now eapply convneu_wk.
    - intros ??? ΠA ihdom ihcod t u ? ρ ? [redL redR].
      rewrite wkΠ_eq. set (X := wkΠ' _ _).
      unshelve econstructor; try change (tProd _ _) with ((PiRedTyPack.prod ΠA)⟨ρ⟩).
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
  Qed.
End Weakenings.
