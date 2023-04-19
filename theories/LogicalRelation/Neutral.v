Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l wl Γ A} : Ne[Γ |- A]< wl > -> [Γ |- A]< wl > -> [ Γ |- A ~ A : U]< wl > -> [Γ ||-<l> A]< wl >.
Proof.
  intros neA wtyA reflA. apply LRne_.
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l wl Γ A n} (h : [Γ ||-U<l> A]< wl >) :
  Ne[Γ |- n : A]< wl > ->
  [Γ |- n : A]< wl > ->
  [Γ |- n ~ n : A]< wl > ->
  [LogRelRec l | Γ ||-U n : A | h]< wl >.
Proof.
  assert [Γ |- A ≅ U]< wl > by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, tm_ne_whne.
  * eapply tm_nf_conv.
    -- now eapply tm_ne_nf.
    -- assumption.
  * eapply convtm_conv; tea; gen_typing.
  * eapply RedTyRecBwd, neu. 2,3: gen_typing.
    eapply ty_ne_term, tm_ne_conv; now gen_typing.
Defined.


Lemma neElim {wl Γ l K} : [Γ ||-<l> K]< wl > -> whne K -> [Γ ||-ne K]< wl >.
Proof.
  intros h; pattern l,wl,Γ,K,h; eapply LR_rect_TyUr;
  clear l wl Γ K h.
  - intros ???? [??? r] ne; pose proof (redtywf_whne r  ne); subst; inversion ne.
  - intros; assumption.
  - intros ???? [?? red] ?? ne ; cbn in *.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
  - intros ???? [red] ne.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
  - intros ???? [red] ne.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
  - intros ???? [red] ne.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
Qed.

Set Printing Primitive Projection Parameters.


Lemma neuEq {l wl Γ A B} (RA : [Γ ||-<l> A]< wl >) :
  Ne[Γ |- A]< wl > -> Ne[Γ |- B]< wl > ->
  [Γ |- A]< wl > -> [Γ |- B]< wl > ->
  [Γ |- A ~ B : U]< wl > ->
  [Γ ||-<l> A ≅ B | RA]< wl >.
Proof.
  intros neA neB wtyA wtyB eqAB.
  unshelve irrelevance0. 1: assumption. 3: reflexivity.
  1: apply neu; try assumption; now eapply lrefl.
  econstructor.
  1: now apply redtywf_refl.
  all: cbn; assumption.
Qed.

Lemma ty_app_ren {wl Γ Δ A f a dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f : A]< wl > -> [Γ |- A ≅ tProd dom cod]< wl > -> [Δ |- a : dom⟨ρ⟩]< wl > -> [Δ |- tApp f⟨ρ⟩ a : cod[a .: ρ >> tRel]]< wl >.
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply ty_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma convneu_app_ren {wl Γ Δ A f g a b dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f ~ g : A]< wl > ->
  [Γ |- A ≅ tProd dom cod]< wl > ->
  [Δ |- a ≅ b : dom⟨ρ⟩]< wl > ->
  [Δ |- tApp f⟨ρ⟩ a ~ tApp g⟨ρ⟩ b : cod[a .: ρ >> tRel]]< wl >.
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply convneu_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma neu_app_ren {wl Γ Δ A n a dom cod} (ρ : Δ ≤ Γ) :
  [|- Δ]< wl > ->
  [Γ |- tProd dom cod]< wl > ->
  Ne[Γ |- n : A]< wl > -> [Γ |- A ≅ tProd dom cod]< wl > -> Nf[Δ |- a : dom⟨ρ⟩]< wl > -> Ne[Δ |- tApp n⟨ρ⟩ a : cod[a .: ρ >> tRel]]< wl >.
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  eapply tm_ne_app; [|eassumption].
  change (Ne[Δ |- n⟨ρ⟩ : (tProd dom cod)⟨ρ⟩]< wl >).
  eapply tm_ne_conv.
  + now eapply tm_ne_wk.
  + now eapply convty_wk.
Qed.

Record complete {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) := {
  reifyTyConvN :
    forall B,
      [Γ ||-<l> A ≅ B | RA]< wl > -> nat ;
  reifyTyConv :
    forall B (convB : [Γ ||-<l> A ≅ B | RA]< wl >)
           (wl' : wfLCon) (τ : wl' ≤ε wl)
           (Ninfl : reifyTyConvN B convB  <= length wl'),
        Nf[Γ |- B]< wl' > ;
  reflect : forall n n',
    Ne[Γ |- n : A]< wl > ->
    Ne[Γ |- n' : A]< wl > ->
    [Γ |- n : A]< wl > ->
    [Γ |- n' : A]< wl > ->
    [Γ |- n ~ n' : A]< wl > ->
    [Γ ||-<l> n : A | RA]< wl > × [Γ ||-<l> n ≅ n' : A| RA]< wl > ;
  reifyN : forall a, [Γ ||-<l> a : A | RA]< wl > -> nat ;
  reify : forall a (ha : [Γ ||-<l> a : A | RA]< wl >)
                 (wl' : wfLCon) (τ : wl' ≤ε wl)
                 (Ninfl : reifyN a ha  <= length wl'),
                   Nf[ Γ |- a : A]< wl' > ;
  }.

(*Record complete  {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) := {
  reifyTyConv :
    forall B (convB : [Γ ||-<l> A ≅ B | RA]< wl >),
        Nf[Γ |- B]< wl > ;
  reflect : forall n n',
    Ne[Γ |- n : A]< wl > ->
    Ne[Γ |- n' : A]< wl > ->
    [Γ |- n : A]< wl > ->
    [Γ |- n' : A]< wl > ->
    [Γ |- n ~ n' : A]< wl > ->
    [Γ ||-<l> n : A | RA]< wl > × [Γ ||-<l> n ≅ n' : A| RA]< wl > ;
  reify : forall a (ha : [Γ ||-<l> a : A | RA]< wl >),
      Nf[ Γ |- a : A]< wl > ;
    }.*)

Lemma complete_reflect_simpl {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) (c : complete RA) :
  forall n, Ne[Γ |- n : A]< wl > -> [Γ |- n : A]< wl > -> [Γ |- n ~ n : A]< wl > -> [Γ ||-<l> n : A | RA]< wl >.
Proof.
intros; eapply c.
5: eassumption.
all: assumption.
Qed.

Lemma complete_var0 {l wl Γ A A'} (RA : [Γ ,, A ||-<l> A']< wl >) :
  complete RA ->
  [Γ ,, A |- A⟨↑⟩ ≅ A']< wl > ->
  [Γ |- A]< wl > ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA]< wl >.
Proof.
  intros cRA conv HA.
  assert [Γ ,, A |- tRel 0 : A']< wl >
  by (eapply ty_conv; tea; escape; eapply (ty_var (wfc_wft EscRA) (in_here _ _))).
  eapply complete_reflect_simpl; tea.
  - eapply tm_ne_conv; tea. 
    now eapply tm_ne_rel.
  - eapply convneu_var; tea.
Qed.


Lemma complete_U : forall l wl Γ A (RA : [Γ ||-U< l > A]< wl >), complete (LRU_ RA).
Proof.
  intros l wl Γ A h0.
  unshelve econstructor.
  - exact (fun _ _ => 0).
  - exact (fun _ _ => 0).
  - intros ? [] ???.
    eapply ty_nf_red, ty_nf_sort ; gen_typing.
  - intros ?? ???? h; pose proof (lrefl h); pose proof (urefl h).
    assert [Γ |- A ≅ U]< wl > by (destruct h0; gen_typing); split.
    2: unshelve econstructor.
    1-3: now apply neU.
    + eapply RedTyRecBwd, neu. 2,3: try gen_typing.
      eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
    + cbn. gen_typing.
    + eapply RedTyRecBwd; apply neu. 2, 3: gen_typing.
      eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
    + eapply TyEqRecBwd. eapply neuEq. all: try gen_typing.
      all: eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
  - intros a [a' Hr Ha] ???.
    assert ([Γ |-[ ta ] U ≅ A]< wl >).
    { destruct h0; gen_typing. }
    eapply tm_nf_conv ; try easy.
    + eapply tm_nf_red; [eapply tmr_wf_red|].
      gen_typing.
      eapply tm_nf_red.
      now gen_typing.
      eapply tm_nf_Ltrans ; [ | eassumption].
      assumption.
    + eapply convty_Ltrans ; [ | eassumption].
      assumption.
Qed.

Lemma complete_ne : forall l wl Γ A (RA : [Γ ||-ne A]< wl >), complete (LRne_ l RA).
Proof.
  intros l wl Γ A h0. unshelve econstructor.
  - exact (fun _ _ => 0).
  - exact (fun _ _ => 0).
  - intros ? [] ???.
    eapply ty_nf_red.
    eapply redty_Ltrans ; try now destruct red.
    now eapply ty_nf_Ltrans ; try now apply ty_ne_nf.
  - destruct h0 as [B []]; intros ** ; assert ([Γ |- A ≅ B]< wl >) by gen_typing ;
      split.
  + exists n; cbn.
    * eapply redtmwf_refl ; gen_typing.
    * now eapply tm_ne_conv.
    * eapply lrefl; eapply convneu_conv; eassumption.
  + exists n n'; cbn.
    1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
    1,2: now eapply tm_ne_conv.
    gen_typing.
- intros a [a' Hr Hne] ???.
  assert ([Γ |-[ ta ] neRedTy.ty h0 ≅ A]< wl >).
  { destruct h0; simpl in *; symmetry.
    eapply convty_exp; [now apply tyr_wf_red| |].
    all: gen_typing. }
  eapply tm_nf_Ltrans.
  eassumption.
  eapply tm_nf_conv; [|eassumption].
  + eapply tm_nf_red; [now apply tmr_wf_red|].
    now apply tm_ne_nf.
Qed.

(*Lemma complete_Pi : forall l wl Γ A (RA : [Γ ||-Π< l > A]< wl >),
  (forall (Δ : context) (wl' : wfLCon) (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
          (Ninfl : (PiRedTyPack.domN RA) <= length wl')
          (h : [ |-[ ta ] Δ]< wl' >),
        complete (PiRedTyPack.domRed RA ρ τ Ninfl h)) ->
  (forall (Δ : context) (a : term) (wl' : wfLCon)
          (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
          (Ninfl : (PiRedTyPack.domN RA) <= length wl')
          (h : [ |-[ ta ] Δ]< wl' >)
          (ha : [PiRedTyPack.domRed RA ρ τ Ninfl h | Δ ||- a : (PiRedTyPack.dom RA)⟨ρ⟩]< wl' >)
          {wl'' : wfLCon}
          (τ' : wl'' ≤ε wl')
          (Minfl : PiRedTyPack.codomN RA ρ τ Ninfl h ha <= length wl''),
        complete (PiRedTyPack.codRed RA ρ τ Ninfl h ha τ' Minfl)) ->
  complete (LRPi' RA).
Proof.
  intros l wl Γ A ΠA0 ihdom ihcod.
  unshelve esplit.
  - intros B ΠB.
    exact (max (PiRedTyPack.domN ΠA0) (PiRedTyEq.domN ΠB)).
  - admit.
  - intros B ΠB ???.
    assert (tΓ : [|- Γ]< wl >) by (destruct ΠA0; gen_typing).
(*      eapply ty_nf_red ; try now apply tyr_wf_red, ΠB.
    
    eapply ty_nf_prod.
    * Search le minus 0.
      remember (max (PiRedTyPack.domN ΠA0) (PiRedTyEq.domN ΠB) - length wl) as m.
      revert wl tΓ ΠA0 ΠB ihdom ihcod Heqm.
      induction m ; intros.
      unshelve eapply ihdom.
      -- exact wk_id.
      -- now eapply wfLCon_le_id.
      -- eapply Nat.max_lub_l.
         eapply Nat.sub_0_le.
         now erewrite <- Heqm.
      -- assumption.
      -- erewrite <- wk_id_ren_on; eapply (PiRedTyEq.domRed ΠB).
         eapply Nat.max_lub_r.
         eapply Nat.sub_0_le.
         now erewrite <- Heqm.
      -- assert (ty_nf_ϝ : forall A n (ne : not_in_LCon (pi1 wl) n), 
                    Nf[ Γ |- A ]< wl ,,l (ne, true) > ->
                    Nf[ Γ |- A ]< wl ,,l (ne, false) > ->
                    Nf[ Γ |- A ]< wl > ).
         admit.
         assert (not_in_LCon wl 0) as Hyp.
         admit.
         unshelve eapply ty_nf_ϝ.
         ++ exact 0.
         ++ assumption.
         ++ pose (test := IHm (wl,,l (Hyp, true))
                            (wfc_Ltrans (LCon_le_step _ (wfLCon_le_id _)) tΓ)).
            eapply test.
         eapply Nat.sub_0_le.
         generalize (PiRedTyEq.domN ΠB).
         clear ihdom ihcod ΠA0 ΠB A B tΓ.
         intro n.
         remember (n - #|wl|) as m.
         revert wl Heqm.
         induction m.
         
         ++ reflexivity.
         ++ intros.
         (* Faire autant de splits que néccessaire pour que domN A et domN B
            soient < length wl *)
         eapply ty_nf_prod.

  
    unshelve refine (max (max (PiRedTyPack.domN ΠA0) (PiRedTyEq.domN ΠB)) _).
    unshelve eapply ihdom.
  - intros B ΠB.
    exact (PiRedTyPack.domN ΠA0).
  - cbn ; intros B ΠB * f Ninfl.
    assert (tΓ : [|- Γ]< wl >) by (destruct ΠA0; gen_typing).*)
    eapply ty_nf_red.
    + eapply redty_Ltrans ; try easy.
      apply tyr_wf_red, ΠB.
    + eapply ty_nf_prod.
      * destruct (ihdom Γ wl' (wk_id) τ (Nat.max_lub_l _ _ _ Ninfl) (wfc_Ltrans τ tΓ)).
        cbn in *.
        unshelve eapply ihdom.
        -- exact wl'.
        -- exact wk_id.
        -- assumption.
        -- now eapply Nat.max_lub_l.
        -- now eapply wfc_Ltrans.
        -- erewrite <- wk_id_ren_on.
           eapply (PiRedTyEq.domRed ΠB) ; now eapply Nat.max_lub_r.
        -- now eapply wfLCon_le_id.
        -- cbn.
            assert (forall (wl' : wfLCon) (τ : wl' ≤ε wl)
                 (Ninfl : (PiRedTyPack.domN ΠA0) <= length wl'),
                 [PiRedTyPack.domRed ΠA0 wk_id τ Ninfl (wfc_Ltrans τ tΓ) | Γ ||- (PiRedTyPack.dom ΠA0)⟨wk_id⟩ ≅ PiRedTyEq.dom ΠB]< wl >).
  1: erewrite <- wk_id_ren_on; eapply (PiRedTyEq.domRed ΠB).
  eapply ty_nf_prod.
  + now eapply ihdom.
  + unshelve eapply ihdom.
    * exact wk_id.
    * now eapply wfLCon_le_id.
    * 
  assert [forall (wl' : wfLCon) (τ : wl' ≤ε wl)
                 (Ninfl : (PiRedTyPack.domN RA) <= length wl'),
        PiRedTyPack.domRed ΠA0 wk_id tΓ | Γ ||- (PiRedTyPack.dom ΠA0)⟨wk_id⟩ ≅ PiRedTyEq.dom ΠB]< wl >.
  1: erewrite <- wk_id_ren_on; eapply (PiRedTyEq.domRed ΠB).
  eapply ty_nf_prod.
  + now eapply ihdom.
  + destruct ΠB as [dom cod ?? domRed codRed] ; cbn in *.
    assert [|- Γ ,, dom]. 1:{
      apply wfc_cons; tea.
      now eapply escapeConv.
    }
    eapply ihcod.
    replace cod with cod[tRel 0 .: @wk1 Γ dom >> tRel].
    2: bsimpl ; rewrite scons_eta' ; now bsimpl.
    eapply codRed.
    Unshelve.  1: tea.
    eapply complete_var0.
      * eapply ihdom.
      * symmetry; eapply escapeEq; erewrite <- wk1_ren_on.
        unshelve eapply domRed. tea.
      * now eapply escapeConv.
- set (ΠA := ΠA0); destruct ΠA0 as [dom cod].
  simpl in ihdom, ihcod.
  assert [Γ |- A ≅ tProd dom cod]< wl > by gen_typing.
  unshelve refine ( let funred : forall n, Ne[Γ |- n : A]< wl > -> [Γ |- n : A]< wl > -> [Γ |- n ~ n : A]< wl > -> [Γ ||-Π n : A | PiRedTyPack.toPiRedTy ΠA]< wl > := _ in _).
  {
    intros. exists n; cbn.
    * eapply redtmwf_refl ; gen_typing.
    * now eapply NeFun, tm_ne_whne.
    * eapply tm_nf_conv; [| |eassumption].
      + now eapply tm_ne_nf.
      + now eapply wft_prod.
    * gen_typing.
    * intros; apply complete_reflect_simpl; [apply ihcod| |..].
      { eapply neu_app_ren; try eassumption.
        + now apply wft_prod.
        + now apply (ihdom _ ρ h). }
      1: escape ; now eapply ty_app_ren.
      eapply convneu_app_ren. 1,2: eassumption.
      eapply LREqTermRefl_ in ha.
      now escape.
    * intros. apply ihcod.
      + eapply neu_app_ren; try eassumption.
        -- now apply wft_prod.
        -- now apply (ihdom _ ρ h).
      + eapply tm_ne_conv.
        - eapply neu_app_ren; try eassumption.
          -- now apply wft_prod.
          -- now apply (ihdom _ ρ h).
        - now eapply escape, codRed.
        - symmetry. now unshelve eapply escapeEq, codExt.
      + apply escapeTerm in ha; now eapply ty_app_ren.
      + pose proof (cv := escapeEq _ (codExt _ _ _ ρ _ ha hb eq0)).
        symmetry in cv; unshelve eapply (ty_conv _ cv).
        apply escapeTerm in hb; now eapply ty_app_ren.
      + apply escapeEqTerm in eq0; now eapply convneu_app_ren.
  }
  intros ?????? h.
  pose proof (lrefl h); pose proof (urefl h).
  split. 1: now apply funred.
  unshelve econstructor.
  1,2: now apply funred.
  all: cbn; clear funred.
  * gen_typing.
  * intros. apply ihcod; cbn.
    + eapply neu_app_ren; try eassumption.
      -- now apply wft_prod.
      -- now eapply (ihdom _ ρ).
    + eapply neu_app_ren; try eassumption.
      -- now apply wft_prod.
      -- now eapply (ihdom _ ρ).
    + apply escapeTerm in ha; now eapply ty_app_ren.
    + apply escapeTerm in ha; now eapply ty_app_ren.
    + eapply convneu_app_ren. 1,2: eassumption.
    eapply escapeEqTerm; eapply LREqTermRefl_; eassumption.
- intros a [a' Hr Ha].
  destruct ΠA0 as [dom codom]; simpl in *.
  assert ([Γ |- tProd dom codom ≅ A ]< wl >) by gen_typing.
  eapply tm_nf_conv; [| |eassumption].
  * eapply tm_nf_red; [now apply tmr_wf_red|].
    assumption.
  * destruct red; gen_typing.
Qed.

Lemma complete_Nat {l wl Γ A} (NA : [Γ ||-Nat A]< wl >) : complete (LRNat_ l NA).
Proof.
  split.
  - intros ? [].
    eapply ty_nf_red, ty_nf_nat; gen_typing.
  - intros. 
    assert [Γ |- A ≅ tNat]< wl > by (destruct NA; gen_typing). 
    assert [Γ |- n : tNat]< wl > by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,7: eapply convtm_convneu.
    1,4: eapply lrefl.
    4-6: now (eapply tm_ne_conv; gen_typing).
    all: eapply convneu_conv; tea.
  - simpl in *.
    assert [Γ |- tNat ≅ A]< wl > by (destruct NA; gen_typing).
    assert [Γ |- A]< wl > by now (destruct NA; gen_typing).
    intros a Ha; eapply tm_nf_conv; [|eassumption|eassumption]; revert a Ha.
    let T := match goal with |- ?P => P end in
    enough (IH : T × (forall (a : term) (n : NatProp NA a), Nf[ Γ |-[ ta ] a : tNat]< wl >)); [apply IH|].
    apply NatRedInduction.
    + intros.
      eapply tm_nf_red; [now apply tmr_wf_red|eassumption].
    + eapply tm_nf_zero; gen_typing.
    + intros; now eapply tm_nf_succ.
    + intros ne []. apply tm_ne_nf. assumption.
Qed.

Lemma complete_Empty {l wl Γ A} (NA : [Γ ||-Empty A]< wl >) : complete (LREmpty_ l NA).
Proof.
  split.
  - intros ? [].
    eapply ty_nf_red, ty_nf_empty; gen_typing.
  - intros. 
    assert [Γ |- A ≅ tEmpty]< wl > by (destruct NA; gen_typing). 
    assert [Γ |- n : tEmpty]< wl > by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,7: eapply convtm_convneu.
    1,4: eapply lrefl.
    4-6: now (eapply tm_ne_conv; gen_typing).
    all: eapply convneu_conv; tea.
  - simpl in *.
    assert [Γ |- tEmpty ≅ A]< wl > by (destruct NA; gen_typing).
    intros a Ha; eapply tm_nf_conv; [| |eassumption].
    + destruct Ha.
      destruct prop.
      destruct r.
      eapply tm_nf_red. exact red.
      now apply tm_ne_nf.
    + destruct NA as [[]]; gen_typing.
Qed.

Lemma completeness {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) : complete RA.
Proof.
revert l wl Γ A RA; eapply LR_rect_TyUr; cbn; intros.
- now apply complete_U.
- now apply complete_ne.
- now apply complete_Pi.
- now apply complete_Nat.
- now apply complete_Empty.
Qed.

Lemma neuTerm {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) {n} :
  Ne[Γ |- n : A]< wl > ->
  [Γ |- n : A]< wl > ->
  [Γ |- n ~ n : A]< wl > ->
  [Γ ||-<l> n : A | RA]< wl >.
Proof.
  intros.  now eapply completeness.
Qed.

Lemma neuTermEq {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) {n n'} :
  Ne[Γ |- n : A]< wl > ->
  Ne[Γ |- n' : A]< wl > ->
  [Γ |- n : A]< wl > ->
  [Γ |- n' : A]< wl > ->
  [Γ |- n ~ n' : A]< wl > ->
  [Γ ||-<l> n ≅ n' : A| RA]< wl >.
Proof.
  intros; now eapply completeness.
Qed.

Lemma var0conv {l wl Γ A A'} (RA : [Γ ,, A ||-<l> A']< wl >) :
  [Γ,, A |- A⟨↑⟩ ≅ A']< wl > ->
  [Γ |- A]< wl > ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA]< wl >.
Proof.
  apply complete_var0 ; now eapply completeness.
Qed.

Lemma var0 {l wl Γ A A'} (RA : [Γ ,, A ||-<l> A']< wl >) :
  A⟨↑⟩ = A' ->
  [Γ |- A]< wl > ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA]< wl >.
Proof.
  intros eq.
  apply var0conv.
  rewrite eq.
  unshelve eapply escapeEq; tea.
  eapply LRTyEqRefl_.
Qed.

Lemma reifyTerm {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) {t} : [Γ ||-<l> t : A | RA]< wl > -> Nf[Γ |- t : A]< wl >.
Proof.
intros; now eapply completeness.
Qed.

Lemma reifyType {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) : Nf[Γ |- A]< wl >.
Proof.
  unshelve eapply reifyTyConv; tea.
  1: now eapply completeness.
  apply LRTyEqRefl_.
Qed.
*)
End Neutral.
