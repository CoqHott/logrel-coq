From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A} : Ne[Γ |- A] -> [Γ |- A] -> [ Γ |- A ~ A : U] -> [Γ ||-<l> A].
Proof.
  intros neA wtyA reflA. apply LRne_.
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l Γ A n} (h : [Γ ||-U<l> A]) :
  Ne[Γ |- n : A] ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [LogRelRec l | Γ ||-U n : A | h].
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, tm_ne_whne.
  * eapply tm_nf_conv; [|gen_typing|eassumption].
    now eapply tm_ne_nf.
  * eapply convtm_conv; tea; gen_typing.
  * eapply RedTyRecBwd, neu. 2,3: gen_typing.
    eapply ty_ne_term, tm_ne_conv; now gen_typing.
Defined.


Lemma neElim {Γ l K} : [Γ ||-<l> K] -> whne K -> [Γ ||-ne K].
Proof.
  intros h; pattern l,Γ,K,h; eapply LR_rect_TyUr;
  clear l Γ K h.
  - intros ??? [??? r] ne; pose proof (redtywf_whne r  ne); subst; inversion ne.
  - intros; assumption.
  - intros ??? [?? red] ?? ne ; cbn in *.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
  - intros ??? [red] ne.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
  - intros ??? [red] ne.
    rewrite (redtywf_whne red ne) in ne.
    inversion ne.
Qed.

Set Printing Primitive Projection Parameters.


Lemma neuEq {l Γ A B} (RA : [Γ ||-<l> A]) :
  Ne[Γ |- A] -> Ne[Γ |- B] ->
  [Γ |- A] -> [Γ |- B] ->
  [Γ |- A ~ B : U] ->
  [Γ ||-<l> A ≅ B | RA].
Proof.
  intros neA neB wtyA wtyB eqAB.
  unshelve irrelevance0. 1: assumption. 3: reflexivity.
  1: apply neu; try assumption; now eapply lrefl.
  econstructor.
  1: now apply redtywf_refl.
  all: cbn; assumption.
Qed.

Lemma ty_app_ren {Γ Δ A f a dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f : A] -> [Γ |- A ≅ tProd dom cod] -> [Δ |- a : dom⟨ρ⟩] -> [Δ |- tApp f⟨ρ⟩ a : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply ty_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma convneu_app_ren {Γ Δ A f g a b dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f ~ g : A] ->
  [Γ |- A ≅ tProd dom cod] ->
  [Δ |- a ≅ b : dom⟨ρ⟩] ->
  [Δ |- tApp f⟨ρ⟩ a ~ tApp g⟨ρ⟩ b : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply convneu_app. 3: eassumption.
  replace (tProd _ _) with (tProd dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma neu_app_ren {Γ Δ A n a dom cod} (ρ : Δ ≤ Γ) :
  [|- Δ] ->
  [Γ |- tProd dom cod] ->
  Ne[Γ |- n : A] -> [Γ |- A ≅ tProd dom cod] -> Nf[Δ |- a : dom⟨ρ⟩] -> Ne[Δ |- tApp n⟨ρ⟩ a : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up dom ρ⟩[a..]) by (now bsimpl).
  eapply tm_ne_app; [|eassumption].
  change (Ne[Δ |- n⟨ρ⟩ : (tProd dom cod)⟨ρ⟩]).
  eapply tm_ne_conv; [| |now eapply convty_wk].
  + now eapply tm_ne_wk.
  + now eapply wft_wk.
Qed.

Record complete {l Γ A} (RA : [Γ ||-<l> A]) := {
  reifyTyConv : forall B, [Γ ||-<l> A ≅ B | RA] -> Nf[Γ |- B];
  reflect : forall n n',
    Ne[Γ |- n : A] ->
    Ne[Γ |- n' : A] ->
    [Γ |- n : A] ->
    [Γ |- n' : A] ->
    [Γ |- n ~ n' : A] ->
    [Γ ||-<l> n : A | RA] × [Γ ||-<l> n ≅ n' : A| RA];
  reify : forall a, [Γ ||-<l> a : A | RA] -> Nf[ Γ |- a : A];
}.

Lemma complete_reflect_simpl {l Γ A} (RA : [Γ ||-<l> A]) (c : complete RA) :
  forall n, Ne[Γ |- n : A] -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA].
Proof.
intros; eapply c.
5: eassumption.
all: assumption.
Qed.

Lemma complete_var0 {l Γ A A'} (RA : [Γ ,, A ||-<l> A']) :
  complete RA ->
  [Γ ,, A |- A⟨↑⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros cRA conv HA.
  assert [Γ ,, A |- tRel 0 : A']
  by (eapply ty_conv; tea; escape; eapply (ty_var (wfc_wft EscRA) (in_here _ _))).
  eapply complete_reflect_simpl; tea.
  - eapply tm_ne_conv; tea. 
    2: now escape. 
    now eapply tm_ne_rel.
  - eapply convneu_var; tea.
Qed.


Lemma complete_U : forall l Γ A (RA : [Γ ||-U< l > A]), complete (LRU_ RA).
Proof.
intros l Γ A h0; split.
- intros ? [].
  eapply ty_nf_red, ty_nf_sort; gen_typing.
- intros ?? ???? h; pose proof (lrefl h); pose proof (urefl h).
  assert [Γ |- A ≅ U] by (destruct h0; gen_typing); split.
  2: unshelve econstructor.
  1-3: now apply neU.
  + eapply RedTyRecBwd, neu. 2,3: try gen_typing.
    eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
  + cbn. gen_typing.
  + eapply RedTyRecBwd; apply neu. 2, 3: gen_typing.
    eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
  + eapply TyEqRecBwd. eapply neuEq. all: try gen_typing.
    all: eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
- intros a [a' Hr Ha].
  assert ([Γ |-[ ta ] U ≅ A]).
  { destruct h0; gen_typing. }
  eapply tm_nf_conv; [| |eassumption].
  + eapply tm_nf_red; [eapply tmr_wf_red|]; eassumption.
  + now eapply escape, LRU_.
Qed.

Lemma complete_ne : forall l Γ A (RA : [Γ ||-ne A]), complete (LRne_ l RA).
Proof.
intros l Γ A h0; split.
- intros ? [].
  eapply ty_nf_red; [|now apply ty_ne_nf].
  gen_typing.
- destruct h0 as [B []]; intros ** ; assert ([Γ |- A ≅ B]) by gen_typing ; split.
  + exists n; cbn.
    * eapply redtmwf_refl ; gen_typing.
    * now eapply tm_ne_conv.
    * eapply lrefl; eapply convneu_conv; eassumption.
  + exists n n'; cbn.
    1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
    1,2: now eapply tm_ne_conv.
    gen_typing.
- intros a [a' Hr Hne].
  assert ([Γ |-[ ta ] neRedTy.ty h0 ≅ A]).
  { destruct h0; simpl in *; symmetry.
    eapply convty_exp; [now apply tyr_wf_red| |].
    all: gen_typing. }
  eapply tm_nf_conv; [| |eassumption].
  + eapply tm_nf_red; [now apply tmr_wf_red|].
    now apply tm_ne_nf.
  + now eapply escape, LRne_ with (l := l).
Qed.

Lemma complete_Pi : forall l Γ A (RA : [Γ ||-Π< l > A]),
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        complete (PiRedTyPack.domRed RA ρ h)) ->
  (forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PiRedTyPack.domRed RA ρ h | Δ ||- a : (PiRedTyPack.dom RA)⟨ρ⟩]),
        complete (PiRedTyPack.codRed RA ρ h ha)) ->
  complete (LRPi' RA).
Proof.
intros l Γ A ΠA0 ihdom ihcod; split.
- intros B ΠB.
  assert (tΓ : [|- Γ]) by (destruct ΠA0; gen_typing).
  eapply ty_nf_red; [apply tyr_wf_red, ΠB|].
  assert [PiRedTyPack.domRed ΠA0 wk_id tΓ | Γ ||- (PiRedTyPack.dom ΠA0)⟨wk_id⟩ ≅ PiRedTyEq.dom ΠB].
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
  assert [Γ |- A ≅ tProd dom cod] by gen_typing.
  unshelve refine ( let funred : forall n, Ne[Γ |- n : A] -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Π n : A | PiRedTyPack.toPiRedTy ΠA] := _ in _).
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
  assert ([Γ |- tProd dom codom ≅ A ]) by gen_typing.
  eapply tm_nf_conv; [| |eassumption].
  * eapply tm_nf_red; [now apply tmr_wf_red|].
    assumption.
  * destruct red; gen_typing.
Qed.

Lemma complete_Nat {l Γ A} (NA : [Γ ||-Nat A]) : complete (LRNat_ l NA).
Proof.
  split.
  - intros ? [].
    eapply ty_nf_red, ty_nf_nat; gen_typing.
  - intros. 
    assert [Γ |- A ≅ tNat] by (destruct NA; gen_typing). 
    assert [Γ |- n : tNat] by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,7: eapply convtm_convneu.
    1,4: eapply lrefl.
    4-6: now (eapply tm_ne_conv; gen_typing).
    all: eapply convneu_conv; tea.
  - simpl in *.
    assert [Γ |- tNat ≅ A] by (destruct NA; gen_typing).
    assert [Γ |- A] by now (destruct NA; gen_typing).
    intros a Ha; eapply tm_nf_conv; [|eassumption|eassumption]; revert a Ha.
    let T := match goal with |- ?P => P end in
    enough (IH : T × (forall (a : term) (n : NatProp NA a), Nf[ Γ |-[ ta ] a : tNat])); [apply IH|].
    apply NatRedInduction.
    + intros.
      eapply tm_nf_red; [now apply tmr_wf_red|eassumption].
    + eapply tm_nf_zero; gen_typing.
    + intros; now eapply tm_nf_succ.
    + intros ne []. apply tm_ne_nf. assumption.
Qed.

Lemma complete_Empty {l Γ A} (NA : [Γ ||-Empty A]) : complete (LREmpty_ l NA).
Proof.
  split.
  - intros ? [].
    eapply ty_nf_red, ty_nf_empty; gen_typing.
  - intros. 
    assert [Γ |- A ≅ tEmpty] by (destruct NA; gen_typing). 
    assert [Γ |- n : tEmpty] by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,7: eapply convtm_convneu.
    1,4: eapply lrefl.
    4-6: now (eapply tm_ne_conv; gen_typing).
    all: eapply convneu_conv; tea.
  - simpl in *.
    assert [Γ |- tEmpty ≅ A] by (destruct NA; gen_typing).
    intros a Ha; eapply tm_nf_conv; [| |eassumption].
    + destruct Ha.
      destruct prop.
      destruct r.
      eapply tm_nf_red. exact red.
      now apply tm_ne_nf.
    + destruct NA as [[]]; gen_typing.
Qed.

Lemma completeness {l Γ A} (RA : [Γ ||-<l> A]) : complete RA.
Proof.
revert l Γ A RA; eapply LR_rect_TyUr; cbn; intros.
- now apply complete_U.
- now apply complete_ne.
- now apply complete_Pi.
- now apply complete_Nat.
- now apply complete_Empty.
Qed.

Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  Ne[Γ |- n : A] ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
Proof.
  intros.  now eapply completeness.
Qed.

Lemma neuTermEq {l Γ A} (RA : [Γ ||-<l> A]) {n n'} :
  Ne[Γ |- n : A] ->
  Ne[Γ |- n' : A] ->
  [Γ |- n : A] ->
  [Γ |- n' : A] ->
  [Γ |- n ~ n' : A] ->
  [Γ ||-<l> n ≅ n' : A| RA].
Proof.
  intros; now eapply completeness.
Qed.

Lemma var0conv {l Γ A A'} (RA : [Γ ,, A ||-<l> A']) :
  [Γ,, A |- A⟨↑⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  apply complete_var0 ; now eapply completeness.
Qed.

Lemma var0 {l Γ A A'} (RA : [Γ ,, A ||-<l> A']) :
  A⟨↑⟩ = A' ->
  [Γ |- A] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros eq.
  apply var0conv.
  rewrite eq.
  unshelve eapply escapeEq; tea.
  eapply LRTyEqRefl_.
Qed.

Lemma reifyTerm {l Γ A} (RA : [Γ ||-<l> A]) {t} : [Γ ||-<l> t : A | RA] -> Nf[Γ |- t : A].
Proof.
intros; now eapply completeness.
Qed.

Lemma reifyType {l Γ A} (RA : [Γ ||-<l> A]) : Nf[Γ |- A].
Proof.
  unshelve eapply reifyTyConv; tea.
  1: now eapply completeness.
  apply LRTyEqRefl_.
Qed.

End Neutral.
