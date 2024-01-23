From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A} : [Γ |- A] -> [ Γ |- A ~ A : U] -> [Γ ||-<l> A].
Proof.
  intros wtyA reflA. apply LRne_.
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l Γ A n} (h : [Γ ||-U<l> A]) :
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [LogRelRec l | Γ ||-U n : A | h].
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, convneu_whne.
  * apply convtm_convneu ; tea.
    1: now constructor.
    now eapply convneu_conv.
  * eapply RedTyRecBwd, neu. 1,2: gen_typing.
Defined.


Set Printing Primitive Projection Parameters.


Lemma neuEq {l Γ A B} (RA : [Γ ||-<l> A]) :
  [Γ |- A] -> [Γ |- B] ->
  [Γ |- A ~ B : U] ->
  [Γ ||-<l> A ≅ B | RA].
Proof.
  intros wtyA wtyB eqAB.
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

Record complete {l Γ A} (RA : [Γ ||-<l> A]) := {
  reflect : forall n n',
    [Γ |- n : A] ->
    [Γ |- n' : A] ->
    [Γ |- n ~ n' : A] ->
    [Γ ||-<l> n : A | RA] × [Γ ||-<l> n ≅ n' : A| RA];
}.

Lemma complete_reflect_simpl {l Γ A} (RA : [Γ ||-<l> A]) (c : complete RA) :
  forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA].
Proof.
intros; eapply c.
all: eassumption.
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
  - eapply convneu_var; tea.
Qed.


Lemma complete_U : forall l Γ A (RA : [Γ ||-U< l > A]), complete (LRU_ RA).
Proof.
intros l Γ A h0; split.
- intros ???? h; pose proof (lrefl h); pose proof (urefl h).
  assert [Γ |- A ≅ U] by (destruct h0; gen_typing); split.
  2: unshelve econstructor.
  1-3: now apply neU.
  + eapply RedTyRecBwd, neu. 1,2: try gen_typing.
  + cbn. gen_typing.
  + eapply RedTyRecBwd; apply neu. 1,2: gen_typing.
  + eapply TyEqRecBwd. eapply neuEq. all: try gen_typing.
    all: eapply ty_ne_term, tm_ne_conv; tea; gen_typing.
Qed.

Lemma complete_ne : forall l Γ A (RA : [Γ ||-ne A]), complete (LRne_ l RA).
Proof.
intros l Γ A h0; split.
- destruct h0 as [B []]; intros ** ; assert ([Γ |- A ≅ B]) by gen_typing ; split.
  + exists n; cbn.
    * eapply redtmwf_refl ; gen_typing.
    * eapply lrefl; eapply convneu_conv; eassumption.
  + exists n n'; cbn.
    1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
    gen_typing.
Qed.

Lemma complete_Pi : forall l Γ A (RA : [Γ ||-Π< l > A]),
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        complete (PolyRed.shpRed RA ρ h)) ->
  (forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a : _]),
        complete (PolyRed.posRed RA ρ h ha)) ->
  complete (LRPi' RA).
Proof.
intros l Γ A ΠA0 ihdom ihcod; split.
- set (ΠA := ΠA0); destruct ΠA0 as [dom cod].
  simpl in ihdom, ihcod.
  assert [Γ |- A ≅ tProd dom cod] by gen_typing.
  assert [Γ |- A ≅ tProd dom cod] by gen_typing.
  assert [Γ |- dom].
  {
    erewrite <- wk_id_ren_on.
    eapply escape, polyRed.
    gen_typing.
  }
  assert [|- Γ ,, dom] as Hext by gen_typing.
  assert [Γ,, dom |-[ ta ] tRel 0 : dom⟨@wk1 Γ dom⟩].
  {
    eapply ty_var ; tea.
    rewrite wk1_ren_on.
    econstructor.
  }
  assert [Γ,, dom |-[ ta ] tRel 0 ~ tRel 0 : dom⟨@wk1 Γ dom⟩]
    by now apply convneu_var.
  assert [PolyRed.shpRed polyRed (wk1 dom) Hext | Γ,, dom ||- tRel 0 : dom⟨wk1 dom⟩]
    by now eapply ihdom.
  assert [Γ ,, dom |- cod].
  {
    replace cod with cod[tRel 0 .: @wk1 Γ dom >> tRel].
    2: bsimpl; rewrite scons_eta'; now asimpl.
    now eapply escape, polyRed.
  }
  assert (forall n Δ a (ρ : Δ ≤ Γ),
      [|- Δ] -> [Γ |- n : A] -> [Δ |- a : dom⟨ρ⟩] -> [Δ |-[ ta ] tApp n⟨ρ⟩ a : cod[a .: ρ >> tRel]]) as Happ.
    {
      intros.
      eapply typing_meta_conv.
      1: eapply ty_app ; tea.
      1: eapply typing_meta_conv.
      1: eapply ty_wk.
      - eassumption.
      - eapply ty_conv ; tea.
      - cbn ; reflexivity.
      - now bsimpl. 
    }
    assert (forall n, [Γ |- n : A] -> [Γ,, dom |-[ ta ] tApp n⟨@wk1 Γ dom⟩ (tRel 0) : cod]).
    {
      intros.
      eapply typing_meta_conv.
      1: apply Happ ; tea.
      bsimpl. rewrite scons_eta'. now bsimpl.
    }
  assert (forall n n',
    [Γ |- n : A] -> [Γ |- n' : A] ->
    [Γ |- n ~ n : A] -> [Γ |- n' ~ n' : A] -> 
    [Γ |- n ~ n' : A] ->
    [Γ |-[ ta ] n ≅ n' : tProd dom cod]).
  {
    intros.
    eapply convtm_eta ; tea.
    - now eapply ty_conv.
    - constructor.
      now eapply convneu_conv.
    - now eapply ty_conv.
    - econstructor.
      now eapply convneu_conv.
    - eapply convneu_app_ren in H21 ; tea ; cycle -1.
      2: eapply ihcod in H21 as [_ hred].
      + now eapply escapeEqTerm, reflLRTmEq.
      + erewrite <- wk1_ren_on.
        eapply convtm_meta_conv.
        1: now escape.
        1: bsimpl; rewrite scons_eta' ; now bsimpl.
        now bsimpl.
      + eapply typing_meta_conv ; eauto.
        bsimpl. rewrite scons_eta'. now bsimpl.
      + eapply typing_meta_conv ; eauto.
        bsimpl. rewrite scons_eta'. now bsimpl.
  }

  unshelve refine ( let funred : forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Π n : A | ΠA] := _ in _).
  {
    intros. exists n; cbn.
    - eapply redtmwf_refl ; gen_typing.
    - constructor; now eapply convneu_conv.
    - eauto.
    - intros.
      eapply ihcod ; last first.
      + eapply convne_meta_conv.
        1: eapply convneu_app.
        * eapply convne_meta_conv.
          1: eapply convneu_wk.
          2: eapply convneu_conv ; tea.
          all: cbn ; easy.
        * now eapply escapeEqTerm, reflLRTmEq.
        * now bsimpl.
        * reflexivity. 
      + eapply Happ ; tea.
        now escape.
      + eapply Happ ; tea.
        now escape.
    - intros.
      eapply ihcod ; last first.
      + eapply convne_meta_conv.
        1: eapply convneu_app.
        * eapply convne_meta_conv.
          1: eapply convneu_wk.
          2: eapply convneu_conv ; tea.
          all: cbn ; easy.
        * now escape.
        * now bsimpl.
        * reflexivity. 
      + eapply ty_conv.
        1: eapply Happ ; tea ; now escape.
        symmetry.
        eapply escapeEq, PolyRed.posExt ; tea.
      + eapply Happ ; tea.
        now escape.
  }

  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  split. 1: now apply funred.
  unshelve econstructor.
  1,2: now apply funred.
  all: cbn; clear funred.
  * eauto.
  * intros. apply ihcod; cbn.
    + apply escapeTerm in ha; now eapply ty_app_ren.
    + apply escapeTerm in ha; now eapply ty_app_ren.
    + eapply convneu_app_ren. 1,2: eassumption.
    eapply escapeEqTerm; eapply reflLRTmEq; eassumption.

  Unshelve.
  all: eauto.
Qed.

Arguments ParamRedTy.outTy /.

Lemma complete_Sig : forall l Γ A (RA : [Γ ||-Σ< l > A]),
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        complete (PolyRed.shpRed RA ρ h)) ->
  (forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a : _]),
        complete (PolyRed.posRed RA ρ h ha)) ->
  complete (LRSig' RA).
Proof.
  intros l Γ A ΣA0 ihdom ihcod.
  set (ΣA := ΣA0); destruct ΣA0 as [dom cod] ; cbn in *.

  assert [Γ |- A ≅ ΣA.(outTy)]
    by (destruct ΣA; cbn in *; gen_typing).
  assert [Γ |- ΣA.(outTy)]
    by (destruct ΣA; cbn in *; gen_typing).
  assert [Γ |- dom].
  {
    erewrite <- wk_id_ren_on.
    eapply escape, polyRed.
    gen_typing.
  } 
  assert [|- Γ ,, dom] as Hext by gen_typing.
  assert [Γ,, dom |-[ ta ] tRel 0 : dom⟨@wk1 Γ dom⟩].
  {
    eapply ty_var ; tea.
    rewrite wk1_ren_on.
    econstructor.
  }
  assert [Γ,, dom |-[ ta ] tRel 0 ~ tRel 0 : dom⟨@wk1 Γ dom⟩]
    by now apply convneu_var.
  assert [PolyRed.shpRed polyRed (wk1 dom) Hext | Γ,, dom ||- tRel 0 : dom⟨wk1 dom⟩]
    by now eapply ihdom.
  assert [Γ ,, dom |- cod].
  {
    replace cod with cod[tRel 0 .: @wk1 Γ dom >> tRel].
    2: bsimpl; rewrite scons_eta'; now asimpl.
    now eapply escape, polyRed.
  }
  assert (hfst : forall n Δ (ρ : Δ ≤ Γ) (h : [ |- Δ]), [Γ |- n : A] -> [Γ |- n ~ n : A] ->
    [PolyRedPack.shpRed ΣA ρ h | Δ ||- tFst n⟨ρ⟩ : _]).
    1:{
      intros; eapply complete_reflect_simpl.
      * eapply ihdom.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst; now eapply ty_conv.
      * rewrite wk_fst; eapply convneu_wk; tea.
        eapply convneu_fst; now eapply convneu_conv.
    }
  assert (hconv_fst : forall n n' Δ (ρ : Δ ≤ Γ) (h : [ |- Δ]), [Γ |- n : A] -> [Γ |- n' : A] -> [Γ |- n ~ n' : A] ->
    [PolyRedPack.shpRed ΣA ρ h | Δ ||- tFst n⟨ρ⟩ ≅ tFst n'⟨ρ⟩ : _]).
    1:{
      intros.
      eapply ihdom.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst; now eapply ty_conv.
      * rewrite wk_fst ; eapply ty_wk ; tea.
        eapply ty_fst ; now eapply ty_conv. 
      * repeat rewrite wk_fst; eapply convneu_wk; tea.
        eapply convneu_fst; now eapply convneu_conv.
    }
  assert (hconv : forall n n',
  [Γ |- n : A] -> [Γ |- n' : A] ->
  [Γ |- n ~ n : A] -> [Γ |- n' ~ n' : A] ->
  [Γ |- n ~ n' : A] -> [Γ |-[ ta ] n ≅ n' : tSig dom cod]).
  {
    intros.
    eapply convtm_eta_sig ; cbn in * ; tea.
    - now eapply ty_conv.
    - econstructor.
      now eapply convneu_conv.
    - now eapply ty_conv.
    - econstructor.
      now eapply convneu_conv.
    - eapply convtm_meta_conv.
      1: eapply escapeEqTerm, ihdom.
      4: now rewrite wk_id_ren_on.
      4: reflexivity.
      all: rewrite wk_id_ren_on.
      + now eapply ty_fst, ty_conv.
      + now eapply ty_fst, ty_conv.
      + eapply convneu_fst, convneu_conv ; tea.
      Unshelve.
      gen_typing.
    - eapply convtm_meta_conv.
      1: eapply escapeEqTerm, (ihcod _ (tFst n) wk_id).
      5: reflexivity.
      Unshelve.
      + eapply typing_meta_conv.
        1: gen_typing.
        now bsimpl.
      + eapply ty_conv.
        1: gen_typing.
        symmetry.
        replace (cod[(tFst n')..]) with (cod[(tFst n') .: (@wk_id Γ) >> tRel]) by (now bsimpl).
        eapply escapeEq, polyRed.(PolyRed.posExt) ; tea.
        Unshelve.
        * now erewrite <- wk_id_ren_on.
        * now erewrite <- (wk_id_ren_on _ n), <- (wk_id_ren_on _ n').
        * gen_typing.
        * now erewrite <- wk_id_ren_on.
      + eapply convne_meta_conv.
        1:now eapply convneu_snd, convneu_conv.
        1: now bsimpl.
        easy.
      + now bsimpl.
      + gen_typing.
      + now erewrite <- wk_id_ren_on.
      }
  split.
  unshelve refine ( let funred : forall n,
    [Γ |- n : A] ->
    [Γ |- n ~ n : A] -> [Γ ||-Σ n : A | ΣA] := _ in _).
  {
    intros n **.
    cbn in *.
    unshelve eexists n _.
    - intros. now eapply hfst. 
    - eapply redtmwf_refl; now eapply ty_conv.
    - constructor ; cbn ; now eapply convneu_conv.
    - eauto.
    - intros.
      cbn.
      eapply complete_reflect_simpl.
      * eapply ihcod.
      * rewrite wk_snd.
        eapply typing_meta_conv.
        1: eapply ty_wk ; tea.
        1: now eapply ty_snd, ty_conv.
        now bsimpl.
      * eapply convne_meta_conv.
        3: reflexivity.
        1: rewrite wk_snd.
        1: eapply convneu_wk ; tea.
        1: now eapply convneu_snd, convneu_conv.
        now bsimpl.
  }

  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).  
  unshelve refine (let Rn :[Γ ||-Σ n : A | ΣA] := _ in _).
    1: eapply funred; tea; now eapply lrefl.
    unshelve refine (let Rn' :[Γ ||-Σ n' : A | ΣA] := _ in _).
    1: eapply funred; tea; now eapply urefl.
    assert (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
      [Δ |- cod[tFst n⟨ρ⟩ .: ρ >> tRel] ≅ cod[tFst n'⟨ρ⟩ .: ρ >> tRel]]).
    {
      intros; eapply escapeEq; unshelve eapply (PolyRed.posExt ΣA); tea.
      + eapply Rn.
      + eapply Rn'.
      + now eapply hconv_fst.
    }
    split; tea; eexists Rn Rn'.
    + cbn.
      eapply hconv ; tea.
    + cbn. intros. now eapply hconv_fst.
    + intros; cbn; eapply ihcod.
      all: rewrite wk_fst; rewrite !wk_snd.
      2: eapply ty_conv; [|now symmetry]; rewrite wk_fst.
      all: rewrite <- subst_ren_subst_mixed.
      * eapply ty_wk; tea; eapply ty_snd; now eapply ty_conv.
      * eapply ty_wk; tea; eapply ty_snd; now eapply ty_conv.
      * eapply convneu_wk; tea; eapply convneu_snd; now eapply convneu_conv.
Qed.

Lemma complete_Nat {l Γ A} (NA : [Γ ||-Nat A]) : complete (LRNat_ l NA).
Proof.
  split.
  - intros. 
    assert [Γ |- A ≅ tNat] by (destruct NA; gen_typing). 
    assert [Γ |- n : tNat] by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,4: eapply convtm_convneu ; [now constructor|..].
    all: eapply convneu_conv; [|eassumption].
    all: first [assumption|now eapply lrefl].
Qed.

Lemma complete_Empty {l Γ A} (NA : [Γ ||-Empty A]) : complete (LREmpty_ l NA).
Proof.
  split.
  - intros. 
    assert [Γ |- A ≅ tEmpty] by (destruct NA; gen_typing). 
    assert [Γ |- n : tEmpty] by now eapply ty_conv.
    split; econstructor.
    1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
    2,4: do 2 constructor; tea.
    1,4: eapply convtm_convneu ; [now constructor|..].
    all: eapply convneu_conv; [|eassumption].
    all: try first [assumption|now eapply lrefl].
Qed.

Lemma complete_Id {l Γ A} (IA : [Γ ||-Id<l> A]) :
  complete (LRId' IA).
Proof.
  split; intros.
  assert [Γ |- A ≅ IA.(IdRedTy.outTy)] by (destruct IA; unfold IdRedTy.outTy; cbn; gen_typing).
  assert [Γ |- n : IA.(IdRedTy.outTy)] by now eapply ty_conv.
  split; econstructor.
  1,4,5: eapply redtmwf_refl; tea; now eapply ty_conv.
  2,4: do 2 constructor; tea.
  1,4: eapply convtm_convneu ; [now constructor|..].
  all: eapply convneu_conv; tea; now eapply lrefl.
Qed.

Lemma completeness {l Γ A} (RA : [Γ ||-<l> A]) : complete RA.
Proof.
revert l Γ A RA; eapply LR_rect_TyUr; cbn; intros.
- now apply complete_U.
- now apply complete_ne.
- now apply complete_Pi.
- now apply complete_Nat.
- now apply complete_Empty.
- now apply complete_Sig.
- now apply complete_Id.
Qed.

Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
Proof.
  intros.  now eapply completeness.
Qed.

Lemma neuTermEq {l Γ A} (RA : [Γ ||-<l> A]) {n n'} :
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
  eapply reflLRTyEq.
Qed.

End Neutral.