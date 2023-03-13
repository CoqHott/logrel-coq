From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped UntypedReduction UntypedValues Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance Escape.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A} : sne A -> [Γ |- A] -> [ Γ |- A ~ A : U] -> [Γ ||-<l> A].
Proof.
  intros neA wtyA reflA. apply LRne_.
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l Γ A n} (h : [Γ ||-U<l> A]) :
  sne n ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [LogRelRec l | Γ ||-U n : A | h].
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now apply NeType.
  * eapply convtm_conv; tea; gen_typing.
  * eapply RedTyRecBwd; apply neu; try assumption; gen_typing.
Defined.

Lemma neElim {Γ l K} : [Γ ||-<l> K] -> whne K -> [Γ ||-ne K].
Proof.
  intros h; pattern l,Γ,K,h; set (P := fun _ => _); eapply LR_rect_TyUr;
  clear l Γ K h.
  - intros ??? [??? r] ne; pose proof (redtywf_whne r  ne); subst; inversion ne.
  - intros ** ne; assumption.
  - intros ??? [??? [?? red]] ** ne ; cbn in *.
    apply redty_red in red.
    rewrite (red_whne _ _ red ne) in ne.
    inversion ne.
Qed.

Set Printing Primitive Projection Parameters.


Lemma neuEq {l Γ A B} (RA : [Γ ||-<l> A]) :
  sne A -> sne B ->
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

Lemma ty_app_ren {Γ Δ A f a na dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f : A] -> [Γ |- A ≅ tProd na dom cod] -> [Δ |- a : dom⟨ρ⟩] -> [Δ |- tApp f⟨ρ⟩ a : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up na dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply ty_app. 1,4: eassumption.
  replace (tProd _ _ _) with (tProd na dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma convneu_app_ren {Γ Δ A f g a b na dom cod} (ρ : Δ ≤ Γ) :
  [Γ |- f ~ g : A] ->
  [Γ |- A ≅ tProd na dom cod] ->
  [Δ |- a ≅ b : dom⟨ρ⟩] ->
  [Δ |- tApp f⟨ρ⟩ a ~ tApp g⟨ρ⟩ b : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up na dom ρ⟩[a..]) by (now bsimpl).
  unshelve eapply convneu_app. 1,4: eassumption.
  replace (tProd _ _ _) with (tProd na dom cod)⟨ρ⟩ by now bsimpl.
  gen_typing.
Qed.

Lemma neuTerm_aux {l Γ A} (RA : [Γ ||-<l> A]) :
  (forall n n',
  sne n ->
  sne n' ->
  [Γ |- n : A] ->
  [Γ |- n' : A] ->
  [Γ |- n ~ n' : A] ->
  [Γ ||-<l> n : A | RA] × [Γ ||-<l> n ≅ n' : A| RA])
  ×
  (forall a, [Γ ||-<l> a : A | RA] -> snf a).
Proof.
  pattern l, Γ, A, RA; set (P := fun _ => _).
  assert (helper : forall l Γ A RA, P l Γ A RA -> forall n, sne n -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA]).
  { intros ???? ih **; subst P; eapply ih. 5: eassumption. all: assumption. }
  eapply LR_rect_TyUr; clear l Γ A RA; subst P; cbn; intros ??? h0; split.
  - intros ?? ???? h; pose proof (lrefl h); pose proof (urefl h).
    assert [Γ |- A ≅ U] by (destruct h0; gen_typing); split.
    2: unshelve econstructor.
    1-3: now apply neU.
    + eapply RedTyRecBwd; apply neu ; try assumption; gen_typing.
    + cbn. gen_typing.
    + eapply RedTyRecBwd; apply neu; try assumption; gen_typing.
    + eapply TyEqRecBwd. eapply neuEq; try assumption; gen_typing.
  - intros a [a' Hr Ha].
    apply snf_red with a'; [now eapply redtmwf_red|now apply isSNType_snf].
  - destruct h0 as [B []]; intros ** ; assert ([Γ |- A ≅ B]) by gen_typing ; split.
    + exists n; cbn.
      * eapply redtmwf_refl ; gen_typing.
      * assumption.
      * eapply lrefl; eapply convneu_conv; eassumption.
    + exists n n'; cbn.
      1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
      1,2: assumption.
      gen_typing.
  - intros a [a' Hr Hne]; apply snf_sne with a'; [|assumption].
    eapply redtmwf_red; eassumption.
  - do 2 match goal with [ H : _ |- _ ] => revert H end.
    rename h0 into ΠA0; intros ihdom ihcod. set (ΠA := ΠA0); destruct ΠA0 as [na dom cod []].
    assert [Γ |- A ≅ tProd na dom cod] by gen_typing.
    unshelve refine ( let funred : forall n, sne n -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Π n : A | PiRedTyPack.toPiRedTy ΠA] := _ in _).
    {
      intros. exists n; cbn.
      * eapply redtmwf_refl ; gen_typing.
      * now eapply NeFun.
      * gen_typing.
      * intros; apply helper; [apply ihcod| |..].
        { eapply sne_tApp; [reflexivity|now apply sne_ren|].
          destruct (ihdom _ ρ h) as [_ Hnf].
          apply Hnf, ha. }
        1: apply escapeTerm_ in ha; now eapply ty_app_ren.
        eapply convneu_app_ren. 1,2: eassumption.
        eapply escapeEqTerm_; eapply LREqTermRefl_; eassumption.
      * intros. apply ihcod.
        + eapply sne_tApp; [reflexivity|now apply sne_ren|].
          destruct (ihdom _ ρ h) as [_ Hnf]; apply Hnf, ha.
        + eapply sne_tApp; [reflexivity|now apply sne_ren|].
          destruct (ihdom _ ρ h) as [_ Hnf]; apply Hnf, hb.
        + apply escapeTerm_ in ha; now eapply ty_app_ren.
        + pose proof (cv := escapeEq_ _ (codExt _ _ _ ρ _ ha hb eq0)).
          symmetry in cv; unshelve eapply (ty_conv _ cv).
          apply escapeTerm_ in hb; now eapply ty_app_ren.
        + apply escapeEqTerm_ in eq0; now eapply convneu_app_ren.
    }
    intros ?????? h.
    pose proof (lrefl h); pose proof (urefl h).
    split. 1: now apply funred.
    unshelve econstructor.
    1,2: now apply funred.
    all: cbn; clear funred.
    * gen_typing.
    * intros. apply ihcod; cbn.
      + eapply sne_tApp; [reflexivity|now apply sne_ren|].
        destruct (ihdom _ ρ h0) as [_ Hnf]; apply Hnf, ha.
      + eapply sne_tApp; [reflexivity|now apply sne_ren|].
        destruct (ihdom _ ρ h0) as [_ Hnf]; apply Hnf, ha.
      + apply escapeTerm_ in ha; now eapply ty_app_ren.
      + apply escapeTerm_ in ha; now eapply ty_app_ren.
      + eapply convneu_app_ren. 1,2: eassumption.
      eapply escapeEqTerm_; eapply LREqTermRefl_; eassumption.
  - do 2 match goal with [ H : _ |- _ ] => revert H end.
    intros ihdom ihcodom a [a' Hr Ha].
    apply snf_red with a'; [|now apply isSNFun_snf].
    now eapply redtmwf_red.
Qed.

Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  sne n ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
Proof.
  intros.  now eapply neuTerm_aux.
Qed.

Lemma neuTermEq {l Γ A} (RA : [Γ ||-<l> A]) {n n'} :
  sne n ->
  sne n' ->
  [Γ |- n : A] ->
  [Γ |- n' : A] ->
  [Γ |- n ~ n' : A] ->
  [Γ ||-<l> n ≅ n' : A| RA].
Proof.
  intros; now eapply neuTerm_aux.
Qed.

Lemma var0 {l Γ A A'} nA (RA : [Γ ,, vass nA A ||-<l> A']) :
  A⟨↑⟩ = A' ->
  [Γ ,, vass nA A ||-<l> tRel 0 : A' | RA].
Proof.
  intros <-.
  assert [Γ ,, vass nA A |- tRel 0 : A⟨↑⟩]
  by (escape; eapply (ty_var (wfc_wft EscRA) (in_here _ _))).
  eapply neuTerm; tea.
  - eapply sne_tRel; reflexivity.
  - eapply convneu_var; tea.
Qed.

Lemma reifyTerm {l Γ A} (RA : [Γ ||-<l> A]) {t} : [Γ ||-<l> t : A | RA] -> snf t.
Proof.
intros; now eapply neuTerm_aux.
Qed.

Lemma reifyType {l Γ A} (RA : [Γ ||-<l> A]) : snf A.
Proof.
assert (tΓ : wf_context Γ).
{ eapply wfc_wft, escape; apply RA. }
destruct RA as [RA HRA].
induction HRA.
+ apply snf_tSort with set.
  eapply redty_red, h.
+ destruct neA; eapply snf_sne; [|eassumption].
  eapply redty_red, red.
+ do 3 match goal with [ H : _ |- _ ] => revert H end.
  intros IHdom IHcodom tΓ.
  eapply snf_tProd.
  - eapply redty_red, ΠA.
  - specialize (IHdom _ wk_id tΓ (PiRedTy.domRed _ _ tΓ) tΓ).
    rewrite wk_id_ren_on in IHdom; apply IHdom.
  - destruct ΠA ; destruct HAad ; cbn in *.
    pose (Δ := Γ ,, vass na dom).
    assert (tΔ : wf_context Δ) by (now apply wfc_cons).
    unshelve epose (rdom := _ : [ Γ ,, vass na dom ||-< l > dom⟨@wk1 Γ na dom⟩ ]).
    { econstructor. exact (domAd (Γ,, vass na dom) (@wk1 Γ na dom) tΔ). }
    specialize (IHcodom _ (tRel 0) (wk1 na dom) tΔ).
    replace cod with (cod[tRel 0 .: @wk1 Γ na dom >> tRel]).
    eapply IHcodom.
    * change ([ Γ ,, vass na dom ||-< l > tRel 0 : dom⟨@wk1 Γ na dom⟩ | rdom ]).
      eapply var0. now bsimpl.
    * unshelve eapply codRed. eassumption.
      change ([ Γ ,, vass na dom ||-< l > tRel 0 : dom⟨@wk1 Γ na dom⟩ | rdom ]).
      eapply var0. now bsimpl.
    * eassumption.
    * bsimpl ; rewrite scons_eta' ; now bsimpl.
Qed.

End Neutral.
