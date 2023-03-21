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
  * eapply tm_nf_conv; [|eassumption].
    now eapply tm_ne_nf.
  * eapply convtm_conv; tea; gen_typing.
  * eapply RedTyRecBwd, neu. 2,3: gen_typing.
    now eapply ty_ne_term, tm_ne_conv.
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

Lemma neu_app_ren {Γ Δ A n a na dom cod} (ρ : Δ ≤ Γ) :
  [|- Δ] ->
  Ne[Γ |- n : A] -> [Γ |- A ≅ tProd na dom cod] -> Nf[Δ |- a : dom⟨ρ⟩] -> Ne[Δ |- tApp n⟨ρ⟩ a : cod[a .: ρ >> tRel]].
Proof.
  intros.
  replace (cod[a .: ρ >> tRel]) with (cod⟨wk_up na dom ρ⟩[a..]) by (now bsimpl).
  eapply tm_ne_app; [|eassumption].
  instantiate (1 := na).
  change (Ne[Δ |- n⟨ρ⟩ : (tProd na dom cod)⟨ρ⟩]).
  eapply tm_ne_conv; [|now eapply convty_wk].
  now eapply tm_ne_wk.
Qed.

Lemma neuTerm_aux {l Γ A} (RA : [Γ ||-<l> A]) :
  (forall n n',
  Ne[Γ |- n : A] ->
  Ne[Γ |- n' : A] ->
  [Γ |- n : A] ->
  [Γ |- n' : A] ->
  [Γ |- n ~ n' : A] ->
  [Γ ||-<l> n : A | RA] × [Γ ||-<l> n ≅ n' : A| RA])
  ×
  (forall a, [Γ ||-<l> a : A | RA] -> Nf[ Γ |- a : A]).
Proof.
  pattern l, Γ, A, RA; set (P := fun _ => _).
  assert (helper : forall l Γ A RA, P l Γ A RA -> forall n, Ne[Γ |- n : A] -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA]).
  { intros ???? ih **; subst P; eapply ih. 5: eassumption. all: assumption. }
  eapply LR_rect_TyUr; clear l Γ A RA; subst P; cbn; intros ??? h0; split.
  - intros ?? ???? h; pose proof (lrefl h); pose proof (urefl h).
    assert [Γ |- A ≅ U] by (destruct h0; gen_typing); split.
    2: unshelve econstructor.
    1-3: now apply neU.
    + eapply RedTyRecBwd, neu. 2,3: try gen_typing.
      now eapply ty_ne_term, tm_ne_conv.
    + cbn. gen_typing.
    + eapply RedTyRecBwd; apply neu. 2, 3: gen_typing.
      now eapply ty_ne_term, tm_ne_conv.
    + eapply TyEqRecBwd. eapply neuEq. all: try gen_typing.
      all: now eapply ty_ne_term, tm_ne_conv.
  - intros a [a' Hr Ha].
    assert ([Γ |-[ ta ] U ≅ A]).
    { destruct h0; gen_typing. }
    eapply tm_nf_conv; [|eassumption].
    eapply tm_nf_red; [eapply tmr_wf_red|]; eassumption.
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
    eapply tm_nf_conv; [|eassumption].
    eapply tm_nf_red; [now apply tmr_wf_red|].
    now apply tm_ne_nf.
  - do 2 match goal with [ H : _ |- _ ] => revert H end.
    rename h0 into ΠA0; intros ihdom ihcod. set (ΠA := ΠA0); destruct ΠA0 as [na dom cod []].
    simpl in ihdom, ihcod.
    assert [Γ |- A ≅ tProd na dom cod] by gen_typing.
    unshelve refine ( let funred : forall n, Ne[Γ |- n : A] -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Π n : A | PiRedTyPack.toPiRedTy ΠA] := _ in _).
    {
      intros. exists n; cbn.
      * eapply redtmwf_refl ; gen_typing.
      * now eapply NeFun, tm_ne_whne.
      * eapply tm_nf_conv; [|eassumption].
        now eapply tm_ne_nf.
      * gen_typing.
      * intros; apply helper; [apply ihcod| |..].
        { eapply neu_app_ren; try eassumption.
          now apply (ihdom _ ρ h). }
        1: escape ; now eapply ty_app_ren.
        eapply convneu_app_ren. 1,2: eassumption.
        eapply LREqTermRefl_ in ha.
        now escape.
      * intros. apply ihcod.
        + eapply neu_app_ren; try eassumption.
          now apply (ihdom _ ρ h).
        + eapply tm_ne_conv.
          - eapply neu_app_ren; try eassumption.
            now apply (ihdom _ ρ h).
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
        now eapply (ihdom _ ρ).
      + eapply neu_app_ren; try eassumption.
        now eapply (ihdom _ ρ).
      + apply escapeTerm in ha; now eapply ty_app_ren.
      + apply escapeTerm in ha; now eapply ty_app_ren.
      + eapply convneu_app_ren. 1,2: eassumption.
      eapply escapeEqTerm; eapply LREqTermRefl_; eassumption.
  - do 2 match goal with [ H : _ |- _ ] => revert H end.
    intros ihdom ihcodom a [a' Hr Ha].
    destruct h0 as [na dom codom]; simpl in *.
    assert ([Γ |- tProd na dom codom ≅ A ]) by gen_typing.
    eapply tm_nf_conv; [|eassumption].
    eapply tm_nf_red; [now apply tmr_wf_red|].
    assumption.
Qed.

Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  Ne[Γ |- n : A] ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
Proof.
  intros.  now eapply neuTerm_aux.
Qed.

Lemma neuTermEq {l Γ A} (RA : [Γ ||-<l> A]) {n n'} :
  Ne[Γ |- n : A] ->
  Ne[Γ |- n' : A] ->
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
  - now eapply tm_ne_rel.
  - eapply convneu_var; tea.
Qed.

Lemma reifyTerm {l Γ A} (RA : [Γ ||-<l> A]) {t} : [Γ ||-<l> t : A | RA] -> Nf[Γ |- t : A].
Proof.
intros; now eapply neuTerm_aux.
Qed.

Lemma reifyType {l Γ A} (RA : [Γ ||-<l> A]) : Nf[Γ |- A].
Proof.
assert (tΓ : wf_context Γ).
{ eapply wfc_wft, escape; apply RA. }
destruct RA as [RA HRA].
induction HRA.
+ destruct h.
  eapply ty_nf_red, ty_nf_sort; gen_typing.
+ destruct neA.
  eapply ty_nf_red; [|now apply ty_ne_nf].
  gen_typing.
+ do 3 match goal with [ H : _ |- _ ] => revert H end.
  intros IHdom IHcodom tΓ.
  eapply ty_nf_red; [apply tyr_wf_red, ΠA|].
  eapply ty_nf_prod.
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
