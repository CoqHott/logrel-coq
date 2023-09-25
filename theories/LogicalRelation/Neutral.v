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
  * eapply convtm_conv; [|tea].
    now apply convtm_convneu.
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
  unshelve refine ( let funred : forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Π n : A | ΠA] := _ in _).
  {
    intros. exists n; cbn.
    * eapply redtmwf_refl ; gen_typing.
    * constructor; now eapply convneu_conv.
    * eapply convtm_conv; [|eassumption].
      now apply convtm_convneu.
    * intros; apply complete_reflect_simpl; [apply ihcod| |..].
      1: escape ; now eapply ty_app_ren.
      eapply convneu_app_ren. 1,2: eassumption.
      eapply reflLRTmEq in ha.
      now escape.
    * intros. apply ihcod.
      + apply escapeTerm in ha; now eapply ty_app_ren.
      + escape; eapply ty_conv.
        1: now eapply ty_app_ren.
        symmetry; unshelve eapply escapeEq, PolyRed.posExt; cycle 2; tea.
      + apply escapeEqTerm in eq0; now eapply convneu_app_ren.
  }
  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  split. 1: now apply funred.
  unshelve econstructor.
  1,2: now apply funred.
  all: cbn; clear funred.
  * gen_typing.
  * intros. apply ihcod; cbn.
    + apply escapeTerm in ha; now eapply ty_app_ren.
    + apply escapeTerm in ha; now eapply ty_app_ren.
    + eapply convneu_app_ren. 1,2: eassumption.
    eapply escapeEqTerm; eapply reflLRTmEq; eassumption.
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
  intros l Γ A PA ihdom ihcod.
  assert [Γ |- A ≅ PA.(outTy)] by (destruct PA; cbn in *; gen_typing).
  assert [Γ |- PA.(outTy)] by (destruct PA; cbn in *; gen_typing). 
  split.
  - 
    unshelve refine ( let funred : forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Σ n : A | PA] := _ in _).
    1:{
      intros n **.
      assert (hfst : forall Δ (ρ : Δ ≤ Γ) (h : [ |- Δ]), [PolyRedPack.shpRed PA ρ h | Δ ||- tFst n⟨ρ⟩ : _]).
      1:{
        intros; eapply complete_reflect_simpl.
        * eapply ihdom.
        * rewrite wk_fst; eapply ty_wk; tea.
          eapply ty_fst; now eapply ty_conv.
        * rewrite wk_fst; eapply convneu_wk; tea.
          eapply convneu_fst; now eapply convneu_conv.
      }
      exists n hfst.
      + eapply redtmwf_refl; now eapply ty_conv.
      + constructor; now eapply convneu_conv.
      + eapply convtm_convneu; now eapply convneu_conv.
      + intros; irrelevanceRefl.
        eapply complete_reflect_simpl; [unshelve eapply ihcod|..]; tea.
        1: eapply hfst.
        all: rewrite wk_fst; rewrite <- subst_ren_subst_mixed; rewrite wk_snd.
        * eapply ty_wk; tea; eapply ty_snd; now eapply ty_conv.
        * eapply convneu_wk; tea; eapply convneu_snd; now eapply convneu_conv.
    }
    intros.
    unshelve refine (let Rn :[Γ ||-Σ n : A | PA] := _ in _).
    1: eapply funred; tea; now eapply lrefl.
    unshelve refine (let Rn' :[Γ ||-Σ n' : A | PA] := _ in _).
    1: eapply funred; tea; now eapply urefl.
    assert (Rnn' : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
      [PolyRedPack.shpRed PA ρ h | Δ ||- tFst n⟨ρ⟩ ≅ tFst n'⟨ρ⟩ : (ParamRedTyPack.dom PA)⟨ρ⟩]).
    1:{
      intros; cbn; eapply ihdom.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst; now eapply ty_conv.
      * rewrite wk_fst; eapply ty_wk; tea.
        eapply ty_fst; now eapply ty_conv. 
      * do 2 rewrite wk_fst; eapply convneu_wk; tea.
        eapply convneu_fst; now eapply convneu_conv.
    }
    assert (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
      [Δ |- (ParamRedTy.cod PA)[tFst n⟨ρ⟩ .: ρ >> tRel] ≅ (ParamRedTy.cod PA)[tFst n'⟨ρ⟩ .: ρ >> tRel]]).
    {
      intros; eapply escapeEq; unshelve eapply (PolyRed.posExt PA); tea.
      + eapply Rn.
      + eapply Rn'.
      + eapply Rnn'.
    }
    split; tea; eexists Rn Rn'.
    + cbn; eapply convtm_convneu; now eapply convneu_conv.
    + apply Rnn'.
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
    1,4: eapply convtm_convneu.
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
    1,4: eapply convtm_convneu.
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
  1,4: eapply convtm_convneu.
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
