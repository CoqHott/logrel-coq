From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Irrelevance Escape.

Set Universe Polymorphism.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A} : whne A -> [Γ |- A] -> [ Γ |- A ~ A : U] -> [Γ ||-<l> A].
Proof.
  intros neA wtyA reflA. apply LRne_. 
  exists A; [gen_typing|..]; assumption.
Defined.

Lemma neU {l Γ A n} (h : [Γ ||-U<l> A]) : 
  whne n ->
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
  whne A -> whne B ->
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
  forall n n',
  whne n ->
  whne n' ->
  [Γ |- n : A] ->
  [Γ |- n' : A] ->
  [Γ |- n ~ n' : A] ->
  [Γ ||-<l> n : A | RA] × [Γ ||-<l> n ≅ n' : A| RA].
Proof.
  pattern l, Γ, A, RA; set (P := fun _ => _).
  assert (helper : forall l Γ A RA, P l Γ A RA -> forall n, whne n -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-<l> n : A | RA]).
  { intros ???? ih **; subst P; eapply ih. 5: eassumption. all: assumption. }
  eapply LR_rect_TyUr; clear l Γ A RA; subst P; cbn.
  - intros ??? h0 ?? ???? h; pose proof (lrefl h); pose proof (urefl h).
    assert [Γ |- A ≅ U] by (destruct h0; gen_typing); split.
    2: unshelve econstructor. 
    1-3: now apply neU.
    + eapply RedTyRecBwd; apply neu ; try assumption; gen_typing.
    + cbn. gen_typing.
    + eapply RedTyRecBwd; apply neu; try assumption; gen_typing.
    + eapply TyEqRecBwd. eapply neuEq; try assumption; gen_typing.
  - intros ??? [B []] ** ; assert ([Γ |- A ≅ B]) by gen_typing ; split.
    + exists n; cbn.
      * eapply redtmwf_refl ; gen_typing.
      * assumption.
      * eapply lrefl; eapply convneu_conv; eassumption.
    + exists n n'; cbn.
      1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
      1,2: assumption.
      gen_typing. 
  - intros ??? ΠA0 * ihdom ihcod. set (ΠA := ΠA0); destruct ΠA0 as [na dom cod []].
    assert [Γ |- A ≅ tProd na dom cod] by gen_typing.
    unshelve refine ( let funred : forall n, whne n -> [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-Π n : A | PiRedTyPack.toPiRedTy ΠA] := _ in _).
    {
      intros; exists n; cbn.
      * eapply redtmwf_refl ; gen_typing.
      * now eapply NeFun.
      * gen_typing.
      * intros; apply helper; [apply ihcod| constructor; now apply whne_ren|..].
        1: apply escapeTerm_ in ha; now eapply ty_app_ren. 
        eapply convneu_app_ren. 1,2: eassumption.
        eapply escapeEqTerm_; eapply LREqTermRefl_; eassumption.
      * intros. apply ihcod. 
        1,2: constructor; now apply whne_ren.
        1: apply escapeTerm_ in ha; now eapply ty_app_ren. 
        2: apply escapeEqTerm_ in eq0; now eapply convneu_app_ren.
        pose proof (cv := escapeEq_ _ (codExt _ _ _ ρ _ ha hb eq0)).
        symmetry in cv; unshelve eapply (ty_conv _ cv).
        apply escapeTerm_ in hb; now eapply ty_app_ren.
    }
    intros ?????? h.
    pose proof (lrefl h); pose proof (urefl h).
    split. 1: now apply funred.
    unshelve econstructor.
    1,2: now apply funred.
    all: cbn; clear funred.
    * gen_typing.
    * intros. apply ihcod; cbn.
      1,2: constructor; now apply whne_ren.
      1,2: apply escapeTerm_ in ha; now eapply ty_app_ren.
      eapply convneu_app_ren. 1,2: eassumption.
      eapply escapeEqTerm_; eapply LREqTermRefl_; eassumption.
Qed.


Lemma neuTerm {l Γ A} (RA : [Γ ||-<l> A]) {n} :
  whne n ->
  [Γ |- n : A] ->
  [Γ |- n ~ n : A] ->
  [Γ ||-<l> n : A | RA].
Proof.
  intros.  now eapply neuTerm_aux.
Qed.

Lemma neuTermEq {l Γ A} (RA : [Γ ||-<l> A]) {n n'} :
  whne n ->
  whne n' ->
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
  eapply neuTerm; tea ; constructor + eapply convneu_var; tea.
Qed.

End Neutral.
