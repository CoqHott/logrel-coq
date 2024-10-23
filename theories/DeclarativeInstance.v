(** * LogRel.DeclarativeInstance: proof that declarative typing is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms UntypedReduction Weakening GenericTyping DeclarativeTyping.

Import DeclarativeTypingData.

(** ** Stability by weakening *)

Lemma shift_up_ren {Γ Δ t} (ρ : Δ ≤ Γ) : t⟨ρ⟩⟨↑⟩ = t⟨↑ >> up_ren ρ⟩.
Proof. now asimpl. Qed.

Section TypingWk.
  
  Let PCon (l : wfLCon) (Γ : context) := True.
  Let PTy (l : wfLCon) (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > -> [Δ |- A⟨ρ⟩]< l >.
  Let PTm (l : wfLCon) (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩]< l >.
  Let PTyEq (l : wfLCon) (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]< l >.
  Let PTmEq (l : wfLCon) (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]< l >.



  Theorem typing_wk (l : wfLCon) : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq l.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction ; clear l.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - intros l Γ A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros ??????? ih ** ; rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
    - intros * _ IHA ? * ?.
      econstructor.
      now eapply IHA.
    - intros * Ht Htren Hf Hfren * Hyp.
      eapply ϝwfType ; [eapply Htren | eapply Hfren].
      all: unshelve eapply (WfContextDecl_trans _ _ Hyp).
      all: now eapply LCon_le_step, wfLCon_le_id.
    - intros * _ IHΓ Hnth ? * ?.
      eapply typing_meta_conv.
      1: econstructor ; tea.
      1: eapply in_ctx_wk ; tea.
      reflexivity.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      econstructor ; tea.
      econstructor.
      now eapply IHA.
    - intros * _ IHA _ IHt ? ρ ?.
      econstructor.
      1: now eapply IHA.
      eapply IHt with (ρ := wk_up _ ρ).
      econstructor ; tea.
      now eapply IHA.
    - intros * _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply typing_meta_conv.
      1: econstructor.
      1: now eapply IHf.
      1: now eapply IHu.
      now asimpl.
    - intros; now constructor.
    - intros; now constructor.
    - intros; cbn; econstructor; eauto.
    - intros; cbn; econstructor; eauto.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      unshelve erewrite subst_ren_wk_up ; [exact tNat | ].
      eapply (wfTermNatElim l).
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros; now constructor.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up; eapply (wfTermEmptyElim l).
      * eapply ihP; econstructor; tea; now econstructor.
      * now eapply ihe.
    - intros; now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros * ? ihP ? iht ? ihf ? ihb **; cbn.
      erewrite subst_ren_wk_up; eapply (wfTermBoolElim l).
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply iht.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihf.
        now erewrite subst_ren_wk_up.
      * now eapply ihb.
    - intros ????? ih1 ? ih2 ** ; rewrite <- wk_sig; cbn.
      constructor.
      1: now eapply ih1.
      eapply ih2 ; constructor; eauto.
      now constructor.
    - intros ??????? ihA ? ihB ? iha ? ihb **.
      rewrite <- wk_sig; rewrite <- wk_pair.
      constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up. 
      now eapply ihb.
    - intros; cbn; econstructor; eauto.
    - intros ?????? ih **.
      unshelve erewrite subst_ren_wk_up; tea.
      econstructor; now eapply ih.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
    - intros * _ IHA _ IHx **; rewrite <- wk_Id, <- wk_refl.
      constructor; eauto.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- wk_idElim.
      erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩]< l > by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros * ? iht ? ihf * Hyp.
      eapply ϝwfTerm ; [eapply iht | eapply ihf].
      all: unshelve eapply (WfContextDecl_trans _ _ Hyp).
      all: eapply LCon_le_step ; now eapply wfLCon_le_id.
    - intros l Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
    - intros ??????????? ih **.
      do 2 rewrite <- wk_sig; constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2!wk_Id; constructor; eauto.
    - intros * _ IHA ? ρ ?.
      eapply TypeRefl.
      now eapply IHA.
    - intros * _ IH ? ρ ?.
      econstructor.
      now eapply IH.
    - intros * _ IH ? ρ ?.
      now econstructor ; eapply IH.
    - intros * _ IHA _ IHB ? ρ ?.
      eapply TypeTrans.
      + now eapply IHA.
      + now eapply IHB.
    - intros l Γ A B n ne HAt IHAt HAf IHAf Δ ρ HΔ.
      eapply ϝTypeConv ; [eapply IHAt | eapply IHAf].
      all: unshelve eapply (WfContextDecl_trans _ _ HΔ).
      all: eapply LCon_le_step ; now eapply wfLCon_le_id.
    - intros l Γ u t A B _ IHA _ IHt _ IHu ? ρ ?.
      cbn.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHA.
      + eapply IHt with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + now asimpl.
      + now asimpl. 
    - intros l Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        pose (IHA _ ρ H).
        econstructor; tea; now econstructor.
    - intros l Γ u u' f f' A B _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + now asimpl.
      + now asimpl.
    - intros * _ IHA _ IHA' _ IHA'' _ IHe ? ρ ?.
      cbn; econstructor; try easy.
      apply (IHe _ (wk_up _ ρ)).
      now constructor.
    - intros * _ IHf ? ρ ?.
      cbn.
      rewrite <- shift_upRen.
      now apply TermFunEta, IHf.
    - intros * ? ih **; cbn; constructor; now apply ih.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up.
      eapply (TermNatElimCong l).
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihhz.
        2: reflexivity.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy. 
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihhz ? ihhs **.
      erewrite subst_ren_wk_up.
      eapply (TermNatElimZero l); fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      erewrite subst_ren_wk_up.
      eapply (TermNatElimSucc l); fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up.
      eapply (TermEmptyElimCong l).
      * eapply ihP; constructor; tea; now constructor.
      * now eapply ihe.
    - intros * ? ihP ? iht ? ihf ? ihb **; cbn.
      erewrite subst_ren_wk_up.
      eapply (TermBoolElimCong l).
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply iht.
        2: reflexivity.
        now erewrite subst_ren_wk_up.
      * eapply convtm_meta_conv.
        1: now eapply ihf.
        2: reflexivity.
        now erewrite subst_ren_wk_up.
      * now eapply ihb.
    - intros * ? ihP ? ihht ? ihhf **.
      erewrite subst_ren_wk_up.
      eapply (TermBoolElimTrue l); fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihht.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhf.
        now erewrite subst_ren_wk_up.
    - intros * ? ihP ? ihht ? ihhf **.
      erewrite subst_ren_wk_up.
      eapply (TermBoolElimFalse l); fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihht.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhf.
        now erewrite subst_ren_wk_up.
    - intros * ? ihP * Hyp.
      econstructor.
      now eapply ihP.
    - intros * ? _ Hin * Hyp ; cbn.
      rewrite bool_to_term_ren ; cbn.
      unshelve econstructor; [exact tBool | | ].
      rewrite -> (nat_to_term_ren ρ n) .
      all: econstructor ; eauto.
      econstructor ; eauto.
    - intros * ????? ih ** ; do 2 rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; tea; constructor; eauto.
    - intros * ? ihA₀ ? ihA ? ihA' ? ihB ? ihB' ? iha ? ihb Δ ρ **.
      rewrite <- wk_sig, <- !wk_pair.
      assert [|-[de] Δ,, A⟨ρ⟩]< l > by now constructor.
      constructor; eauto.
      rewrite <- subst_ren_wk_up; now apply ihb.
    - intros * ? ihp Δ ρ **.
      rewrite <- wk_sig, <- wk_pair.
      constructor; rewrite wk_sig; eauto.
    - intros * ? ih **. econstructor; now eapply ih.
    - intros * ??? ihB ** ; rewrite <- wk_fst; rewrite <- wk_pair; constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * ? ih **.
      unshelve erewrite subst_ren_wk_up; tea; cbn.
      econstructor; now eapply ih.
    - intros * ??? ihB **. 
      rewrite <- wk_snd; rewrite <- wk_pair.
      unshelve erewrite subst_ren_wk_up.
      2:constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2! wk_Id; constructor; eauto.
    - intros * _ IHA _ IHx **.
      rewrite <- 2!wk_refl, <- wk_Id; constructor; eauto.
    - intros * _ IHA0 _ IHx0 _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- 2!wk_idElim; erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩]< l > by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHA' _ IHz _ IHAA' _ IHxy _ IHxz **.
      rewrite <- wk_idElim; erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩]< l > by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?.
      now econstructor.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
    - intros l Γ t u A n ne HAt IHAt HAf IHAf Δ ρ HΔ.
      eapply ϝTermConv ; [eapply IHAt | eapply IHAf].
      all: unshelve eapply (WfContextDecl_trans _ _ HΔ).
      all: now eapply LCon_le_step, wfLCon_le_id.
  Qed.

End TypingWk.

(** ** A first set of boundary conditions *)

(** These lemmas assert that various boundary conditions, ie that if a certain typing-like relation
holds, some of its components are themselves well-formed. For instance, if [Γ |- t ⤳* u : A] then
[Γ |- t : A ]. The tactic boundary automates usage of these lemmas. *)

(** We cannot prove yet that all boundaries are well-typed: this needs stability of typing
by substitution and injectivity of type constructors, which we get from the logical relation.*)

Section Boundaries.
  Import DeclarativeTypingData.

  Definition boundary_ctx_ctx {l Γ A} : [|- Γ,, A]< l > -> [|- Γ]< l >.
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_ctx_tip {l Γ A} : [|- Γ,, A]< l > -> [Γ |- A]< l >.
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_tm_ctx {l Γ} {t A} :
      [ Γ |- t : A ]< l > -> 
      [ |- Γ ]< l >.
  Proof.
    induction 1 ; try now eauto using boundary_ctx_ctx.
    eapply ϝwfCon.
    + now eapply IHTypingDecl1. 
    + now eapply IHTypingDecl2.
  Qed.
  
  Definition boundary_ty_ctx {l Γ} {A} :
      [ Γ |- A ]< l > -> 
      [ |- Γ ]< l >.
  Proof.
    induction 1 ; eauto using boundary_tm_ctx.
    eapply ϝwfCon.
    + now eapply IHWfTypeDecl1. 
    + now eapply IHWfTypeDecl2.
  Qed.

  Definition boundary_tm_conv_ctx {l Γ} {t u A} :
      [ Γ |- t ≅ u : A ]< l > -> 
      [ |- Γ ]< l >.
  Proof.
    induction 1 ; eauto using boundary_tm_ctx, boundary_ty_ctx.
    eapply ϝwfCon.
    + now eapply IHConvTermDecl1. 
    + now eapply IHConvTermDecl2.
  Qed.

  Definition boundary_ty_conv_ctx {l Γ} {A B} :
      [ Γ |- A ≅ B ]< l > -> 
      [ |- Γ ]< l >.
  Proof.
    induction 1 ; eauto using  boundary_ty_ctx, boundary_tm_conv_ctx.
    eapply ϝwfCon.
    + now eapply IHConvTypeDecl1. 
    + now eapply IHConvTypeDecl2.
  Qed.

  Definition boundary_red_l {l Γ t u K} : 
    [ Γ |- t ⤳* u ∈ K]< l > ->
    match K with istype => [ Γ |- t ]< l > | isterm A => [ Γ |- t : A ]< l > end.
  Proof.
    destruct 1; assumption.
  Qed.

  Definition boundary_red_tm_l {l Γ t u A} : 
    [ Γ |- t ⤳* u : A]< l > ->
    [ Γ |- t : A ]< l >.
  Proof.
    apply @boundary_red_l with (K := isterm A).
  Qed.

  Definition boundary_red_ty_l {l Γ A B} : 
    [ Γ |- A ⤳* B ]< l > ->
    [ Γ |- A ]< l >.
  Proof.
    apply @boundary_red_l with (K := istype).
  Qed.

End Boundaries.

#[export] Hint Resolve
  boundary_ctx_ctx boundary_ctx_tip boundary_tm_ctx
  boundary_ty_ctx boundary_tm_conv_ctx boundary_ty_conv_ctx
  boundary_red_tm_l
  boundary_red_ty_l : boundary.

(** ** Inclusion of the various reductions in conversion *)

Definition RedConvC {l Γ} {t u : term} {K} :
    [Γ |- t ⤳* u ∈ K]< l > -> 
    match K with istype => [Γ |- t ≅ u]< l > | isterm A => [Γ |- t ≅ u : A]< l > end.
Proof.
apply reddecl_conv.
Qed.

Definition RedConvTeC {l Γ} {t u A : term} :
    [Γ |- t ⤳* u : A]< l > -> 
    [Γ |- t ≅ u : A]< l >.
Proof.
apply @RedConvC with (K := isterm A).
Qed.

Definition RedConvTyC {l Γ} {A B : term} :
    [Γ |- A ⤳* B]< l > -> 
    [Γ |- A ≅ B]< l >.
Proof.
apply @RedConvC with (K := istype).
Qed.

(** ** Weakenings of reduction *)

Lemma redtmdecl_wk {l Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ]< l > -> [Γ |- t ⤳* u : A]< l > -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩]< l >.
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_wk.
  - now apply typing_wk.
Qed.

Lemma redtydecl_wk {l Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ]< l > -> [Γ |- A ⤳* B]< l > -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩]< l >.
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_wk.
  - now apply typing_wk.
Qed.

(** ** Derived rules for multi-step reduction *)

Lemma redtmdecl_app l Γ A B f f' t :
  [ Γ |- f ⤳* f' : tProd A B ]< l > ->
  [ Γ |- t : A ]< l > ->
  [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ]< l >.
Proof.
  intros [] ?; split.
  + now econstructor.
  + now apply redalg_app.
  + econstructor; [tea|now apply TermRefl].
Qed.

Lemma redtmdecl_conv l Γ t u A A' : 
  [Γ |- t ⤳* u : A]< l > ->
  [Γ |- A ≅ A']< l > ->
  [Γ |- t ⤳* u : A']< l >.
Proof.
  intros [] ?; split.
  + now econstructor.
  + assumption.
  + now econstructor.
Qed.

Lemma redtydecl_term l Γ A B :
  [ Γ |- A ⤳* B : U]< l > -> [Γ |- A ⤳* B ]< l >.
Proof.
  intros []; split.
  + now constructor.
  + assumption.
  + now constructor.
Qed.

#[export] Instance RedTermTrans l Γ A : Transitive (red_tm Γ l A).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TermTrans.
Qed.

#[export] Instance RedTypeTrans l Γ : Transitive (red_ty l Γ).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TypeTrans.
Qed.

(** ** Bundling the properties together in an instance *)

Module DeclarativeTypingProperties.
  Export DeclarativeTypingData.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: try now boundary.
    - intros ; now eapply WfContextDecl_trans.
    - intros; now eapply ϝwfCon.
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    all: try now econstructor.
    - intros.
      now eapply typing_wk.
    - intros ; now eapply WfTypeDecl_trans.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    all: try (intros; now econstructor).
    - intros.
      now eapply typing_wk.
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
    - intros ; now eapply TypingDecl_trans.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - intros ; now eapply ConvTypeDecl_trans.
  - intros.
    now eapply ϝTypeConv.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - intros.
    econstructor; [|tea].
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros * ? H; apply H.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - intros.
    eapply TermTrans; [|now eapply TermFunEta].
    eapply TermTrans; [now eapply TermSym, TermFunEta|].
    constructor; tea.
    all: now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - intros.
    eapply TermTrans; [|now constructor].
    eapply TermTrans; [eapply TermSym; now constructor|].
    constructor; tea; now apply TypeRefl.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - intros ; now eapply ConvTermDecl_trans.
  - intros.
    now eapply ϝTermConv.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split; red.
    + intros ?? []; split; tea; now econstructor.
    + intros ??? [] []; split; tea; now econstructor.
  - intros ?????? [] ?; split; tea; now econstructor.
  - intros ???????? []; split.
    + now eapply whne_ren.
    + now eapply whne_ren.
    + now eapply typing_wk.
  - now intros ????? [].
  - intros ????; split; now econstructor.
  - intros ???????? [] ?; split; now econstructor.
  - intros ????????????? []; split; now econstructor.
  - intros ??????? []; split; now econstructor.
  - intros ????????????? []; split; now econstructor.
  - intros ????? [].
    econstructor ; [ | | econstructor].
    all: induction n ; now econstructor.
  - intros ?????? []; split; now econstructor.
  - intros ?????? []; split; now econstructor.
  - intros * ??????? []; split; now econstructor.
  - intros ??????? [].
    econstructor ; eauto.
    now eapply ConvTermDecl_trans.
  - intros ???????[] [].
    econstructor ; eauto.
    now econstructor.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - intros; now eapply redtmdecl_red.
  - intros. now eapply boundary_red_tm_l.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; now eapply redtmdecl_app.
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_boolElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros * Hg Hin ; split.
    + econstructor.
      clear Hin b.
      now induction n ; econstructor ; eauto.
    + eapply redalg_one_step; now constructor.
    + now econstructor.
  - intros * ? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natEmpty.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_fst.
    + now econstructor.
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_snd.
    + now econstructor.
  - intros **; split; refold.
    + econstructor; tea.
      econstructor. 
      1: econstructor; tea; now econstructor.
      econstructor.
      1: now econstructor.
      1,2: econstructor; tea.
      1: now econstructor.
      eapply TermTrans; tea; now econstructor.
    + eapply redalg_one_step; constructor.
    + now econstructor.
  - intros * ????? []; split; refold.
    + now econstructor.
    + now eapply redalg_idElim.
    + econstructor; tea; now (eapply TypeRefl + eapply TermRefl).
  - intros; now eapply redtmdecl_conv.
  - intros; split.
    + assumption.
    + reflexivity.
    + now econstructor.
  - intros * Hinf [] ; split.
    + now eapply TypingDecl_trans.
    + now eapply redalg_Ltrans.
    + now eapply ConvTermDecl_trans.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtydecl_wk.
  - intros; now eapply redtydecl_red.
  - intros. now eapply boundary_red_ty_l.
  - intros.
    now eapply redtydecl_term.
  - intros; split.
    + assumption.
    + reflexivity.
    + now constructor.
  - intros * Hinf [] ; split.
    + now eapply WfTypeDecl_trans.
    + now eapply redalg_Ltrans.
    + now eapply ConvTypeDecl_trans.    
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.
