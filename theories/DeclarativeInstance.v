(** * LogRel.DeclarativeInstance: proof that declarative typing is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms UntypedReduction UntypedValues Weakening GenericTyping DeclarativeTyping.

Import DeclarativeTypingData.

(** ** Generation *)

(** The generation lemma (the name comes from the PTS literature), gives a 
stronger inversion principle on typing derivations, that give direct access
to the last non-conversion rule, and bundle together all conversions.

Note that because we do not yet know that [Γ |- t : T] implies [Γ |- T],
we cannot use reflexivity in the case where the last rule was not a conversion
one, and we get the slightly clumsy disjunction of either an equality or a
conversion proof. We get a better version of generation later on, once we have
this implication. *)

Definition termGenData l (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl, [|- Γ]< l > & in_ctx Γ n decl]
    | tProd A B =>  [× T = U, [Γ |- A : U]< l > & [Γ,, A |- B : U]< l >]
    | tLambda A t => ∑ B, [× T = tProd A B, [Γ |- A]< l > & [Γ,, A |- t : B]< l >]
    | tApp f a => ∑ A B, [× T = B[a..], [Γ |- f : tProd A B]< l > & [Γ |- a : A]< l >]
    | tSort _ => False
    | tNat => T = U
    | tZero => T = tNat
    | tSucc n => T = tNat × [Γ |- n : tNat]< l >
    | tNatElim P hz hs n =>
      [× T = P[n..], [Γ,, tNat |- P]< l >, [Γ |- hz : P[tZero..]]< l >, [Γ |- hs : elimSuccHypTy P]< l > & [Γ |- n : tNat]< l >]
    | tBool => T = U
    | tTrue => T = tBool
    | tFalse => T = tBool
    | tAlpha n => T = tBool × [Γ |- n : tNat]< l >
    | tBoolElim P ht hf b =>
      [× T = P[b..], [Γ,, tBool |- P]< l >, [Γ |- ht : P[tTrue..]]< l >, [Γ |- hf : P[tFalse..]]< l > & [Γ |- b : tBool]< l >]
    | tEmpty => T = U
    | tEmptyElim P e =>
      [× T = P[e..], [Γ,, tEmpty |- P]< l > & [Γ |- e : tEmpty]< l >]
  end.
(*
Lemma termGen l Γ t A :
  [Γ |- t : A]< l > ->
  ∑ A', (termGenData l Γ t A') × ((A' = A) + [Γ |- A' ≅ A]< l >).
Proof.
  induction 1.
  all: try (eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter).
  + destruct IHTypingDecl as [? [? [-> | ]]].
    * prod_splitter; tea; now right.
    * prod_splitter; tea; right; now eapply TypeTrans.
  + 
Qed.

Lemma prod_ty_inv l Γ A B :
  [Γ |- tProd A B]< l > ->
  [Γ |- A]< l > × [Γ,, A |- B]< l >.
Proof.
  intros Hty.
  inversion Hty ; subst ; clear Hty.
  1: easy.
  eapply termGen in H as (?&[-> ]&_).
  split ; now econstructor.
Qed.*)

(** ** Stability by weakening *)

Lemma subst_ren_wk_up {Γ Δ P A} {ρ : Γ ≤ Δ}: forall n, P[n..]⟨ρ⟩ = P⟨wk_up A ρ⟩[n⟨ρ⟩..].
Proof. intros; now bsimpl. Qed.

Lemma shift_up_ren {Γ Δ t} (ρ : Δ ≤ Γ) : t⟨ρ⟩⟨↑⟩ = t⟨↑ >> up_ren ρ⟩.
Proof. now asimpl. Qed.

Section TypingWk.
  
  Let PCon (l : wfLCon) (Γ : context) := True.
  Let PTy l (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > -> [Δ |- A⟨ρ⟩]< l >.
  Let PTm l (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩]< l >.
  Let PTyEq l (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]< l >.
  Let PTmEq l (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ]< l > ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]< l >.



  Theorem typing_wk l : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq l.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction ; clear l.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - intros ? ? IH.
      now econstructor.
    - intros ? Γ A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros l' * ? ? ? ? IHA *.
      econstructor.
      now eapply IHA.
    - intros. now econstructor.
    - intros l Γ A n ne HAt IHAt HAf IHAf Δ ρ HΔ.
      eapply ϝwfType.
      + eapply IHAt.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
      + eapply IHAf.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
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
      erewrite subst_ren_wk_up; eapply (wfTermNatElim l).
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros; now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros * ? ihP ? ihht ? ihhf ? ihb **; cbn.
      erewrite subst_ren_wk_up; eapply (wfTermBoolElim l).
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihht.
        now erewrite subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhf.
        now erewrite subst_ren_wk_up.
      * now eapply ihb.
    - intros; now constructor.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up; eapply (wfTermEmptyElim l).
      * eapply ihP; econstructor; tea; now econstructor.
      * now eapply ihe.
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros l Γ t A n ne HAt IHAt HAf IHAf Δ ρ HΔ.
      eapply ϝwfTerm.
      + eapply IHAt.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
      + eapply IHAf.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
    - intros l Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
    - intros * _ IHA ? ρ ?.
      eapply TypeRefl.
      now eapply IHA.
    - intros * _ IH ? ρ ?.
      econstructor.
      now eapply IH.
    - intros l Γ A B n ne HAt IHAt HAf IHAf Δ ρ HΔ.
      eapply ϝTypeConv.
      + eapply IHAt.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
      + eapply IHAf.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
    - intros * _ IH ? ρ ?.
      now econstructor ; eapply IH.
    - intros * _ IHA _ IHB ? ρ ?.
      eapply TypeTrans.
      + now eapply IHA.
      + now eapply IHB.
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
    - intros l Γ f f' A B _ IHA _ IHf _ IHg _ IHe ? ρ ?.
      cbn.
      econstructor.
      1-3: easy.
      specialize (IHe _ (wk_up _ ρ)).
      cbn in IHe.
      repeat rewrite renRen_term in IHe.
      cbn in * ; refold.
      do 2 rewrite shift_up_ren.
      erewrite <- wk_up_ren_on.
      eapply IHe.
      econstructor ; tea.
      now eapply IHA.
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
    - intros * ? ihP ? ihht ? ihhf ? ihb **; cbn.
      erewrite subst_ren_wk_up.
      eapply (TermBoolElimCong l).
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihht.
        2: reflexivity.
        now erewrite subst_ren_wk_up.
      * eapply convtm_meta_conv.
        1: now eapply ihhf.
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
    - intros ; cbn ; now econstructor.
    - intros l Γ n b HΓ _ inl * HΔ.
      cbn ; refold.
      erewrite wk_bool_to_term ; erewrite wk_nat_to_term.
      now econstructor.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up.
      eapply (TermEmptyElimCong l).
      * eapply ihP; constructor; tea; now constructor.
      * now eapply ihe.
    - intros l Γ t u A n ne HAt IHAt HAf IHAf Δ ρ HΔ.
      eapply ϝTermConv.
      + eapply IHAt.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
      + eapply IHAf.
        unshelve eapply (WfContextDecl_trans _ _ HΔ).
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?.
      now econstructor.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
  Qed.

End TypingWk.

(** ** A first set of boundary conditions *)

(** These lemmas assert that various boundary conditions, ie that if a certain typing-like relation
holds, some of its components are themselves well-formed. For instance, if [Γ |- t ⇒* u : A] then
[Γ |- t : A ]. The tactic boundary automates usage of these lemmas. *)

(** We cannot prove yet that all boundaries are well-typed: this needs stability of typing
by substitution and injectivity of type constructors, which we get from the logical relation.*)

Section Boundaries.
  Import DeclarativeTypingData.

  Definition boundary_ctx_ctx {l Γ A} : [|- Γ,, A]< l > -> [|- Γ]< l >.
  Proof.
    remember (Γ,, A) eqn: H.
    induction 1.
    - discriminate.
    - injection H ; intros ; now subst.
    - eapply ϝwfCon.
      + now eapply IHWfContextDecl1. 
      + now eapply IHWfContextDecl2.
  Qed.

  Definition boundary_ctx_tip {l Γ A} : [|- Γ,, A]< l > -> [Γ |- A]< l >.
  Proof.
    remember (Γ,, A) eqn: H.
    induction 1.
    - discriminate.
    - injection H ; intros ; now subst.
    - eapply ϝwfType.
      + now eapply IHWfContextDecl1. 
      + now eapply IHWfContextDecl2.
  Qed.

  Definition boundary_tm_ctx {l Γ} {t A} :
      [ Γ |- t : A ]< l > -> 
      [ |- Γ ]< l >.
  Proof.
    induction 1 ; eauto using boundary_ctx_ctx.
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
    induction 1 ; eauto using boundary_tm_ctx.
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
    [ Γ |- t ⇒* u ∈ K]< l > ->
    match K with istype => [ Γ |- t ]< l > | isterm A => [ Γ |- t : A ]< l > end.
  Proof.
    destruct 1; assumption.
  Qed.

  Definition boundary_red_tm_l {l Γ t u A} : 
    [ Γ |- t ⇒* u : A]< l > ->
    [ Γ |- t : A ]< l >.
  Proof.
    apply @boundary_red_l with (K := isterm A).
  Qed.

  Definition boundary_red_ty_l {l Γ A B} : 
    [ Γ |- A ⇒* B ]< l > ->
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
    [Γ |- t ⇒* u ∈ K]< l > -> 
    match K with istype => [Γ |- t ≅ u]< l > | isterm A => [Γ |- t ≅ u : A]< l > end.
Proof.
apply reddecl_conv.
Qed.

Definition RedConvTeC {l Γ} {t u A : term} :
    [Γ |- t ⇒* u : A]< l > -> 
    [Γ |- t ≅ u : A]< l >.
Proof.
apply @RedConvC with (K := isterm A).
Qed.



Definition RedConvTyC {l Γ} {A B : term} :
    [Γ |- A ⇒* B]< l > -> 
    [Γ |- A ≅ B]< l >.
Proof.
apply @RedConvC with (K := istype).
Qed.

(** ** Weakenings of reduction *)

Lemma redtmdecl_wk {l Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ]< l > -> [Γ |- t ⇒* u : A]< l > -> [Δ |- t⟨ρ⟩ ⇒* u⟨ρ⟩ : A⟨ρ⟩]< l >.
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_wk.
  - now apply typing_wk.
Qed.

Lemma redtydecl_wk {l Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ]< l > -> [Γ |- A ⇒* B]< l > -> [Δ |- A⟨ρ⟩ ⇒* B⟨ρ⟩]< l >.
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_wk.
  - now apply typing_wk.
Qed.

(** ** Derived rules for multi-step reduction *)

Lemma redtmdecl_app l Γ A B f f' t :
  [ Γ |- f ⇒* f' : tProd A B ]< l > ->
  [ Γ |- t : A ]< l > ->
  [ Γ |- tApp f t ⇒* tApp f' t : B[t..] ]< l >.
Proof.
  intros [] ?; split.
  + now econstructor.
  + now apply redalg_app.
  + econstructor; [tea|now apply TermRefl].
Qed.

Lemma redtmdecl_conv l Γ t u A A' : 
  [Γ |- t ⇒* u : A]< l > ->
  [Γ |- A ≅ A']< l > ->
  [Γ |- t ⇒* u : A']< l >.
Proof.
  intros [] ?; split.
  + now econstructor.
  + assumption.
  + now econstructor.
Qed.

Lemma redtydecl_term l Γ A B :
  [ Γ |- A ⇒* B : U]< l > -> [Γ |- A ⇒* B ]< l >.
Proof.
  intros []; split.
  + now constructor.
  + assumption.
  + now constructor.
Qed.

#[export] Instance RedTermTrans l Γ A : Transitive (red_tm l Γ A).
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
  Export DeclarativeTypingData UntypedValues.WeakValuesProperties.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: try boundary.
    intros ; now eapply ϝwfCon.
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    all: try now econstructor.
    - intros.
      now eapply typing_wk.
    - easy.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    all: try (intros; now econstructor).
    - intros.
      now eapply typing_wk.
    - easy. 
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - easy.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - intros.
    now eapply ϝTypeConv.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  1:{ intros.
    constructor ; red ; intros.
    all: now econstructor. }
  all: intros ; try now econstructor.
  1: intros; now eapply typing_wk.
  1: easy.
  1: { intros.
    eapply TermConv.
    2: now eapply TypeSym, RedConvTyC.
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC. }
  intros ;  eassumption.
  all : try now do 2 econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - easy.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - now econstructor.
  - now econstructor.
  - econstructor.
    induction n ; now econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - intros; now eapply redtmdecl_red.
  - intros. now eapply boundary_red_tm_l.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redSuccAlg; [constructor|reflexivity].
    + now constructor.
  - intros; split.
    + (econstructor; tea) ; econstructor.
      now eapply boundary_tm_ctx.
    + eapply redSuccAlg; [constructor|reflexivity].
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redSuccAlg; [constructor|reflexivity].
    + now constructor.
  - intros; now eapply redtmdecl_app.
  - intros ??????????? []?; split.
    + repeat (constructor; tea).
    + now eapply redalg_natElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros ??????? []?; split.
    + repeat (constructor; tea).
    + now eapply redalg_natEmpty.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros; now eapply redtmdecl_conv.
  - intros; split.
    + assumption.
    + reflexivity.
    + now econstructor.
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
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.
