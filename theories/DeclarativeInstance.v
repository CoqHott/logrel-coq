From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped UntypedReduction Weakening GenericTyping DeclarativeTyping Generation.

Import DeclarativeTypingData.


Section TypingWk.
  Import DeclarativeTypingData.
  
  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PTm (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].

  Theorem typing_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - intros Γ na A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ _ ρ).
      now constructor.
    - intros * _ IHA ? * ?.
      econstructor.
      now eapply IHA.
    - intros * _ IHΓ Hnth ? * ?.
      eapply typing_meta_conv.
      1: econstructor ; tea.
      1: eapply in_ctx_wk ; tea.
      reflexivity.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ _ ρ).
      econstructor ; tea.
      econstructor.
      now eapply IHA.
    - intros * _ IHA _ IHt ? ρ ?.
      econstructor.
      1: now eapply IHA.
      eapply IHt with (ρ := wk_up _ _ ρ).
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
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ _ ρ).
        econstructor ; tea.
        now eapply IHA.
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
    - intros Γ ? u t A B _ IHA _ IHt _ IHu ? ρ ?.
      cbn.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHA.
      + eapply IHt with (ρ := wk_up _ _ ρ).
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + now asimpl.
      + now asimpl. 
    - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ _ ρ).
        pose (IHA _ ρ H).
        econstructor; tea; now econstructor.
    - intros Γ ? u u' f f' A B _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + now asimpl.
      + now asimpl.
    - intros Γ ? ? f f' A B _ IHA _ IHf _ IHg _ IHe ? ρ ?.
      cbn.
      econstructor.
      1-3: easy.
      specialize (IHe _ (wk_up _ _ ρ)).
      cbn in IHe.
      bsimpl.
      repeat rewrite renRen_term in IHe.
      cbn in * ; refold.
      eapply IHe.
      econstructor ; tea.
      now eapply IHA.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?.
      now econstructor.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
  Qed.

  Corollary typing_shift : WfDeclInductionConcl
    (fun _ => True)
    (fun (Γ : context) (A : term) => forall nt T, [|- Γ] -> [Γ |- T] -> [Γ,, vass nt T |- A⟨↑⟩])
    (fun (Γ : context) (A t : term) => forall nt T, [|- Γ] -> [Γ |- T] -> [Γ,, vass nt T |- t⟨↑⟩ : A⟨↑⟩])
    (fun (Γ : context) (A B : term) => forall nt T, [|- Γ] -> [Γ |- T] -> [Γ,, vass nt T |- A⟨↑⟩ ≅ B⟨↑⟩])
    (fun (Γ : context) (A t u : term) => forall nt T, [|- Γ] -> [Γ |- T] -> [Γ,, vass nt T |- t⟨↑⟩ ≅ u⟨↑⟩ : A⟨↑⟩]).
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    1: now constructor.
    all: intros Γ * Hty nt T HΓ HA.
    all: eapply typing_wk in Hty.
    all: specialize (Hty _ (@wk1 Γ nt T)).
    all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ nt T)) ; refold.
    all: eapply Hty.
    all: now econstructor.
  Qed.

  Corollary typing_eta (Γ : context) na A B f :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ,, vass na A |- B] ->
    [Γ |- f : tProd na A B] ->
    [Γ,, vass na A |- eta_expand f : B].
  Proof.
    intros ? ? ? Hf.
    eapply typing_shift in Hf ; tea.
    eapply typing_meta_conv.
    1: econstructor.
    - cbn in Hf.
      now eassumption.
    - eapply typing_meta_conv.
      1: now do 2 econstructor.
      now reflexivity.
    - asimpl.
      rewrite scons_eta'.
      now asimpl.
    Qed.

End TypingWk.

Section WfContext.
  Import DeclarativeTypingData.

  Definition boundary_ctx_ctx {Γ na A} : [|- Γ,, vass na A] -> [|- Γ].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_ctx_tip {Γ na A} : [|- Γ,, vass na A] -> [Γ |- A].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_tm_ctx {Γ} {t A} :
      [ Γ |- t : A ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ctx_ctx.
  Qed.

  Definition boundary_ty_ctx {Γ} {A} :
      [ Γ |- A ] -> 
      [ |- Γ ].
  Proof.
    induction 1; now eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_tm_conv_ctx {Γ} {t u A} :
      [ Γ |- t ≅ u : A ] -> 
      [ |- Γ ].
  Proof.
      induction 1 ; now eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_ty_conv_ctx {Γ} {A B} :
      [ Γ |- A ≅ B ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ty_ctx, boundary_tm_conv_ctx.
  Qed.

  Definition boundary_ored_tm_l {Γ t u A} : 
    [ Γ |- t ⇒ u : A] ->
    [ Γ |- t : A ].
  Proof.
    induction 1.
    all: econstructor ; eauto.
    now econstructor.
  Qed.

  Definition boundary_ored_ty_l {Γ A B} : 
    [ Γ |- A ⇒ B ] ->
    [ Γ |- A ].
  Proof.
    destruct 1.
    econstructor.
    now eapply boundary_ored_tm_l.
  Qed.

  Definition boundary_red_tm_l {Γ t u A} : 
    [ Γ |- t ⇒* u : A] ->
    [ Γ |- t : A ].
  Proof.
    induction 1 ; eauto using boundary_ored_tm_l.
  Qed.

  Definition boundary_red_ty_l {Γ A B} : 
    [ Γ |- A ⇒* B ] ->
    [ Γ |- A ].
  Proof.
    induction 1 ; eauto using boundary_ored_ty_l.
  Qed.

End WfContext.

#[export] Hint Resolve
  boundary_ctx_ctx boundary_ctx_tip boundary_tm_ctx
  boundary_ty_ctx boundary_tm_conv_ctx boundary_ty_conv_ctx
  boundary_ored_tm_l boundary_ored_ty_l boundary_red_tm_l
  boundary_red_ty_l : boundary.


(** Inclusion of the various reduction-like *)

Definition RedConvTe {Γ} {t u A : term} :
    [Γ |- t ⇒ u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
    induction 1.
    1,3: now econstructor.
    econstructor ; eauto.
    now econstructor.
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⇒* u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
  induction 1.
  - now constructor.
  - now eapply RedConvTe.
  - now eapply TermTrans.
Qed.

Definition RedConvTy {Γ} {A B : term} :
    [Γ |- A ⇒ B] -> 
    [Γ |- A ≅ B].
Proof.
  destruct 1.
  now econstructor ; eapply RedConvTe.
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⇒* B] -> 
    [Γ |- A ≅ B].
Proof.
  induction 1.
  - now constructor.
  - now eapply RedConvTy.
  - now eapply TypeTrans.
Qed.

Lemma oredtm_meta_conv (Γ : context) (t u u' A A' : term) :
  [Γ |- t ⇒ u : A] ->
  A' = A ->
  u' = u ->
  [Γ |- t ⇒ u' : A'].
Proof.
  now intros ? -> ->.
Qed.

(* Weakenings *)

Lemma oredtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
[|- Δ ] -> [Γ |- t ⇒ u : A] -> [Δ |- t⟨ρ⟩ ⇒ u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros ? red.
  induction red as [? ? ? ? ? ? Ht Ha | |]; refold.
  - cbn in *.
    eapply oredtm_meta_conv.
    1: econstructor.
    + now eapply typing_wk.
    + eapply typing_wk with (ρ := wk_up _ _ ρ) ; tea.
      econstructor ; tea.
      now eapply typing_wk.
    + now eapply typing_wk.
    + now asimpl.
    + now asimpl. 
  - cbn in *.
    eapply oredtm_meta_conv.
    1: econstructor.
    + now eauto.
    + now eapply typing_wk.
    + now asimpl.
    + reflexivity.
  - econstructor.
    1: eassumption.
    now eapply typing_wk.
Qed.

Lemma redtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⇒* u : A] -> [Δ |- t⟨ρ⟩ ⇒* u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros * ?.
  induction 1.
  - econstructor ; now apply typing_wk.
  - econstructor ; now eapply oredtmdecl_wk.
  - now econstructor.
Qed.

Lemma oredtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⇒ B] -> [Δ |- A⟨ρ⟩ ⇒ B⟨ρ⟩].
Proof.
  intros ? red.
  destruct red.
  constructor.
  change U with (U⟨ρ⟩).
  now apply oredtmdecl_wk.
Qed.

Lemma redtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⇒* B] -> [Δ |- A⟨ρ⟩ ⇒* B⟨ρ⟩].
Proof.
  intros * ?.
  induction 1.
  - now econstructor ; apply typing_wk.
  - now econstructor ; eapply oredtydecl_wk.
  - now econstructor.
Qed.

(* Type erasure *)

Lemma oredtmdecl_ored Γ t u A : 
  [Γ |- t ⇒ u : A] ->
  [t ⇒ u].
Proof.
  induction 1.
  1-2: now econstructor.
  eassumption.
Qed.

Lemma redtmdecl_red Γ t u A : 
  [Γ |- t ⇒* u : A] ->
  [t ⇒* u].
Proof.
  induction 1.
  - now econstructor.
  - econstructor ; eauto using oredtmdecl_ored.
    reflexivity.
  - now etransitivity.
Qed.

Lemma oredtydecl_ored Γ A B : 
  [Γ |- A ⇒ B] ->
  [A ⇒ B].
Proof.
  induction 1.
  now eapply oredtmdecl_ored.
Qed.

Lemma redtydecl_red Γ A B : 
  [Γ |- A ⇒* B] ->
  [A ⇒* B].
Proof.
  induction 1.
  - now econstructor.
  - econstructor ; eauto using oredtydecl_ored.
    reflexivity.
  - now etransitivity.
Qed.

(* Lifting rules from ⇒ to ⇒* *)

Lemma redtmdecl_app Γ na A B f f' t :
  [ Γ |- f ⇒* f' : tProd na A B ] ->
  [ Γ |- t : A ] ->
  [ Γ |- tApp f t ⇒* tApp f' t : B[t..] ].
Proof.
  intros Hf ?.
  remember (tProd na A B) as T in *.
  induction Hf.
  + subst.
    now do 2 econstructor.
  + subst.
    now do 2 econstructor.
  + now econstructor.
Qed.

Lemma redtmdecl_conv Γ t u A A' : 
  [Γ |- t ⇒* u : A] ->
  [Γ |- A ≅ A'] ->
  [Γ |- t ⇒* u : A'].
Proof.
  intros Ht ?.
  induction Ht.
  + now do 2 econstructor.
  + now do 2 econstructor.
  + now econstructor.
Qed.

Lemma redtydecl_term Γ A B :
  [ Γ |- A ⇒* B : U] -> [Γ |- A ⇒* B ].
Proof.
  remember U as T.
  induction 1 ; subst.
  + now do 2 econstructor.
  + now do 2 econstructor.
  + now econstructor.
Qed.

#[export] Instance RedTermTrans Γ A : Transitive (red_tm Γ A).
Proof.
  now econstructor.
Qed.

#[export] Instance RedTypeTrans Γ : Transitive (red_ty Γ).
Proof.
  now econstructor.
Qed.

Module DeclarativeTypingProperties.
  Export DeclarativeTypingData.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: boundary. 
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    3-5: now econstructor.
    - intros.
      now eapply typing_wk.
    - easy.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    - intros.
      now eapply typing_wk.
    - easy. 
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
    - intros.
      now econstructor.
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
  - easy.
  - intros.
    econstructor.
    2: now eapply TypeSym, RedConvTyC.
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros. eassumption.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
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
  Qed.
  
  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - easy. 
  - intros.
    now eapply redtmdecl_red.
  - intros.
    now do 2 econstructor.
  - intros.
    now eapply redtmdecl_app.
  - intros.
    now eapply redtmdecl_conv.
  - intros.
    now econstructor.
  Qed. 

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtydecl_wk.
  - easy.
  - intros.
    now eapply redtydecl_red.
  - intros.
    now eapply redtydecl_term.
  - intros.
    now econstructor.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.