From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped UntypedReduction Weakening GenericTyping DeclarativeTyping Generation.

Import DeclarativeTypingData.

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
    1: econstructor ; refold.
    1,3: now eapply typing_wk.
    + unshelve eapply typing_wk in Ht.
      3: now eapply wk_up.
      1: shelve.
      2: now econstructor ; [eassumption | eapply typing_wk].
      now apply Ht.
    + now asimpl.
    + now asimpl. 
  - cbn in *.
    eapply oredtm_meta_conv.
    1: econstructor ; refold.
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
  refold.
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
    all: intros.
    - now eapply WFtype.
    - now eapply WFterm.
    - now eapply WFterm. 
    - now eapply WFEqType.
    - now eapply WFEqTerm.
    - now eapply WFEqType, RedConvTyC.
    - now eapply WFEqTerm, RedConvTeC. 
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    2-4: now econstructor.
    intros.
    now eapply typing_wk.
  Qed.

  #[export, refine] Instance InferringDeclProperties : InferringProperties (ta := de) := {}.
  Proof.
    2-5: intros ;
    repeat match goal with
      | H : [_ |- _ ▹h _ ] |- _ => apply InfRedTy in H
    end ;
    now econstructor.
    - intros.
      now eapply typing_wk.
  Qed.  

  #[export, refine] Instance InferringRedDeclProperties : InferringRedProperties (ta := de) := {}.
  Proof.
    - intros.
      now eapply typing_wk.
    - intros.
      econstructor ; tea.
      now eapply RedConvTyC. 
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    - intros.
      now eapply typing_wk.
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
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  Qed.
  
  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
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
  - intros.
    now eapply redtydecl_red.
  - intros.
    now eapply redtydecl_term.
  - intros.
    now econstructor.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.