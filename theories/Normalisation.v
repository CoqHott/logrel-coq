(** * LogRel.Normalisation: well-typed terms always reduce to a normal form. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping.
From LogRel Require Import LogicalRelation UntypedValues Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape Neutral Induction ShapeView Reflexivity.
From LogRel.Substitution Require Import Escape Poly.

Record WN (t : term) := {
  wn_val : term;
  wn_red : [ t ⇒* wn_val ];
  wn_whnf : whnf wn_val;
}.

Lemma WN_wk : forall t (ρ : nat -> nat), WN t -> WN t⟨ρ⟩.
Proof.
intros * [r].
exists r⟨ρ⟩.
+ now apply credalg_wk.
+ now apply whnf_ren.
Qed.

Lemma WN_exp : forall t u, [t ⇒* u] -> WN u -> WN t.
Proof.
intros t u ? [r].
exists r; tea.
now etransitivity.
Qed.

Lemma WN_whnf : forall t, whnf t -> WN t.
Proof.
intros; exists t; tea.
reflexivity.
Qed.

Lemma WN_isFun : forall t, isFun t -> WN t.
Proof.
intros t []; apply WN_whnf; now constructor.
Qed.

Lemma WN_isPair : forall t, isPair t -> WN t.
Proof.
intros t []; apply WN_whnf; now constructor.
Qed.

Module Nf.

Definition nf := de.

#[export] Instance WfContextNf : WfContext nf := fun Γ => True.
#[export] Instance WfTypeNf : WfType nf := fun Γ A => True.
#[export] Instance TypingNf : Typing nf := fun Γ A t => True.
#[export] Instance ConvTypeNf : ConvType nf := fun Γ A B => WN A × WN B.
#[export] Instance ConvTermNf : ConvTerm nf := fun Γ A t u => WN t × WN u.
#[export] Instance ConvNeuConvNf : ConvNeuConv nf := fun Γ A m n => whne m × whne n.
#[export] Instance ConvNeuListNf : ConvNeuList nf := fun Γ A m n => whne_list m × whne_list n.
#[export] Instance RedTypeNf : RedType nf := fun Γ A B => [A ⇒* B].
#[export] Instance RedTermNf : RedTerm nf := fun Γ A t u => [t ⇒* u].

#[export, refine] Instance WfCtxNfProperties : WfContextProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance WfTypeNfProperties : WfTypeProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance TypingNfProperties : TypingProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance ConvTypeNfProperties : ConvTypeProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros * []; now split.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? []; split; now eapply WN_exp.
Qed.

#[export, refine] Instance ConvTermNfProperties : ConvTermProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? ? []; split; now eapply WN_exp.
+ intros * ? []; split; now apply WN_whnf, whnf_whne.
+ intros * []; split; now apply WN_whnf, whnf_whne_list. 
+ intros * ? ? ? ? ? ? []; split; now apply WN_isFun.
+ intros; split; now apply WN_isPair.
Qed.

#[export, refine] Instance ConvNeuNfProperties : ConvNeuProperties (ta := nf) := {}.
Proof.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply whne_ren.
+ intros * []; assumption.
+ intros; split; constructor.
+ intros * [] ?; split; now constructor.
+ intros * ? ? ? []; split; now constructor.
+ intros * ? []; split; now constructor.
+ intros * []; split; now constructor.
+ intros * []; split; now constructor.
Qed.


#[export, refine] Instance ConvNeuListNfProperties : ConvNeuListProperties (ta := nf) := {}.
Proof.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply whne_list_ren.
+ intros * []; split; now econstructor.
+ now intros * [].
+ intros * [] ??; now split. 
+ intros * ?????? [] []; split; constructor ; tea ; now constructor.
+ intros * ?????? [] []; split; constructor ; tea ; now constructor.
Qed.

#[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := nf) := {}.
Proof.
all: try now (intros; apply redalg_one_step; constructor).
+ intros; now apply credalg_wk.
+ intros; eassumption.
+ now constructor.
+ intros; now apply redalg_app.
+ intros; now apply redalg_natElim.
+ intros; now apply redalg_natEmpty.
+ intros; now apply redalg_fst.
+ intros; now apply redalg_snd.
+ intros; now apply redalg_map.
+ intros; assumption.
+ intros; reflexivity.
Qed.

#[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := nf) := {}.
Proof.
all: try now intros; eassumption.
+ intros; now apply credalg_wk.
+ constructor.
+ intros; reflexivity.
Qed.

#[export] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ _ := {}.

End Nf.

Section Normalisation.

  Import Nf.

  Theorem typing_nf : WfDeclInductionConcl
    (fun _ => True)
    (fun Γ A => True)
    (fun Γ A t => True)
    (fun Γ A B => WN A × WN B)
    (fun Γ A t u => WN t × WN u).
  Proof.
    red.
    prod_splitter.
    all: intros * H%Fundamental.
    - constructor.
    - constructor.
    - constructor.
    - destruct H as [? ? ? H].
      apply escapeEq in H as []; now split.
    - destruct H as [? ? ? ? H].
      apply escapeTmEq in H as []; now split.
  Qed.

End Normalisation.

Import DeclarativeTypingProperties.

Corollary typing_nf_alt  {Γ t} : well_formed Γ t -> WN  t.
Proof.
  intros [[] Hty].
  all: first [apply TypeRefl in Hty|apply TermRefl in Hty].
  all: now eapply typing_nf in Hty as [? _].
Qed.


Record cored t t' : Prop := { _ : [t' ⇒ t] }.

Theorem typing_SN Γ t :
  well_formed Γ t ->
  Acc cored t.
Proof.
  intros [[] Hty].
  all: first [apply TypeRefl in Hty|apply TermRefl in Hty].
  all: eapply typing_nf in Hty as [? _].
  all: pose proof w as [wh red].
  all: induction red.
  - econstructor.
    intros t' [red].
    exfalso.
    eapply whnf_nored ; tea.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
    eapply WN_exp; [tea|]; now apply WN_whnf.
  - econstructor.
    intros t' [red].
    exfalso.
    now eapply whnf_nored.
  - econstructor.
    intros t'' [red'].
    eapply ored_det in red' as <-; [|exact o].
    apply IHred; tea.
    eapply WN_exp; [tea|]; now apply WN_whnf.
Qed.

Section NeutralConversion.
  Import AlgorithmicTypingData.

  Lemma var0_wk1_id {Γ A t} : t[tRel 0 .: @wk1 Γ A >> tRel] = t.
  Proof. bsimpl. rewrite scons_eta'. now asimpl. Qed.


  Lemma refl_rel_id (Γ : context) (A : term) :
    [Γ,, A |-[al] tRel 0 ≅ tRel 0 : A⟨↑⟩] ->
    [Γ |-[al] idterm A ≅h idterm A : arr A A].
  Proof.
    intros Hconv.
    inversion Hconv ; subst.
    eapply UntypedReduction.red_whnf in H0 as <- , H1 as <-.
    2-3: now do 2 econstructor.
    econstructor.
    1-2: econstructor.
    econstructor ; tea.
    - eapply redalg_one_step.
      econstructor.
    - eapply redalg_one_step.
      econstructor.
  Qed.

  Lemma ne_conv_ne_list_conv : forall (Γ : context) (A m n : term),
    [Γ |-[de] A] ->
    [Γ |-[al] m ~h n ▹ tList A] ->
    [Γ ,, A |-[al] tRel 0 ≅ tRel 0 : A⟨↑⟩] ->
    [Γ |-[al] m ~ n :List A].
  Proof.
    intros * HA Hconv HconvRel.
    assert (((Map.fn (Map.eta A m)) = tRel 0) × (Map.lst (Map.eta A m) = m)) as [em em'].
    {
      eapply algo_conv_wh in Hconv as [[] []].
      all: cbn ; split ; reflexivity.
    }
    assert (((Map.fn (Map.eta A n)) = tRel 0) × (Map.lst (Map.eta A n) = n)) as [en en'].
    {
      eapply algo_conv_wh in Hconv as [[] []].
      all: cbn ; split ; reflexivity.
    }
    econstructor ; tea.
    all: now rewrite ?em, ?em', ?en, ?en'.
  Qed.
  
End NeutralConversion.