(** * LogRel.Normalisation: well-typed terms always reduce to a normal form. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance.
From LogRel Require Import LogicalRelation Validity Fundamental AlgorithmicTyping.
From LogRel.LogicalRelation Require Import Escape Neutral Induction ShapeView Reflexivity.
From LogRel.Substitution Require Import Escape Poly.

Record WN (t : term) := {
  wn_val : term;
  wn_red : [ t ⤳* wn_val ];
  wn_whnf : whnf wn_val;
}.

Lemma WN_wk : forall t (ρ : nat -> nat), WN t -> WN t⟨ρ⟩.
Proof.
intros * [r].
exists r⟨ρ⟩.
+ now apply credalg_wk.
+ now apply whnf_ren.
Qed.

Lemma WN_exp : forall t u, [t ⤳* u] -> WN u -> WN t.
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

Definition nf : tag.
Proof.
constructor.
Qed.

#[export] Instance WfContextNf : WfContext nf := fun Γ => True.
#[export] Instance WfTypeNf : WfType nf := fun Γ A => True.
#[export] Instance TypingNf : Typing nf := fun Γ A t => True.
#[export] Instance ConvTypeNf : ConvType nf := fun Γ A B => WN A × WN B.
#[export] Instance ConvTermNf : ConvTerm nf := fun Γ A t u => WN t × WN u.
#[export] Instance ConvNeuConvNf : ConvNeuConv nf := fun Γ A m n => whne m × whne n.
#[export] Instance RedTypeNf : RedType nf := fun Γ A B => [A ⤳* B].
#[export] Instance RedTermNf : RedTerm nf := fun Γ A t u => [t ⤳* u].

#[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance TypingDeclProperties : TypingProperties (ta := nf) := {}.
Proof.
all: try constructor.
Qed.

#[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros * []; now split.
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? []; split; now eapply WN_exp.
Qed.

#[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := nf) := {}.
Proof.
all: try (intros; split; apply WN_whnf; now constructor).
+ intros; split.
  - intros t u []; now split.
  - intros t u v [] []; now split.
+ intros * [] ?; now split.
+ intros * ? []; split; now apply WN_wk.
+ intros * ? ? ? ? ? []; split; now eapply WN_exp.
+ intros * []; split; now apply WN_whnf, whnf_whne.
+ intros * ? ? ? ? ? ? []; split; now eapply WN_isFun, isWfFun_isFun.
+ intros; split; now eapply WN_isPair, isWfPair_isPair.
Qed.

#[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := nf) := {}.
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
+ intros * ??????? []; split; now constructor.
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
+ intros; now eapply redalg_idElim.
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

#[export] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ := {}.

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

  Import DeclarativeTypingData.

  Corollary normalisation {Γ A t} : [Γ |-[de] t : A] -> WN t.
  Proof. now intros ?%TermRefl%typing_nf. Qed.

  Corollary type_normalisation {Γ A} : [Γ |-[de] A] -> WN A.
  Proof. now intros ?%TypeRefl%typing_nf. Qed.

End Normalisation.

Import DeclarativeTypingProperties.

Record cored t t' : Prop := { _ : [t' ⤳ t] }.

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

  Lemma ne_conv_conv : forall (Γ : context) (A m n : term),
    [Γ |-[de] A] ->
    [Γ |-[de] m : A] ->
    [Γ |-[al] m ~ n ▹ A] ->
    [Γ |-[al] m ≅ n : A].
  Proof.
    intros * Hty.
    pose proof (Hty' := Hty).
    eapply Fundamental in Hty' as [? Hfund%reducibleTy].
    revert m n.
    pattern one, Γ, A, Hfund. apply LR_rect_TyUr; clear Γ A Hty VΓ Hfund.
    (* pose (P := (fun Γ A _ _ _ _ => 
      forall m n, [Γ |-[ al ] m ~ n ▹ A] -> [Γ |-[ al ] m ≅ n : A]) :
      forall Γ A rEq rTe rTeEq, LR (LogRelRec one) Γ A rEq rTe rTeEq  -> Type).
    change (P Γ A Hfund.(LRPack.eqTy) Hfund.(LRPack.redTm) Hfund.(LRPack.eqTm) Hfund.(LRAd.adequate)).
    apply LR_rect. *)
    (* all: subst P ; cbn. *)
    - intros.
      econstructor.
      1: eapply redty_red; now destruct h as [??? [??]].
      1-2: reflexivity.
      econstructor. 
      2: now constructor.
      eassumption.
    - intros ? * [] ?.
      econstructor.
      1: gen_typing.
      1-2: reflexivity.
      econstructor.
      1: eassumption.
      econstructor; eapply (convneu_whne eq).
    - intros ? ? ? ΠA IHdom IHcod m n mty Hconv ; cbn in *.
      destruct ΠA  as [?????? []]; cbn in *.
      econstructor.
      1: gen_typing.
      1-2: reflexivity.
      econstructor.
      1-2: econstructor ; now eapply algo_conv_wh in Hconv.
      eapply convtm_meta_conv.
      3: reflexivity.
      1: unshelve eapply IHcod.
      + exact (tRel var_zero).
      + apply wk1.
      + gen_typing.
      + eapply var0; tea ; now bsimpl.
      + econstructor. 1:econstructor.
        * renToWk; erewrite wk_prod; eapply ty_wk.
          1: econstructor; tea; boundary.
          econstructor; tea. gen_typing.
        * rewrite wk1_ren_on; now eapply ty_var0.
        * assert (cod⟨wk_up dom (@wk1 Γ dom)⟩[(tRel 0)..] = cod[tRel 0 .: @wk1 Γ dom >> tRel]) as -> by now bsimpl.
          econstructor. now rewrite var0_wk1_id.
      + eapply convne_meta_conv.
        3: reflexivity.
        1: econstructor.
        * replace (tProd _ _) with ((tProd dom cod)⟨↑⟩) by
            (cbn ; reflexivity).
          eapply algo_conv_shift.
          econstructor ; tea.
          1: now gen_typing.
          econstructor.
        * eapply convtm_meta_conv.
          1: unshelve eapply IHdom.
          -- now eapply wk1.
          -- gen_typing.
          -- rewrite wk1_ren_on; now eapply ty_var0.
          -- eapply convne_meta_conv.
             1: do 2 econstructor.
             2: reflexivity.
             now bsimpl.
          -- now bsimpl.
          -- reflexivity.
        * now bsimpl.
      + bsimpl.
        rewrite scons_eta'.
        now bsimpl.
  - intros _ Δ B NB **; destruct NB.
    econstructor.
    + now eapply redtywf_red.
    + reflexivity.
    + reflexivity.
    + econstructor; [eassumption|constructor].
  - intros _ Δ B NB **; destruct NB.
    econstructor.
    + now eapply redtywf_red.
    + reflexivity.
    + reflexivity.
    + econstructor; [eassumption|constructor].
  - intros ??? ΣA ihdom ihcod m n tym Hconv.
    destruct (polyRedId ΣA); escape.
    assert [|-[de] Γ] by boundary.
    econstructor.
    1: eapply (ParamRedTy.red ΣA).
    1,2: reflexivity.
    assert [Γ |-[de] m : ParamRedTy.outTy ΣA]. 1:{
      econstructor; tea.
      eapply convty_exp. 
      1: eapply (ParamRedTy.red ΣA).
      1: eapply redtywf_refl; eapply (ParamRedTy.red ΣA).
      econstructor; tea;
      eapply LogicalRelation.Escape.escapeEq;
      eapply reflLRTyEq.
    }
    assert [Γ |-[ de ] tFst m : (ParamRedTy.dom ΣA)⟨@wk_id Γ⟩].
    1: rewrite wk_id_ren_on; now econstructor.
    assert [Γ |-[ al ] tFst m ~ tFst n ▹ ParamRedTy.dom ΣA].
    1:{
      do 2 econstructor; tea.
      1: eapply (ParamRedTy.red ΣA).
      constructor.
    }
    econstructor.
    1-2: econstructor ; now eapply algo_conv_wh in Hconv.
    + unshelve epose (r := ihdom _ wk_id _ _ _ _).
      1,4: tea.
      2: rewrite wk_id_ren_on in r; now apply r.
    + unshelve epose (r := ihcod _ (tFst m) wk_id _ _ _ _ _).
      1: tea.
      5: erewrite Sigma.wk_id_shift in r; apply r.
      3: do 2 econstructor; tea.
      3: eapply (ParamRedTy.red ΣA).
      3: constructor.
      * assert (whne m).
        { apply algo_conv_wh in Hconv; now destruct Hconv. }
        eapply neuTerm; tea.
        split; tea; now econstructor.
      * rewrite Sigma.wk_id_shift; now econstructor.
    Unshelve. 2,4: tea.
  - intros ??? [???? red] IH _ m n tym hconv; cbn in *.
    econstructor.
    1: apply red.
    1,2: reflexivity.
    econstructor; tea; constructor.
  Qed.

End NeutralConversion.