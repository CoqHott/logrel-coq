(** * LogRel.Normalisation: well-typed terms always reduce to a normal form.*)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping.
From LogRel Require Import LogicalRelation UntypedValues Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape Neutral Induction ShapeView.
From LogRel.Substitution Require Import Escape.

Section Normalisation.
  Context `{GenericTypingProperties}.

  Theorem typing_nf : WfDeclInductionConcl
    (fun _ => True)
    (fun Γ A => Nf[Γ |- A])
    (fun Γ A t => Nf[Γ |- t : A])
    (fun Γ A B => Nf[Γ |- A] × Nf[Γ |- B])
    (fun Γ A t u => Nf[Γ |- t : A] × Nf[Γ |- u : A]).
  Proof.
    red.
    prod_splitter.
    all: intros * []%Fundamental.
    - easy.
    - now eapply reifyType, reducibleTy.
    - now eapply reifyTerm, reducibleTm.
    - split.
      all: now eapply reifyType, reducibleTy.
    - split.
      all: now eapply reifyTerm, reducibleTm.
  Qed.

End Normalisation.

Import DeclarativeTypingProperties.

Record cored t t' : Prop := { _ : [t' ⇒ t] }.

Theorem typing_SN Γ t :
  well_typed Γ t ->
  Acc cored t.
Proof.
  intros [? Hty].
  eapply typing_nf in Hty as [? [red wh]].
  induction red.
  - econstructor.
    intros t' [red].
    exfalso.
    now eapply whnf_nored.
  - econstructor.
    intros t'' [red'].
    now eapply ored_det in red' as <-.
Qed.

Section NeutralConversion.
  Import AlgorithmicTypingData.

  Lemma ne_conv_conv : forall (Γ : context) (A m n : term),
    [Γ |-[de] A] ->
    [Γ |-[al] m ~ n ▹ A] ->
    [Γ |-[al] m ≅ n : A].
  Proof.
    intros * Hty.
    pose proof (Hty' := Hty).
    eapply Fundamental in Hty' as [? Hfund%reducibleTy].
    revert m n.
    pose (P := (fun Γ A _ _ _ _ => 
      forall m n, [Γ |-[ al ] m ~ n ▹ A] -> [Γ |-[ al ] m ≅ n : A]) :
      forall Γ A rEq rTe rTeEq, LR (LogRelRec one) Γ A rEq rTe rTeEq  -> Type).
    change (P Γ A Hfund.(LRPack.eqTy) Hfund.(LRPack.redTm) Hfund.(LRPack.eqTm) Hfund.(LRAd.adequate)).
    apply LR_rect.
    all: subst P ; cbn.
    - intros.
      econstructor.
      1: eapply redty_red; now destruct h as [??? [??]].
      1-2: reflexivity.
      econstructor. 
      2: now constructor.
      eassumption.
    - intros * [] ?.
      econstructor.
      1: gen_typing.
      1-2: reflexivity.
      econstructor.
      1: eassumption.
      econstructor; eapply (ty_ne_whne ne).
    - intros ? ? ΠAd ΠAad IHdom IHcod m n Hconv ; cbn in *.
      rewrite <- (PiRedTyPack.pack_beta ΠAd ΠAad) in *.
      remember (PiRedTyPack.pack ΠAd ΠAad) as ΠA in *.
      clear ΠAd ΠAad HeqΠA.
      destruct ΠA ; cbn in *.
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
      + eapply neuTerm.
        1: econstructor; reflexivity.
        2: constructor.
        all: eapply typing_meta_conv.
        1,3: now do 2 econstructor ; tea ; boundary.
        all: now bsimpl.
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
  - intros Δ B NB **; destruct NB.
    econstructor.
    + now eapply redtywf_red.
    + reflexivity.
    + reflexivity.
    + econstructor; [eassumption|constructor].
  - intros Δ B NB **; destruct NB.
    econstructor.
    + now eapply redtywf_red.
    + reflexivity.
    + reflexivity.
    + econstructor; [eassumption|constructor].
Qed.

End NeutralConversion.