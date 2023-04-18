(** * LogRel.Normalisation: well-typed terms always reduce to a normal form. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction
  GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping.
From LogRel Require Import LogicalRelation UntypedValues Validity Fundamental.
From LogRel.LogicalRelation Require Import Escape Neutral Induction ShapeView Reflexivity.
From LogRel.Substitution Require Import Escape Poly.

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
  well_formed Γ t ->
  Acc cored t.
Proof.
  intros [[] Hty].
  all: eapply typing_nf in Hty as [? [red wh]].
  all: induction red.
  - econstructor.
    intros t' [red].
    exfalso.
    eapply whnf_nored ; tea.
    now gen_typing.
  - econstructor.
    intros t'' [red'].
    now eapply ored_det in red' as <-.
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
      econstructor; eapply (ty_ne_whne ne).
    - intros ? ? ? ΠA IHdom IHcod m n mty Hconv ; cbn in *.
      destruct ΠA  as [????? []]; cbn in *.
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
      eapply LRTyEqRefl_.
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
      * eapply neuTerm; tea.
        2: eapply TermRefl; tea.
        econstructor; apply algo_conv_wh in Hconv; now destruct Hconv.
      * rewrite Sigma.wk_id_shift; now econstructor.
    Unshelve. 2,4: tea. 
  Qed.

End NeutralConversion.