From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeTyping DeclarativeInstance Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application Universe SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var.

Set Universe Polymorphism.

Section Empty.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma emptyRed {Γ l} : [|- Γ] -> [Γ ||-<l> tEmpty].
Proof. 
  intros; eapply LREmpty_; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma emptyValid {Γ l} (VΓ : [||-v Γ]) : [Γ ||-v<l> tEmpty | VΓ].
Proof.
  unshelve econstructor; intros.
  + now eapply emptyRed.
  + cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma emptyconvValid {Γ l} (VΓ : [||-v Γ]) (VEmpty : [Γ ||-v<l> tEmpty | VΓ]) : 
  [Γ ||-v<l> tEmpty ≅ tEmpty | VΓ | VEmpty].
Proof.
  constructor; intros.
  enough [Δ ||-<l> tEmpty ≅ tEmpty | emptyRed wfΔ] by irrelevance.
  constructor; cbn; eapply redtywf_refl; gen_typing.
Qed.

(* TODO: also appears in Nat.v, should probably be more central *)
Lemma redUOne {Γ} : [|- Γ] -> [Γ ||-U<one> U].
Proof.
  intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
Defined.

Lemma emptyTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tEmpty : U | LRU_ (redUOne wfΔ)].
Proof.
  econstructor.
  + eapply redtmwf_refl; gen_typing.
  + constructor.
  + now apply tm_nf_empty.
  + gen_typing.
  + now eapply (emptyRed (l:= zero)).
Defined.

Lemma emptyTermValid {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tEmpty : U | VΓ | UValid VΓ].
Proof.
  constructor; intros.
  - eapply emptyTermRed. 
  - eexists (emptyTermRed wfΔ) (emptyTermRed wfΔ) (emptyRed wfΔ); cbn.
    + gen_typing.
    + now eapply (emptyRed (l:=zero)).
    + constructor; eapply redtywf_refl; gen_typing.
Qed.

Lemma red_emptyElimSubst {Γ l P n n'} :
  [|- Γ] ->
  [Γ ,, tEmpty |- P] ->
  [Γ |- n :⇒*: n' : tEmpty ] ->
  forall (RN : [Γ ||-<l> tEmpty]),
  [Γ ||-<l> n' : tEmpty | RN] ->
  (forall t t',
    [Γ ||-<l> t : tEmpty | RN] ->
    [Γ ||-<l> t' : tEmpty | RN] ->
    [Γ ||-<l> t ≅ t' : tEmpty | RN] ->
    [Γ |- P[t..] ≅ P[t'..]]) -> 
  [Γ |- tEmptyElim P n :⇒*: tEmptyElim P n' : P[n..]].
Proof.
    intros hΓ hp red rN rn' congP.
    generalize (tmr_wf_red _ _ _ _ red).
    escape.
    assert ([rN | Γ ||- n : tEmpty]).
    { now eapply redwfSubstTerm. }
    assert ([ Γ |- P[n..] ≅ P[n'..]]).
    { apply congP; [assumption|assumption|].
      now eapply redwfSubstTerm. }
    intros.
    econstructor.
    - eapply ty_conv; [|now symmetry].
      escape; apply ty_emptyElim; tea.
    - apply redtm_emptyelim; tea.
      + now eapply redtm_ty_src.
      + intros u Hu.
        assert ([Γ |-[ ta ] u :⇒*: n' : tEmpty]).
        { now constructor. }
        apply congP; [eassumption| |].
        * eapply redwfSubstTerm; [exact rn'|assumption].
        * now eapply LRTmEqSym, redwfSubstTerm.
Qed.

(* TODO: move *)
Lemma up_single_subst {t σ u} : t[up_term_term σ][u..] = t[u .:  σ].
Proof.  now bsimpl. Qed.

(* TODO: move *)
Lemma up_liftSubst_eq {σ t u} : t[up_term_term σ][u]⇑ = t[u .: ↑ >> up_term_term σ].
Proof.
  bsimpl. eapply ext_term; intros [|n]; cbn.
  1: reflexivity.
  unfold funcomp; now rewrite  rinstInst'_term.
Qed.

(* TODO: move *)
Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Definition emptyElim {Γ A} (P : term) {n} (NA : [Γ ||-Empty A]) (p : EmptyProp Γ n) : term.
Proof.
  destruct p.
  - exact (tEmptyElim P ne).
Defined.

Section EmptyElimRed.
  Context {Γ l P}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Empty tEmpty])
    (RN := LREmpty_ _ NN)
    (RP : [Γ,, tEmpty ||-<l> P])
    (RPpt : forall n, [Γ ||-<l> n : _ | RN] -> [Γ ||-<l> P[n..]])
    (RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]),
      [Γ ||-<l> n' : _ | RN] ->
      [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn]).

  Definition emptyRedElimStmt :=
    (forall n (Rn : [Γ ||-<l> n : _ | RN]), 
      [Γ ||-<l> tEmptyElim P n : _ | RPpt _ Rn ] ×
      [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim P (EmptyRedTm.nf Rn) : _ | RPpt _ Rn]) ×
    (forall n (Nn : EmptyProp Γ n) (Rn : [Γ ||-<l> n : _ | RN]), 
      [Γ ||-<l> tEmptyElim P n : P[n..] | RPpt _ Rn ] ×
      [Γ ||-<l> tEmptyElim P n ≅ emptyElim P NN Nn : _ | RPpt _ Rn]).

  Lemma emptyElimRedAux : emptyRedElimStmt.
  Proof.
    escape.
    apply EmptyRedInduction.
    - intros ? nf red ? nfprop ih.
      assert [Γ ||-<l> nf : _ | RN]. 1:{
        econstructor; tea.
        eapply redtmwf_refl; gen_typing.
      }
      eapply redwfSubstTerm.
      + eapply LRTmRedConv. 
        2: unshelve eapply ih; tea.
        eapply RPext. 
        2: eapply LRTmEqSym.
        1,2: eapply redwfSubstTerm; tea.
      + eapply red_emptyElimSubst; tea.
        intros; eapply escapeEq; now eapply RPext.
    - intros ? [] ?.
      apply reflect.
      + apply completeness.
      + eapply tm_ne_emptyelim; now first [eassumption|eapply reifyType|eapply reifyTerm].
      + eapply tm_ne_emptyelim; now first [eassumption|eapply reifyType|eapply reifyTerm].
      + now eapply ty_emptyElim.
      + now eapply ty_emptyElim.
      + eapply convneu_emptyElim; tea.
        { eapply escapeEq, LRTyEqRefl_. }
    Unshelve.
        1: tea. 2: tea.
  Qed.

  Lemma emptyElimRed : forall n (Rn : [Γ ||-<l> n : _ | RN]), [Γ ||-<l> tEmptyElim P n : _ | RPpt _ Rn ].
  Proof. intros. apply (fst emptyElimRedAux). Qed.
End EmptyElimRed.


Section EmptyElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Empty tEmpty])
    (RN := LREmpty_ _ NN)
    (RP : [Γ,, tEmpty ||-<l> P])
    (RQ : [Γ,, tEmpty ||-<l> Q])
    (eqPQ : [Γ,, tEmpty |- P ≅ Q])
    (RPpt : forall n, [Γ ||-<l> n : _ | RN] -> [Γ ||-<l> P[n..]])
    (RQpt : forall n, [Γ ||-<l> n : _ | RN] -> [Γ ||-<l> Q[n..]])
    (RPQext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]),
      [Γ ||-<l> n' : _ | RN] ->
      [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> P[n..] ≅ Q[n'..] | RPpt _ Rn]).    

  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]),
      [Γ ||-<l> n' : _ | RN] ->
      [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn].
  Proof.
    intros. eapply transEq; [| eapply LRTyEqSym ]; eapply RPQext; cycle 1; tea.
    now eapply LREqTermRefl_.
    Unshelve. 3,4: eauto. tea.
  Qed.

  Lemma emptyElimRedAuxLeft : @emptyRedElimStmt _ _ P NN RPpt.
  Proof.
    eapply emptyElimRedAux; tea.
    + eapply RPext.
  Qed.

  Lemma emptyElimRedAuxRight : @emptyRedElimStmt _ _ Q NN RQpt.
  Proof.
    eapply emptyElimRedAux; tea.
    + intros. eapply transEq; [eapply LRTyEqSym |]; eapply RPQext; cycle 1; tea.
      now eapply LREqTermRefl_.
    Unshelve. 2: eauto. all:tea.
  Qed.

  Lemma emptyElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]) (Rn : [Γ ||-<l> n : _ | RN]) (Rn' : [Γ ||-<l> n' : _ | RN]),
      [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ Rn ]) ×
    (forall n n' (Rnn' : EmptyPropEq Γ n n') (Rn : [Γ ||-<l> n : _ | RN]) (Rn' : [Γ ||-<l> n' : _ | RN]),
      [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ Rn ]).
  Proof.
    apply EmptyRedEqInduction.
    - intros ?? nfL nfR redL redR ? prop ih RL RR; edestruct @EmptyPropEq_whnf; eauto. 
      assert [Γ ||-<l> nfL : _ | RN] by (eapply redTmFwd; cycle 1; tea).
      assert [Γ ||-<l> nfR : _ | RN] by (eapply redTmFwd; cycle 1; tea).
      eapply LREqTermHelper.
      * eapply (fst emptyElimRedAuxLeft).
      * eapply (fst emptyElimRedAuxRight).
      * eapply RPQext. 1: tea.
        now econstructor.
      * eapply LRTmEqRedConv.
        + eapply RPext; tea. 
          eapply LRTmEqSym; eapply redwfSubstTerm; cycle 1; tea.
        + unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ (EmptyRedTm.red RL) redL); tea.
          1: dependent inversion RL; subst; cbn; now eapply EmptyProp_whnf.
          unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ (EmptyRedTm.red RR) redR); tea.
          1: dependent inversion RR; subst; cbn; now eapply EmptyProp_whnf.
          now eapply ih.
        Unshelve. tea. 2, 4: tea. 
    - intros ?? neueq ??. escape. inversion neueq.
      assert [Γ |- P[ne..] ≅ Q[ne'..]]. 1:{
        eapply escapeEq. eapply RPQext; tea.
        econstructor.
        1,2: now eapply redtmwf_refl.
        2: now constructor.
        gen_typing.
      }
      eapply neuTermEq.
      + eapply tm_ne_emptyelim; now first [eassumption|eapply reifyType|eapply reifyTerm].
      + eapply tm_ne_conv; [|symmetry; eassumption].
        eapply tm_ne_emptyelim; now first [eassumption|eapply reifyType|eapply reifyTerm].
      + eapply ty_emptyElim; tea.
      + eapply ty_conv. 
        1: eapply ty_emptyElim; tea.
        now symmetry.
      + eapply convneu_emptyElim ; tea.
      Unshelve. tea.
  Qed.

  Lemma emptyElimRedEq :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]) (Rn : [Γ ||-<l> n : _ | RN]) (Rn' : [Γ ||-<l> n' : _ | RN]), 
      [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPpt _ Rn ]).
  Proof. apply emptyElimRedEqAux. Qed.
End EmptyElimRedEq.



Section EmptyElimValid.
  Context {Γ l P}
    (VΓ : [||-v Γ])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN]).
  

  Lemma emptyElimValid {n}
    (Vn : [Γ ||-v<l> n : tEmpty | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tEmptyElim P n : _ | VΓ | VPn].
  Proof.
    constructor; intros.
    - instValid Vσ; cbn.
      irrelevance0.  1: now rewrite singleSubstComm'.
      epose proof (Vuσ := liftSubstS' VN Vσ).
      instValid Vuσ; escape.
      unshelve eapply emptyElimRed; tea.
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 1; tea.
        unshelve econstructor; [now bsimpl| now cbn].
      + intros m m' Rm Rm' Rmm'; cbn.
        irrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt; cycle 1 ; tea.
        1,2: unshelve econstructor; [now bsimpl| now cbn].
        unshelve econstructor; [|now cbn].
        bsimpl; cbn; eapply reflSubst.
    - instAllValid Vσ Vσ' Vσσ'.
      irrelevance0.  1: now rewrite singleSubstComm'.
      pose (Vuσ := liftSubstS' VN Vσ).
      pose proof (Vuσ' := liftSubstS' VN Vσ').
      pose proof (Vuσrea :=  liftSubstSrealign' VN Vσσ' Vσ').
      pose proof (Vuσσ' := liftSubstSEq' VN Vσσ').
      instValid Vuσ'; instAllValid Vuσ Vuσrea Vuσσ'; escape.
      unshelve eapply emptyElimRedEq; tea; fold subst_term.
      all: try now (irrelevance; now rewrite elimSuccHypTy_subst).
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 1; tea.
        unshelve econstructor; [now bsimpl| now cbn].
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 1; tea.
        unshelve econstructor; [now bsimpl| now cbn].
      + intros m m' Rm Rm' Rmm'; cbn.
        irrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt; cycle 1 ; tea.
        1,2: unshelve econstructor; [now bsimpl| now cbn].
        unshelve econstructor; [|now cbn].
        now bsimpl.
  Qed.

End EmptyElimValid.

Lemma emptyElimCongValid {Γ l P Q n n'}
    (VΓ : [||-v Γ])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN])
    (VQ : [Γ ,, tEmpty ||-v<l> Q | VΓN])
    (VPQ : [Γ ,, tEmpty ||-v<l> P ≅ Q | VΓN | VP])
    (Vn : [Γ ||-v<l> n : _ | VΓ | VN])
    (Vn' : [Γ ||-v<l> n' : _ | VΓ | VN])
    (Veqn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn) :
    [Γ ||-v<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | VΓ | VPn].
Proof.
  constructor; intros.
  pose (Vuσ := liftSubstS' VN Vσ).
  instValid Vσ; instValid Vuσ; escape.
  irrelevance0.  1: now rewrite singleSubstComm'.
  unshelve eapply emptyElimRedEq; tea; fold subst_term.
  all: try (irrelevance; now rewrite elimSuccHypTy_subst).
  + intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 1; tea.
    unshelve econstructor; [now bsimpl| now cbn].
  + intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 1; tea.
    unshelve econstructor; [now bsimpl| now cbn].
  + intros m m' Rm Rm' Rmm'; cbn.
    irrelevance0. 1: now rewrite up_single_subst.
    rewrite up_single_subst.
    eapply transEq; cycle 1.
    - unshelve eapply validTyEq. 
      7: tea. 1: tea.
      unshelve econstructor; [now bsimpl| now cbn].
    - unshelve eapply validTyExt; cycle 1 ; tea.
    1,2: unshelve econstructor; [now bsimpl| now cbn].
    unshelve econstructor; [|now cbn].
    bsimpl. eapply reflSubst.
    Unshelve. 1: tea.
    eapply validTy; tea.
    unshelve econstructor; [| now cbn]; now bsimpl.
Qed.

End Empty.
