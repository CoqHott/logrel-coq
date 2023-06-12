From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application Universe SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var.

Set Universe Polymorphism.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma natRed {Γ l} : [|- Γ] -> [Γ ||-<l> tNat].
Proof. 
  intros; eapply LRNat_; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma natValid {Γ l} (VΓ : [||-v Γ]) : [Γ ||-v<l> tNat | VΓ].
Proof.
  unshelve econstructor; intros.
  + now eapply natRed.
  + cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma natconvValid {Γ l} (VΓ : [||-v Γ]) (VNat : [Γ ||-v<l> tNat | VΓ]) : 
  [Γ ||-v<l> tNat ≅ tNat | VΓ | VNat].
Proof.
  constructor; intros.
  enough [Δ ||-<l> tNat ≅ tNat | natRed wfΔ] by irrelevance.
  constructor; cbn; eapply redtywf_refl; gen_typing.
Qed.

Lemma redUOne {Γ} : [|- Γ] -> [Γ ||-U<one> U].
Proof.
  intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
Defined.

Lemma natTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tNat : U | LRU_ (redUOne wfΔ)].
Proof.
  econstructor.
  + eapply redtmwf_refl; gen_typing.
  + constructor.
  + gen_typing.
  + now eapply (natRed (l:= zero)).
Defined.

Lemma natTermValid {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tNat : U | VΓ | UValid VΓ].
Proof.
  constructor; intros.
  - eapply natTermRed. 
  - eexists (natTermRed wfΔ) (natTermRed wfΔ) (natRed wfΔ); cbn.
    + gen_typing.
    + now eapply (natRed (l:=zero)).
    + constructor; eapply redtywf_refl; gen_typing.
Qed.

Lemma zeroRed {Γ l} {NN : [Γ ||-Nat tNat]} (wfΓ : [|- Γ]): [Γ ||-<l> tZero : _ | LRNat_ l NN].
Proof.
  exists tZero.
  1,2: gen_typing.
  constructor.
Defined.

Lemma zeroRedEq {Γ l} {NN : [Γ ||-Nat tNat]} (wfΓ : [|- Γ]): [Γ ||-<l> tZero ≅ tZero : _ | LRNat_ l NN].
Proof.
  exists tZero tZero.
  1-3: gen_typing.
  constructor.
Defined.

Lemma zeroValid {Γ l} (VΓ : [||-v Γ]): 
  [Γ ||-v<l> tZero : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; [unshelve eapply zeroRed| unshelve eapply zeroRedEq]; tea.
Qed.

Lemma succRed {Γ l n} {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> n : _ | LRNat_ l NN] ->
  [Γ ||-<l> tSucc n : _ | LRNat_ l NN].
Proof.
  intros Rn; exists (tSucc n).
  + eapply redtmwf_refl; eapply ty_succ; now escape.
  + eapply convtm_succ; eapply escapeEqTerm; now eapply LREqTermRefl_.
  + now constructor.
Defined.

Lemma succRedEq {Γ l n n'} {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> n : _ | LRNat_ l NN] ->
  [Γ ||-<l> n' : _ | LRNat_ l NN] ->
  [Γ ||-<l> n ≅ n' : _ | LRNat_ l NN] ->
  [Γ ||-<l> tSucc n ≅ tSucc n' : _ | LRNat_ l NN].
Proof.
  intros ???; escape; exists (tSucc n) (tSucc n').
  1,2: eapply redtmwf_refl; now eapply ty_succ.
  + now eapply convtm_succ.
  + now constructor.
Defined.

Lemma succRedInv {Γ l n} {NN : [Γ ||-Nat tNat]} :
  [Γ ||-<l> tSucc n : _ | LRNat_ l NN] ->
  [Γ ||-<l> n : _ | LRNat_ l NN].
Proof.
  intros RSn; inversion RSn; subst. 
  unshelve epose proof (redtmwf_whnf red _). 1: constructor.
  subst. inversion prop; subst; tea.
  match goal with H : [ _ ||-NeNf _ : _] |- _ => destruct H; apply convneu_whne in refl; inv_whne end.
Qed.

Lemma succValid {Γ l n} (VΓ : [||-v Γ]) 
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tSucc n : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn.
  - instValid Vσ ; now unshelve eapply succRed.
  - instAllValid Vσ Vσ' Vσσ'; now unshelve eapply succRedEq.
Qed.

Lemma succcongValid {Γ l n n'} (VΓ : [||-v Γ]) 
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ])
  (Vn' : [Γ ||-v<l> n' : tNat | VΓ | natValid VΓ])
  (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; instValid Vσ; now unshelve eapply succRedEq.
Qed.

Lemma arr_subst_eq {A B σ} : (arr A B)[σ] = arr A[σ] B[σ].
Proof. now bsimpl. Qed.

Lemma shift_up_eq {t σ} : t⟨↑⟩[up_term_term σ] = t[σ]⟨↑⟩.
Proof. now bsimpl. Qed.

Lemma up_single_subst {t σ u} : t[up_term_term σ][u..] = t[u .:  σ].
Proof.  now bsimpl. Qed.

Lemma up_liftSubst_eq {σ t u} : t[up_term_term σ][u]⇑ = t[u .: ↑ >> up_term_term σ].
Proof.
  bsimpl. eapply ext_term; intros [|n]; cbn.
  1: reflexivity.
  unfold funcomp; now rewrite  rinstInst'_term.
Qed.

Lemma elimSuccHypTy_subst {P} σ :
  elimSuccHypTy P[up_term_term σ] = (elimSuccHypTy P)[σ].
Proof.
  unfold elimSuccHypTy.
  cbn. rewrite shift_up_eq.
  rewrite liftSubstComm. cbn. 
  now rewrite up_liftSubst_eq.
Qed.

Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Definition natElim {Γ A} (P hz hs : term) {n} {NA : [Γ ||-Nat A]} (p : NatProp NA n) : term.
Proof.
  destruct p.
  - exact hz.
  - exact (tApp (tApp hs n) (tNatElim P hz hs n)).
  - exact (tNatElim P hz hs ne).
Defined.

Section NatElimRed.
  Context {Γ l P hs hz}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Nat tNat])
    (RN := LRNat_ _ NN)
    (RP : [Γ,, tNat ||-<l> P])
    (RPpt : forall n, [Γ ||-<l> n : _ | RN] -> [Γ ||-<l> P[n..]])
    (RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]),
      [Γ ||-<l> n' : _ | RN] ->
      [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn])
    (RPz := RPpt _ (zeroRed wfΓ))
    (Rhz : [Γ ||-<l> hz : P[tZero..] | RPz]) 
    (RPs : [Γ ||-<l> elimSuccHypTy P])
    (Rhs : [Γ ||-<l> hs : _ | RPs]).

  Definition natRedElimStmt :=
    (forall n (Rn : [Γ ||-<l> n : _ | RN]), 
      [Γ ||-<l> tNatElim P hz hs n : _ | RPpt _ Rn ] ×
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim P hz hs (NatRedTm.nf Rn) : _ | RPpt _ Rn]) ×
    (forall n (Nn : NatProp NN n) (Rn : [Γ ||-<l> n : _ | RN]), 
      [Γ ||-<l> tNatElim P hz hs n : _ | RPpt _ Rn ] ×
      [Γ ||-<l> tNatElim P hz hs n ≅ natElim P hz hs Nn : _ | RPpt _ Rn]).

  Lemma natElimRedAux : natRedElimStmt.
  Proof.
    escape.
    apply NatRedInduction.
    - intros ? nf red ? nfprop ih.
      assert [Γ ||-<l> nf : _ | RN]. 1:{
        econstructor; tea.
        eapply redtmwf_refl; gen_typing.
      }
      eapply redSubstTerm.
      + eapply LRTmRedConv. 
        2: unshelve eapply ih; tea.
        eapply RPext. 
        2: eapply LRTmEqSym.
        1,2: eapply redwfSubstTerm; tea.
      + eapply redtm_natelim; tea.
        cbn; gen_typing.
    - intros. 
      eapply redSubstTerm.
      2: eapply redtm_natElimZero; tea.
      irrelevance.
    - intros n Rn ih RSucc; change [Γ ||-<l> n : tNat | RN] in Rn.
      eapply redSubstTerm.
      2: eapply redtm_natElimSucc; tea.
      2: now escape.
      eapply simple_appTerm.
      2: eapply ih.
      irrelevance0.
      2: unshelve eapply (appTerm RPs Rhs Rn).
      now bsimpl.
    - intros ? [] ?.
      epose proof (reflect _ (completeness _) _ (wk_id)) as [].
      all: repeat rewrite wk_id_ren_on.
      + now eapply ty_natElim.
      + now eapply ty_natElim.
      + eapply convneu_natElim; tea.
        { eapply escapeEq, LRTyEqRefl_. }
        { eapply escapeEqTerm; now eapply LREqTermRefl_. }
        { eapply escapeEqTerm; now eapply LREqTermRefl_. }
      + split ; irrelevance. 
    Unshelve.
    * eapply ArrRedTy; now eapply RPpt.
    * rewrite arr_subst_eq. eapply ArrRedTy.
      2: rewrite liftSubst_singleSubst_eq; cbn.
      all: now eapply RPpt.
    * now apply RPpt.
    * assumption.
    * exact l.
    * assumption.
  Qed.

  Lemma natElimRed : forall n (Rn : [Γ ||-<l> n : _ | RN]), [Γ ||-<l> tNatElim P hz hs n : _ | RPpt _ Rn ].
  Proof. intros. apply (fst natElimRedAux). Qed.
End NatElimRed.


Section NatElimRedEq.
  Context {Γ l P Q hs hs' hz hz'}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Nat tNat])
    (RN := LRNat_ _ NN)
    (RP : [Γ,, tNat ||-<l> P])
    (RQ : [Γ,, tNat ||-<l> Q])
    (eqPQ : [Γ,, tNat |- P ≅ Q])
    (RPpt : forall n, [Γ ||-<l> n : _ | RN] -> [Γ ||-<l> P[n..]])
    (RQpt : forall n, [Γ ||-<l> n : _ | RN] -> [Γ ||-<l> Q[n..]])
    (RPQext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]),
      [Γ ||-<l> n' : _ | RN] ->
      [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> P[n..] ≅ Q[n'..] | RPpt _ Rn])
    (RPz := RPpt _ (zeroRed wfΓ))
    (RQz := RQpt _ (zeroRed wfΓ))
    (Rhz : [Γ ||-<l> hz : P[tZero..] | RPz]) 
    (RQhz : [Γ ||-<l> hz' : Q[tZero..] | RQz]) 
    (RPQhz : [Γ ||-<l> hz ≅ hz' : _ | RPz])
    (RPs : [Γ ||-<l> elimSuccHypTy P])
    (RQs : [Γ ||-<l> elimSuccHypTy Q])
    (Rhs : [Γ ||-<l> hs : _ | RPs])
    (RQhs : [Γ ||-<l> hs' : _ | RQs])
    (RPQhs : [Γ ||-<l> hs ≅ hs' : _ | RPs ])
    .

  Lemma RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RN]),
      [Γ ||-<l> n' : _ | RN] ->
      [Γ ||-<l> n ≅ n' : _ | RN] ->
      [Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn].
  Proof.
    intros. eapply transEq; [| eapply LRTyEqSym ]; eapply RPQext; cycle 1; tea.
    now eapply LREqTermRefl_.
    Unshelve. 3,4: eauto. tea.
  Qed.

  Lemma natElimRedAuxLeft : @natRedElimStmt _ _ P hs hz NN RPpt.
  Proof.
    eapply natElimRedAux; tea.
    + eapply RPext.
  Qed.

  Lemma natElimRedAuxRight : @natRedElimStmt _ _ Q hs' hz' NN RQpt.
  Proof.
    eapply natElimRedAux; tea.
    + intros. eapply transEq; [eapply LRTyEqSym |]; eapply RPQext; cycle 1; tea.
      now eapply LREqTermRefl_.
    Unshelve. 2: eauto. all:tea.
  Qed.

  Lemma natElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]) (Rn : [Γ ||-<l> n : _ | RN]) (Rn' : [Γ ||-<l> n' : _ | RN]), 
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ Rn ]) ×
    (forall n n' (Rnn' : NatPropEq NN n n') (Rn : [Γ ||-<l> n : _ | RN]) (Rn' : [Γ ||-<l> n' : _ | RN]), 
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ Rn ]).
  Proof.
    apply NatRedEqInduction.
    - intros ?? nfL nfR redL redR ? prop ih RL RR; destruct (NatPropEq_whnf prop).
      assert [Γ ||-<l> nfL : _ | RN] by (eapply redTmFwd; cycle 1; tea).
      assert [Γ ||-<l> nfR : _ | RN] by (eapply redTmFwd; cycle 1; tea).
      eapply LREqTermHelper.
      * eapply (fst natElimRedAuxLeft).
      * eapply (fst natElimRedAuxRight).
      * eapply RPQext. 1: tea.
        now econstructor.
      * eapply LRTmEqRedConv.
        + eapply RPext; tea. 
          eapply LRTmEqSym; eapply redwfSubstTerm; cycle 1; tea.
        + unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ (NatRedTm.red RL) redL); tea.
          1: dependent inversion RL; subst; cbn; now eapply NatProp_whnf.
          unshelve erewrite (redtmwf_det _ _ _ _ _ _ _ _ (NatRedTm.red RR) redR); tea.
          1: dependent inversion RR; subst; cbn; now eapply NatProp_whnf.
          now eapply ih.
        Unshelve. tea.
    - intros. eapply LREqTermHelper.
      * unshelve eapply (snd natElimRedAuxLeft); constructor.
      * unshelve eapply (snd natElimRedAuxRight); tea; constructor.
      * eapply RPQext; [unshelve eapply zeroRed| unshelve eapply zeroRedEq]; tea.
      * cbn; irrelevance.
    - intros ??? ih Rn Rn'. pose proof (succRedInv Rn); pose proof (succRedInv Rn').
      eapply LREqTermHelper.
      * unshelve eapply (snd natElimRedAuxLeft); now constructor.
      * unshelve eapply (snd natElimRedAuxRight); tea; now constructor.
      * eapply RPQext; [unshelve eapply succRed| unshelve eapply succRedEq]; tea.
      * cbn.
        eapply simple_appcongTerm.
        4: now eapply ih.
        + irrelevance0. 2: eapply appcongTerm; tea.
          now bsimpl.
        + eapply (fst natElimRedAuxLeft).
        + eapply LRTmRedConv. 2: eapply (fst natElimRedAuxRight).
          eapply LRTyEqSym; now eapply RPQext.
        Unshelve. 2,4,5: tea.
        1: eapply ArrRedTy; now eapply RPpt.
        rewrite arr_subst_eq. eapply ArrRedTy.
        2: rewrite liftSubst_singleSubst_eq; cbn.
        all: now eapply RPpt.
    - intros ?? neueq ??. escape. inversion neueq.
      assert [Γ |- P[ne..] ≅ Q[ne'..]]. 1:{
        eapply escapeEq. eapply RPQext; tea.
        econstructor.
        1,2: now eapply redtmwf_refl.
        2: now constructor.
        gen_typing.
      }
      eapply neuTermEq.
      + eapply ty_natElim; tea.
      + eapply ty_conv. 
        1: eapply ty_natElim; tea.
        now symmetry.
      + eapply convneu_natElim ; tea.
      Unshelve. tea.
  Qed.

  Lemma natElimRedEq :
    (forall n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | RN]) (Rn : [Γ ||-<l> n : _ | RN]) (Rn' : [Γ ||-<l> n' : _ | RN]), 
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPpt _ Rn ]).
  Proof. apply natElimRedEqAux. Qed.
End NatElimRedEq.



Section NatElimValid.
  Context {Γ l P}
    (VΓ : [||-v Γ])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN]).
  
  Lemma elimSuccHypTyValid :
    [Γ ||-v<l> elimSuccHypTy P | VΓ].
  Proof.
    unfold elimSuccHypTy.
    unshelve eapply PiValid.
    1: exact VN.
    eapply simpleArrValid; tea.
    eapply substLiftS; tea.
    eapply irrelevanceTm.
    eapply succValid.
    eapply irrelevanceTm.
    change tNat with tNat⟨@wk1 Γ tNat⟩ at 2.
    eapply var0Valid.
    Unshelve. all: tea.
  Qed.

  Context {hz hs}
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz : P[tZero..] | VΓ | VPz]) 
    (Vhs : [Γ ||-v<l> hs : _ | VΓ | elimSuccHypTyValid]).


  Lemma natElimValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tNatElim P hz hs n : _ | VΓ | VPn].
  Proof.
    constructor; intros.
    - instValid Vσ; cbn.
      irrelevance0.  1: now rewrite singleSubstComm'.
      epose proof (Vuσ := liftSubstS' VN Vσ).
      instValid Vuσ; escape.
      unshelve eapply natElimRed; tea.
      + intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 1; tea.
        unshelve econstructor; [now bsimpl| now cbn].
      + rewrite elimSuccHypTy_subst. eapply validTy; tea; eapply elimSuccHypTyValid.
      + intros m m' Rm Rm' Rmm'; cbn.
        irrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt; cycle 1 ; tea.
        1,2: unshelve econstructor; [now bsimpl| now cbn].
        unshelve econstructor; [|now cbn].
        bsimpl; cbn; eapply reflSubst.
      + irrelevance.
      + irrelevance. now rewrite elimSuccHypTy_subst. 
    - instAllValid Vσ Vσ' Vσσ'.
      irrelevance0.  1: now rewrite singleSubstComm'.
      pose (Vuσ := liftSubstS' VN Vσ).
      pose proof (Vuσ' := liftSubstS' VN Vσ').
      pose proof (Vuσrea :=  liftSubstSrealign' VN Vσσ' Vσ').
      pose proof (Vuσσ' := liftSubstSEq' VN Vσσ').
      instValid Vuσ'; instAllValid Vuσ Vuσrea Vuσσ'; escape.
      unshelve eapply natElimRedEq; tea; fold subst_term.
      6-11: irrelevance; now rewrite elimSuccHypTy_subst.
      3,4: rewrite elimSuccHypTy_subst; eapply validTy; tea; eapply elimSuccHypTyValid.
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

  Lemma natElimZeroValid  : 
    [Γ ||-v<l> tNatElim P hz hs tZero ≅ hz : _ | VΓ | VPz].
  Proof.
    constructor; intros.
    epose proof (Vuσ := liftSubstS' VN Vσ).
    instValid Vσ; instValid Vuσ; escape.
    irrelevance0.  1: now rewrite singleSubstComm'.
    unshelve eapply (snd (natElimRedAux _ _ _ _ _ _ _ _) _ NatRedTm.zeroR); tea; fold subst_term.
    7: eapply zeroValid.
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
    + irrelevance.
    + rewrite elimSuccHypTy_subst. eapply validTy; tea; eapply elimSuccHypTyValid.
    + irrelevance. now rewrite elimSuccHypTy_subst. 
    Unshelve. 4: tea.
  Qed.

  Lemma natElimSuccValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN]) 
    (VPSn := substS VP (succValid _ Vn)) : 
    [Γ ||-v<l> tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : _ | VΓ | VPSn].
  Proof.
    constructor; intros.
    epose proof (Vuσ := liftSubstS' VN Vσ).
    instValid Vσ; instValid Vuσ; escape.
    irrelevance0.  1: now rewrite singleSubstComm'.
    pose (NSn := NatRedTm.succR RVn).
    unshelve eapply (snd (natElimRedAux _ _ _ _ _ _ _ _) _ NSn); tea; fold subst_term.
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
    + irrelevance.
    + rewrite elimSuccHypTy_subst. eapply validTy; tea; eapply elimSuccHypTyValid.
    + irrelevance. now rewrite elimSuccHypTy_subst. 
    + now eapply succRed.
  Qed.

End NatElimValid.

Lemma natElimCongValid {Γ l P Q hz hz' hs hs' n n'}
    (VΓ : [||-v Γ])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VQ : [Γ ,, tNat ||-v<l> Q | VΓN])
    (VPQ : [Γ ,, tNat ||-v<l> P ≅ Q | VΓN | VP])
    (VPz := substS VP (zeroValid VΓ))
    (VQz := substS VQ (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz : P[tZero..] | VΓ | VPz]) 
    (Vhz' : [Γ ||-v<l> hz' : Q[tZero..] | VΓ | VQz])
    (Vheqz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (VPs := elimSuccHypTyValid VΓ VP)
    (VQs := elimSuccHypTyValid VΓ VQ)
    (Vhs : [Γ ||-v<l> hs : _ | VΓ | VPs]) 
    (Vhs' : [Γ ||-v<l> hs' : _ | VΓ | VQs])
    (Vheqs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | VPs]) 
    (Vn : [Γ ||-v<l> n : _ | VΓ | VN])
    (Vn' : [Γ ||-v<l> n' : _ | VΓ | VN])
    (Veqn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn) :
    [Γ ||-v<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | VΓ | VPn].
Proof.
  constructor; intros.
  pose (Vuσ := liftSubstS' VN Vσ).
  instValid Vσ; instValid Vuσ; escape.
  irrelevance0.  1: now rewrite singleSubstComm'.
  unshelve eapply natElimRedEq; tea; fold subst_term.
  6-11: irrelevance; now rewrite elimSuccHypTy_subst.
  3,4: rewrite elimSuccHypTy_subst; eapply validTy; tea; eapply elimSuccHypTyValid.
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

Lemma elimSuccHypTyCongValid {Γ l P P'}
    (VΓ : [||-v Γ])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VP' : [Γ ,, tNat ||-v<l> P' | VΓN])
    (VeqP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN | VP]) :
    [Γ ||-v<l> elimSuccHypTy P ≅ elimSuccHypTy P' | VΓ | elimSuccHypTyValid VΓ VP].
  Proof.
    unfold elimSuccHypTy.
    eapply irrelevanceEq.
    assert [Γ,, tNat ||-v< l > P'[tSucc (tRel 0)]⇑ | validSnoc VΓ VN]. 1:{
      eapply substLiftS; tea.
      eapply irrelevanceTm.
      eapply succValid.
      eapply irrelevanceTm.
      change tNat with tNat⟨@wk1 Γ tNat⟩ at 2.
      eapply var0Valid.
    }
    eapply PiCong.
    - eapply simpleArrValid; tea.
    - eapply reflValidTy.
    - eapply simpleArrCongValid; tea.
      eapply substLiftSEq; tea.
    Unshelve. all: tea.
    unshelve eapply irrelevanceTm; tea.
    2: eapply succValid.
    unshelve eapply irrelevanceTm'.
    5: unshelve eapply var0Valid; tea.
    now bsimpl.
  Qed.

End Nat.
