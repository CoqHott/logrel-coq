(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
Require Import PeanoNat Nat.
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProperties}.

  Lemma escape {l wl Γ A} :
      [Γ ||-< l > A ]< wl > ->
      [Γ |- A]< wl >.
  Proof.
    intros lr.
    pattern l, wl,  Γ, A, lr.
    eapply LR_rect_TyUr.
    - intros * [].
      now gen_typing.
    - intros ? * [].
      now gen_typing.
    - intros ???? [] **; cbn in *.
      now gen_typing.
    - intros ???? []; gen_typing.
    - intros ???? []; gen_typing.
    - intros ???? []; gen_typing.
  Qed.

  Lemma Wescape {l wl Γ A} :
    W[ Γ ||-< l > A ]< wl > -> [Γ |- A]< wl >.
  Proof.
    intros [].
    remember (Lack_n wl WN) as q.
    revert wl Heqq WRed.
    induction q ; intros.
    - eapply escape.
      eapply WRed.
      + now eapply wfLCon_le_id.
      + eapply Lack_nil_AllInLCon.
        now symmetry.
    - unshelve eapply wft_ϝ.
      + exact a.
      + unshelve eapply Lack_n_notinLCon.
        exact WN.
        rewrite <- Heqq.
        cbn.
        now left.
      + eapply IHq.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * f allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
      + eapply IHq.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * f allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
  Qed.
  
  Lemma escapeEq {l wl Γ A B} (lr : [Γ ||-< l > A]< wl >) :
      [ Γ ||-< l > A ≅ B | lr ]< wl > ->
      [Γ |- A ≅ B]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    + intros ???? [] []. 
      gen_typing.
    + intros ???? [] [].
      cbn in *.
      eapply convty_exp.
      all: gen_typing.
    + intros ???? [] * ? ? [] ; cbn in *.
      gen_typing.
    + intros ???? [] []; gen_typing.
    + intros ???? [] []; gen_typing.
    + intros ???? [] []; gen_typing.
  Qed.

  Lemma WescapeEq {l wl Γ A B} (lr : W[Γ ||-< l > A]< wl >) :
      W[ Γ ||-< l > A ≅ B | lr ]< wl > ->
      [Γ |- A ≅ B]< wl >.
  Proof.
    intros [].
    destruct lr as [WN WRed].
    remember (Lack_n wl (max WN WNEq)) as q.
    revert wl Heqq WRed WRedEq.
    induction q ; intros.
    - unshelve eapply escapeEq ; [assumption | ..].
      1: eapply WRed ; [now eapply wfLCon_le_id | ..].
      2: eapply WRedEq.
      all: eapply Lack_nil_AllInLCon ;
        eapply Incl_nil ;
        rewrite Heqq ;
        eapply Lack_n_le.
      1: now eapply Nat.le_max_l.
      now eapply Nat.le_max_r.
    - unshelve eapply convty_ϝ.
      + exact a.
      + unshelve eapply Lack_n_notinLCon.
        exact (max WN WNEq).
        rewrite <- Heqq.
        now left.
      + unshelve eapply IHq.
        * intros * allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedEq ; try eassumption.
      + unshelve eapply IHq.
        * intros * allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedEq ; try eassumption.
  Qed.
  
  Definition escapeTerm {l wl Γ t A} (lr : [Γ ||-< l > A ]< wl >) :
    [Γ ||-< l > t : A | lr ]< wl > ->
    [Γ |- t : A]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ???? [] [] ; cbn in *.
      gen_typing.
    - intros ???? [] [] ; cbn in *.
      gen_typing.
    - intros ???? [] * ?? [] ; cbn in *.
      gen_typing.
    - intros ???? [] []; gen_typing.
    - intros ???? [] []; gen_typing.
    - intros ???? [] []; gen_typing.
  Qed.

  Definition WescapeTerm {l wl Γ t A} (lr : W[Γ ||-< l > A ]< wl >) :
    W[Γ ||-< l > t : A | lr ]< wl > ->
    [Γ |- t : A]< wl >.
  Proof.
    intros [].
    destruct lr as [WN WRed].
    remember (Lack_n wl (max WN WNTm)) as q.
    revert wl Heqq WRed WRedTm.
    induction q ; intros.
    - unshelve eapply escapeTerm ; [assumption | ..].
      1: eapply WRed ; [now eapply wfLCon_le_id | ..].
      2: eapply WRedTm.
      all: eapply Lack_nil_AllInLCon ;
        eapply Incl_nil ;
        rewrite Heqq ;
        eapply Lack_n_le.
      1: now eapply Nat.le_max_l.
      now eapply Nat.le_max_r.
    - unshelve eapply ty_ϝ.
      + exact a.
      + unshelve eapply Lack_n_notinLCon.
        exact (max WN WNTm).
        rewrite <- Heqq.
        now left.
      + unshelve eapply IHq.
        * intros * f allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedTm ; try eassumption.
      + unshelve eapply IHq.
        * intros * f allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedTm ; try eassumption.
  Qed.
   
  Definition escapeEqTerm {l wl Γ t u A} (lr : [Γ ||-< l > A ]< wl >) :
    [Γ ||-< l > t ≅ u : A | lr ]< wl > ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr.
    - intros ???? [] [[] []] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] [] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] * ?? [[termL] [termR]] ; cbn in *.
      eapply convtm_exp ; tea.
      all: gen_typing.
    - intros ???? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
    - intros ???? [] []; cbn in *.
      eapply convtm_exp; tea; gen_typing.
  Qed.

  Definition WescapeEqTerm {l wl Γ t u A} (lr : W[Γ ||-< l > A ]< wl >) :
    W[Γ ||-< l > t ≅ u : A | lr ]< wl > ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    intros [].
    destruct lr as [WN WRed].
    remember (Lack_n wl (max WN WNTmEq)) as q.
    revert wl Heqq WRed WRedTmEq.
    induction q ; intros.
    - unshelve eapply escapeEqTerm ; [assumption | ..].
      1: eapply WRed ; [now eapply wfLCon_le_id | ..].
      2: eapply WRedTmEq.
      all: eapply Lack_nil_AllInLCon ;
        eapply Incl_nil ;
        rewrite Heqq ;
        eapply Lack_n_le.
      1: now eapply Nat.le_max_l.
      now eapply Nat.le_max_r.
    - unshelve eapply convtm_ϝ.
      + exact a.
      + unshelve eapply Lack_n_notinLCon.
        exact (max WN WNTmEq).
        rewrite <- Heqq.
        now left.
      + unshelve eapply IHq.
        * intros * allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedTmEq ; try eassumption.
      + unshelve eapply IHq.
        * intros * allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedTmEq ; try eassumption.
  Qed.
  
  
  Lemma escapeConv {l wl Γ A} (RA : [Γ ||-<l> A]< wl >) :
    forall B,
    [Γ ||-<l> A ≅ B | RA]< wl > ->
    [Γ |- B]< wl >.
  Proof.
    pattern l, wl, Γ, A, RA; eapply LR_rect_TyUr; clear l Γ A RA.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * ihdom ihcod ? []; gen_typing.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
    - intros * []; gen_typing.
  Qed.

  Lemma WescapeConv {l wl Γ A} (RA : W[Γ ||-<l> A]< wl >) :
    forall B,
    W[Γ ||-<l> A ≅ B | RA]< wl > ->
    [Γ |- B]< wl >.
  Proof.
    intros B [].
    destruct RA as [WN WRed].
    remember (Lack_n wl (max WN WNEq)) as q.
    revert wl Heqq WRed WRedEq.
    induction q ; intros.
    - unshelve eapply escapeConv ; [assumption | exact A | ..].
      1: eapply WRed ; [now eapply wfLCon_le_id | ..].
      2: eapply WRedEq.
      all: eapply Lack_nil_AllInLCon ;
        eapply Incl_nil ;
        rewrite Heqq ;
        eapply Lack_n_le.
      1: now eapply Nat.le_max_l.
      now eapply Nat.le_max_r.
    - unshelve eapply wft_ϝ.
      + exact a.
      + unshelve eapply Lack_n_notinLCon.
        exact (max WN WNEq).
        rewrite <- Heqq.
        now left.
      + unshelve eapply IHq.
        * intros * allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedEq ; try eassumption.
      + unshelve eapply IHq.
        * intros * allinl.
          eapply WRed ; try eassumption.
          eapply wfLCon_le_trans ; try eassumption.
          eapply LCon_le_step.
          now eapply wfLCon_le_id.
        * symmetry.
          eapply Lack_n_add.
          now symmetry.
        * intros * allinl.
          now eapply WRedEq ; try eassumption.
  Qed.


    

  
Lemma LRTy_Ltrans@{i i' j j' k k' l l'} {lA} (wl wl' : wfLCon) (f : wl' ≤ε wl)
    (Γ : context) (A : term) :
    [ LogRel@{i j k l} lA | Γ ||- A ]< wl > ->
    [ LogRel@{i j k l} lA | Γ ||- A ]< wl' >.
Proof.
  intros [ [] lrA ] ; cbn in lrA.
  induction lrA as [? ? ? [l1 lt1] | ? ? ? [] | ? ? ? [] [] IHdom IHcod|??? []|??? [] |??? []] ; intros.
  - unshelve eapply LRU_.
    unshelve econstructor ; try assumption.
    + now eapply wfc_Ltrans.
    + destruct red.
      split ; try now eapply redty_Ltrans.
      now eapply wft_Ltrans.
  - unshelve eapply LRne_.
    unshelve econstructor ; try assumption.
    + destruct red ; split ; try now eapply redty_Ltrans.
      now eapply wft_Ltrans.
    + now eapply ty_ne_Ltrans.
    + now eapply convneu_Ltrans.
  - unshelve eapply LRPi_.
    cbn in *.
    unshelve econstructor.
    + exact dom.
    + exact cod.
    + exact domN.
    + intros.
      unshelve eapply domRed ; try assumption.
      now eapply wfLCon_le_trans.
    + intros.
      unshelve eapply codomN ; try assumption.
      now eapply wfLCon_le_trans.
      assumption.
    + intros ; cbn in *.
      unshelve eapply codRed ; [ exact l' | ..] ; try assumption.
      * now eapply wfLCon_le_trans.
      * assumption.
      * assumption.
    + destruct red.
      split.
      2: unshelve eapply redty_Ltrans ; try assumption.
      now eapply wft_Ltrans.
    + now eapply wft_Ltrans.
    + now eapply wft_Ltrans.
    + now eapply convty_Ltrans.
    + intros ; now eapply codExt.
    + cbn in *.
      econstructor.
      * intros. now eapply domAd.
      * intros. now eapply codAd.
  - unshelve eapply LRNat_.
    econstructor.
    destruct red.
    split ; try now eapply redty_Ltrans.
    now eapply wft_Ltrans.
  - unshelve eapply LRBool_.
    destruct red.
    econstructor.
    split ; try now eapply redty_Ltrans.
    now eapply wft_Ltrans.
  - unshelve eapply LREmpty_.
    destruct red.
    econstructor.
    split ; try now eapply redty_Ltrans.
    now eapply wft_Ltrans.
Qed.

Lemma LRTyEq_Ltrans@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > ->
            [Γ ||-< lA' > A ≅ B | lrA']< wl' >.
Admitted.


Lemma LRTm_Ltrans@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > ->
            [Γ ||-< lA' > t : A | lrA']< wl' >.
Admitted.


Lemma LRTm_Ltrans'@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > ->
            [Γ ||-< lA' > t : A | lrA']< wl' >.
Admitted.


Lemma LRTmEq_Ltrans@{i j k l i' j' k' l'} lA lA'
  (wl wl' : wfLCon) (f : wl' ≤ε wl) Γ A        
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >)
  (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl' >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > ->
            [Γ ||-< lA' > t ≅ u : A | lrA']< wl' >.
Admitted.
(*  intros B eqB.
  destruct lrA as [ [] lrA] ; cbn in *.
  induction lrA.
  
  cbn.
  induction lrA as [? ? ? ? | ? | ? ? A [] [] IHdom IHcod|?? NEA|?? NEA |?? NEA].
  - cbn.
    unshelve eapply LRTyEqIrrelevantCum ; [exact lA |..].
    + eapply LRTy_Ltrans ; try eassumption.
      eapply LRU_ ; econstructor ; eassumption.
    + cbn.
  pattern lA, wl, Γ, A, lrA. apply LR_rect_TyUr. clear lA Γ A lrA.
*)

  
End Escapes.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-< _ > _]< _ > |- _] => 
    let X := fresh "Esc" H in
    try pose proof (X := escape H) ;
    block H
  | [H : [_ ||-<_> _ ≅ _ | ?RA ]< _ > |- _] =>
    let X := fresh "Esc" H in
    try pose proof (X := escapeEq RA H) ;
    block H
  | [H : [_ ||-<_> _ : _ | ?RA]< _ > |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeTerm RA H) ;
    block H
  | [H : [_ ||-<_> _ ≅ _ : _ | ?RA]< _ > |- _] =>
    let X := fresh "R" H in
    try pose proof (X := escapeEqTerm RA H) ;
    block H
  end; unblock.
