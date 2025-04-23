From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Irrelevance Monotonicity.

Section Split.
  Context `{GenericTypingProperties}.

  Lemma Split@{i j k l} {wl : wfLCon} {lA Γ A} {n : nat} {ne : not_in_LCon wl n} :
    (forall m, WLogRel@{i j k l} lA (wl ,,l (ne, m)) Γ A) ->
    WLogRel@{i j k l} lA wl Γ A.
  Proof.
    intros Hyp.
    unshelve eexists (ϝnode _ _).
    2: eassumption.
    1: intros m ; exact (WT _ (Hyp m)).
    intros wl' Hover.
    cbn in *.
    destruct (decidInLCon wl' n) ; [ | now inversion Hover].
    now eapply Hyp.
  Defined.

  Lemma EqSplit@{i j k l} {wl : wfLCon} {lA Γ A B} {n : nat} {ne : not_in_LCon wl n}
    HAt :
    (forall m, WLogRelEq@{i j k l} lA (wl ,,l (ne, m)) Γ A B (HAt m)) ->
    WLogRelEq@{i j k l} lA wl Γ A B (Split HAt).
  Proof.
    intros Hyp. 
    exists (ϝnode _ (fun m => WTEq _ (Hyp m))). 
    intros wl' Hover Hover' ; cbn in *.
    destruct (decidInLCon wl' n) ; [ | now inversion Hover].
    now eapply Hyp.
  Qed.

  Corollary EqSplit'@{i j k l} {wl : wfLCon} {lA Γ A B} {n : nat} {ne : not_in_LCon wl n}
    HAt HA :
    (forall m, WLogRelEq@{i j k l} lA (wl ,,l (ne, m)) Γ A B (HAt m)) ->
    WLogRelEq@{i j k l} lA wl Γ A B HA.
  Proof.
    intros HBt ; eapply WLRTyEqIrrelevant' ; [reflexivity | ].
    eapply EqSplit ; eassumption.
  Qed. 

  Lemma TmSplit@{i j k l} {wl : wfLCon} {lA Γ t A} {n : nat} {ne : not_in_LCon wl n}
    HAt :
    (forall m, WLogRelTm@{i j k l} lA (wl ,,l (ne, m)) Γ t A (HAt m)) ->
    WLogRelTm@{i j k l} lA wl Γ t A (Split HAt).
  Proof.
    intros Hyp.
    exists (ϝnode _ (fun m => WTTm _ (Hyp m))).
    intros wl' Hover Hover' ; cbn in *.
    destruct (decidInLCon wl' n) ; [ | now inversion Hover].
    now eapply Hyp.
  Qed.

  Corollary TmSplit'@{i j k l} {wl : wfLCon} {lA Γ t A} {n : nat} {ne : not_in_LCon wl n}
    HAt HA :
    (forall m, WLogRelTm@{i j k l} lA (wl ,,l (ne, m)) Γ t A (HAt m)) ->
    WLogRelTm@{i j k l} lA wl Γ t A HA.
  Proof.
    intros Htt ; eapply WLRTmRedIrrelevant' ; [reflexivity | ].
    eapply TmSplit ; eassumption.
  Qed. 

  Lemma TmEqSplit@{i j k l} {wl : wfLCon} {lA Γ t u A} {n : nat} {ne : not_in_LCon wl n}
    HAt :
    (forall m, WLogRelTmEq@{i j k l} lA (wl ,,l (ne, m)) Γ t u A (HAt m)) ->
    WLogRelTmEq@{i j k l} lA wl Γ t u A (Split HAt).
  Proof.
    intros Hyp.
    exists (ϝnode _ (fun m => WTTmEq _ (Hyp m))).
    intros wl' Hover Hover' ; cbn in *.
    destruct (decidInLCon wl' n) ; [ | now inversion Hover].
    now eapply Hyp.
  Qed.

  Lemma TmEqSplit'@{i j k l} {wl : wfLCon} {lA Γ t u A} {n : nat} {ne : not_in_LCon wl n}
    HAt HA :
    (forall m, WLogRelTmEq@{i j k l} lA (wl ,,l (ne, m)) Γ t u A (HAt m)) ->
    WLogRelTmEq@{i j k l} lA wl Γ t u A HA.
  Proof.
    intros Htt ; eapply WLRTmEqIrrelevant' ; [reflexivity | ].
    eapply TmEqSplit ; eassumption.
  Qed.

  Lemma TreeSplit@{i j k l} {wl : wfLCon} {lA Γ A}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> WLogRel@{i j k l} lA wl' Γ A) ->
    WLogRel@{i j k l} lA wl Γ A.
  Proof.
    eapply (split_to_over_tree@{l}).
    intros ; now eapply (Split).
  Qed.

  Lemma TreeEqSplit@{i j k l} {wl : wfLCon} {lA Γ A B}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> forall HA,
          WLogRelEq@{i j k l} lA wl' Γ A B HA) ->
    forall HA,
    WLogRelEq@{i j k l} lA wl Γ A B HA.
  Proof.
    intros Hyp ; pattern wl.
    eapply (split_to_over_tree@{l}).
    - intros wl' n ne HAt HA ; cbn in *.
      unshelve eapply EqSplit' ; eauto.
      intros m; eapply WLtrans@{k i j k l} ; [ | eassumption ].
      now eapply LCon_le_step, wfLCon_le_id.
    - intros wl' Hover HA.
      now eapply Hyp.
  Qed.

 Lemma TreeTmSplit@{i j k l} {wl : wfLCon} {lA Γ t A}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> forall HA,
          WLogRelTm@{i j k l} lA wl' Γ A t HA) ->
    forall HA,
    WLogRelTm@{i j k l} lA wl Γ A t HA.
  Proof.
    intros Hyp ; pattern wl.
    eapply (split_to_over_tree@{l}).
    - intros wl' n ne HAt HA ; cbn in *.
      unshelve eapply TmSplit' ; eauto.
      intros m ; eapply WLtrans@{k i j k l} ; [ | eassumption ].
      now eapply LCon_le_step, wfLCon_le_id.
    - intros wl' Hover HA.
      now eapply Hyp.
  Qed.
  
  Lemma TreeTmEqSplit@{i j k l} {wl : wfLCon} {lA Γ t u A}
    (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> forall HA,
          WLogRelTmEq@{i j k l} lA wl' Γ A t u HA) ->
    forall HA,
    WLogRelTmEq@{i j k l} lA wl Γ A t u HA.
  Proof.
    intros Hyp ; pattern wl.
    eapply (split_to_over_tree@{l}).
    - intros wl' n ne HAt HA ; cbn in *.
      unshelve eapply TmEqSplit' ; eauto.
      intros m ; eapply WLtrans@{k i j k l} ; [ | eassumption ].
      now eapply LCon_le_step, wfLCon_le_id.
    - intros wl' Hover HA.
      now eapply Hyp.
  Qed.
  
End Split.
