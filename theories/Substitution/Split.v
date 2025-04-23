From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Reflexivity Transitivity Monotonicity Split.
From LogRel.Substitution Require Import Irrelevance Properties Monotonicity.


Set Universe Polymorphism.

Section Split.
Context `{GenericTypingProperties}.

Lemma validTySplit {wl : wfLCon} {Γ l A} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >} :
  (forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >) ->
  [Γ ||-v<l> A | VΓ]< wl >.
Proof.
  intros VAt.
  unshelve econstructor.
  - intros ??????.
    destruct (decidInLCon wl' n) as [ m i | notin].
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n m ne (wfLCon_le_id _)).
      unshelve eapply VAt ; tea.
      change f with (f' •ε f'') in vσ.
      eapply subst_Ltrans' in vσ.
      unshelve eapply irrelevanceSubst.
      * exists (VPack_Ltrans f'' VΓ).
        now eapply  WfC_Ltrans.
      * assumption.
      * exact vσ.
    + unshelve eapply Split.
      2: exact notin.
      intros m.
      pose (i := @in_here_l wl' n m).
      pose (f' := @LCon_le_up wl wl' n m ne notin f). 
      pose (f'':= @LCon_le_step wl wl n m ne (wfLCon_le_id _)).
      pose (f''':= @LCon_le_step wl' wl' n m notin (wfLCon_le_id _)).
      unshelve eapply VAt ; tea.
      2: unshelve epose proof (X:= subst_Ltrans f''' _ vσ).
      1,2: now eapply wfc_Ltrans.
      change (f''' •ε f)  with (f' •ε f'') in X.
      eapply subst_Ltrans' in vσ.
      unshelve eapply irrelevanceSubst.
      -- exists (VPack_Ltrans f'' VΓ).
         now eapply  WfC_Ltrans.
      -- now eapply wfc_Ltrans.
      -- assumption.
  - cbn.
    intros.
    destruct (decidInLCon wl' n) as [ m i | notin] ; cbn in *.
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n m ne (wfLCon_le_id _)).
      unshelve eapply VAt.
      * change f with (f' •ε f'') in vσ'.
        eapply subst_Ltrans' in vσ'.
        unshelve eapply irrelevanceSubst ; [ | assumption | ]. 
        1: now eapply  WfC_Ltrans.
        exact vσ'.
      * change f with (f' •ε f'') in vσσ'.
        unshelve eapply eqsubst_Ltrans' in vσσ'.
        unshelve eapply irrelevanceSubstEq ; [ | assumption | | ]. 
        1: now eapply  WfC_Ltrans.
        2: exact vσσ'.
    + unshelve eapply EqSplit.
      intros m.
      pose (i := @in_here_l wl' n m).
      pose (f' := @LCon_le_up wl wl' n m ne notin f). 
      pose (f'':= @LCon_le_step wl wl n m ne (wfLCon_le_id _)).
      pose (f''':= @LCon_le_step wl' wl' n m notin (wfLCon_le_id _)).
      unshelve eapply VAt ; tea.
      * unshelve epose proof (X:= subst_Ltrans f''' _ vσ').
        1: now eapply wfc_Ltrans.
        change (f''' •ε f)  with (f' •ε f'') in X.
        eapply subst_Ltrans' in X.
        unshelve eapply irrelevanceSubst.
        -- exists (VPack_Ltrans f'' VΓ).
           now eapply  WfC_Ltrans.
        -- now eapply wfc_Ltrans.
        -- assumption.
      * unshelve epose proof (X:= eqsubst_Ltrans f''' _ _ vσσ').
        1: now eapply wfc_Ltrans.
        change (f''' •ε f)  with (f' •ε f'') in X.
        eapply eqsubst_Ltrans' in X.
        unshelve eapply irrelevanceSubstEq.
        1: cbn ; exists (VPack_Ltrans f'' VΓ) ; now eapply  WfC_Ltrans.
        1:  now eapply wfc_Ltrans.
        2: eassumption.
Defined.


Lemma validEqTySplit {wl : wfLCon} {Γ l A B} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >} :
  (forall m, [Γ ||-v<l> A ≅ B | VΓt m | VAt m]< _ >) ->
  [Γ ||-v<l> A ≅ B | VΓ | validTySplit VAt]< wl >.
Proof.
  intros VBt.
  unshelve econstructor.
  - intros ?????? ; cbn.
    destruct (decidInLCon wl' n) as [ m i | notin].
    + now eapply VBt.
    + eapply EqSplit.
      * intros m ; now eapply VBt.
Qed.

Lemma validEqTySplit' {wl : wfLCon} {Γ l A B} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >}:
  (forall m, [Γ ||-v<l> A ≅ B | VΓt m | VAt m]< _ >) ->
  [Γ ||-v<l> A ≅ B | VΓ | VA ]< wl >.
Proof.
  intros.
  unshelve eapply irrelevanceTyEq ; [eassumption | | ].
  2: now eapply validEqTySplit.
Qed.  

Lemma validTmSplit {wl : wfLCon} {Γ l A t} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >} :
  (forall m, [Γ ||-v<l> t : A | VΓt m | VAt m]< _ >) ->
  [Γ ||-v<l> t : A | VΓ | validTySplit VAt]< wl >.
Proof.
  intros Vtt.
  unshelve econstructor.
  - intros ?????? ; cbn.
    destruct (decidInLCon wl' n) as [ i | notin].
    + now eapply Vtt.
    + eapply TmSplit.
      * intros m ; now eapply Vtt.
  - intros ; cbn.
    destruct (decidInLCon wl' n) as [ m i | notin].
    + pose (f' := LCon_le_in_LCon (ne := ne) f i).
      pose (f'':= @LCon_le_step wl wl n m ne (wfLCon_le_id _)).
      unshelve eapply Vtt.
      * change f with (f' •ε f'') in Vσ'.
        eapply subst_Ltrans' in Vσ'.
        unshelve eapply irrelevanceSubst ; [ | assumption | ]. 
        1: now eapply  WfC_Ltrans.
        exact Vσ'.
      * change f with (f' •ε f'') in Vσσ'.
        unshelve eapply eqsubst_Ltrans' in Vσσ'.
        unshelve eapply irrelevanceSubstEq ; [ | assumption | | ]. 
        1: now eapply  WfC_Ltrans.
        2: exact Vσσ'.
    + unshelve eapply TmEqSplit.
      intros m ; pose (i := @in_here_l wl' n m).
      pose (f' := @LCon_le_up wl wl' n m ne notin f). 
      pose (f'':= @LCon_le_step wl wl n m ne (wfLCon_le_id _)).
      pose (f''':= @LCon_le_step wl' wl' n m notin (wfLCon_le_id _)).
      unshelve eapply Vtt ; tea.
      -- unshelve epose proof (X:= subst_Ltrans f''' _ Vσ').
         1: now eapply wfc_Ltrans.
         change (f''' •ε f)  with (f' •ε f'') in X.
         eapply subst_Ltrans' in X.
         unshelve eapply irrelevanceSubst.
         ++ exists (VPack_Ltrans f'' VΓ).
            now eapply  WfC_Ltrans.
         ++ now eapply wfc_Ltrans.
         ++ assumption.
      -- unshelve epose proof (X:= eqsubst_Ltrans f''' _ _ Vσσ').
         1: now eapply wfc_Ltrans.
         change (f''' •ε f)  with (f' •ε f'') in X.
         eapply eqsubst_Ltrans' in X.
         unshelve eapply irrelevanceSubstEq.
         1: cbn ; exists (VPack_Ltrans f'' VΓ) ; now eapply  WfC_Ltrans.
         1:  now eapply wfc_Ltrans.
         2: eassumption.
Qed.

Lemma validTmSplit' {wl : wfLCon} {Γ l A t} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >}:
  (forall m, [Γ ||-v<l> t : A | VΓt m | VAt m]< _ >) ->
  [Γ ||-v<l> t : A | VΓ | VA]< wl >.
Proof.
  intros.
  unshelve eapply irrelevanceTm ; [eassumption | | ].
  2: now eapply validTmSplit.
Qed.  

Lemma validEqTmSplit {wl : wfLCon} {Γ l t u A} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >} :
  (forall m, [Γ ||-v<l> t ≅ u : A | VΓt m | VAt m]< _ >) ->
  [Γ ||-v<l> t ≅ u : A | VΓ | validTySplit VAt]< wl >.
Proof.
  intros Vtut.
  unshelve econstructor.
  - intros ; cbn.
    destruct (decidInLCon wl' n) as [ m i | notin].
    + now eapply Vtut.
    + eapply TmEqSplit.
      * intros m ; now eapply Vtut.
Qed.
        

Lemma validEqTmSplit' {wl : wfLCon} {Γ l t u A} {n : nat} {ne : not_in_LCon wl n}
  {VΓt : forall m, [||-v Γ ]< (wl ,,l (ne, m)) >}
  {VΓ : [||-v Γ]< wl >}
  {VAt : forall m, [Γ ||-v<l> A | VΓt m]< wl ,,l (ne, m) >}
  {VA : [Γ ||-v<l> A | VΓ]< wl >}:
  (forall m, [Γ ||-v<l> t ≅ u : A | VΓt m | VAt m]< _ >) ->
  [Γ ||-v<l> t ≅ u : A | VΓ | VA]< wl >.
Proof.
  intros.
  unshelve eapply irrelevanceTmEq ; [eassumption | | ].
  2: now eapply validEqTmSplit.
Qed.  

Lemma WfCSplit {wl : wfLCon} {Γ} {n : nat} {ne : not_in_LCon wl n} :
  (forall m, [||-v Γ ]< (wl ,,l (ne, m)) >) ->
  [||-v Γ ]< wl >.
Proof.
  intros VGt.
  induction Γ as [ | A ? ?] ; cbn in *.
  - now eapply validEmpty'.
  - cbn in *.
    unshelve eapply validSnoc'.
    1: exact one.
    1:{ eapply IHΓ.
        intros m.
        exact (projT1 (projT2 (invValidity (VGt m)))).
    }
    unshelve eapply validTySplit ; [ | eassumption | ..] ; intros m.
    1: exact (projT1 (projT2 (invValidity (VGt m)))).
    destruct (invValidity (VGt m)) as [lt [VGt' [VAt [Hsubt [Hextt Heqt]]]]].
    destruct lt.
    + eapply embValidTy ; try eassumption.
      1: now constructor.
      eapply irrelevanceTy.
      exact VAt.
    + eapply irrelevanceTy.
      exact VAt.
Qed.

End Split.
