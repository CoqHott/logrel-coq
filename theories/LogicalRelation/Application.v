Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction NormalRed.

Set Universe Polymorphism.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Section AppTerm.
  Context {wl Γ t u F G l l' l''}
    (hΠ : [Γ ||-Π<l> tProd F G]< wl >)
    {RFN : nat}
    {RF : forall wl' (τ : wl' ≤ε wl) (Ninfl : AllInLCon RFN wl'),
        [Γ ||-<l'> F]< wl' > }
    (Rt : [Γ ||-<l> t : tProd F G | LRPi' (normRedΠ0 hΠ)]< wl >)
    (RuN : nat)
    (Ru : forall wl' (τ : wl' ≤ε wl)
                 (Ninfl : AllInLCon RFN wl')
                 (Ninfl' : AllInLCon RuN wl'),
        [Γ ||-<l'> u : F | RF wl' τ Ninfl ]< wl' >)
    (RGu : W[Γ ||-<l''> G[u..]]< wl >).
  
  Definition AppTyN : nat.
  Proof.
    clear Rt RGu.
    destruct hΠ ; cbn in * ; clear hΠ.
    refine (max (max domN RFN) (max RuN _)).
    unshelve refine (Max_Bar _ _ _).
    + assumption.
    + exact (max (max domN RFN) RuN).
    + intros.
      unshelve eapply codomN.
      * assumption.
      * exact u.
      * exact wl'.
      * exact wk_id.
      * assumption.
      * eapply AllInLCon_le ; [ | eassumption].
        eapply Nat.max_lub_l.
        now eapply Nat.max_lub_l.
      * eapply wfc_Ltrans ; try eassumption.
        exact (wfc_wft domTy).
      * abstract (irrelevance0 ; [ | unshelve eapply Ru ; try eassumption ;
                           eapply AllInLCon_le ;
                           [ eapply Nat.max_lub_r ; now eapply Nat.max_lub_l |
                             eassumption | now eapply Nat.max_lub_r |
                             eassumption]] ;
                  assert (tProd dom cod = tProd F G) as ePi
                     by (eapply whredty_det ; gen_typing) ; 
                  inversion ePi ; subst ; 
                  now bsimpl).
  Defined.
Print AppTyN.  
  Definition AppTy : W[Γ ||-<l> G[u..]]< wl >.
  Proof.
    exists AppTyN.
    clear Rt RGu.
    pose proof (r:= PiRedTyPack.red hΠ). 
   assert (tProd (PiRedTyPack.dom hΠ) (PiRedTyPack.cod hΠ) = tProd F G) as ePi
        by (eapply whredty_det ; gen_typing) ; clear r.
    inversion ePi ; subst ; clear ePi.
    pose proof (wfΓ := wfc_wft (PiRedTyPack.domTy hΠ)).
    intros.
    replace ((PiRedTyPack.cod hΠ)[u..]) with ((PiRedTyPack.cod hΠ)[u .: _wk_id Γ >> tRel]) by now bsimpl.
    unshelve eapply ((PiRedTyPack.codRed hΠ) wk_id τ) ; unfold AppTyN in *.
    * unfold AppTyN in *.
      eapply AllInLCon_le ; [ | eassumption].
      unfold AppTyN.
      eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
    * exact (wfc_Ltrans τ wfΓ).
    * irrelevance0 ; [ | unshelve eapply Ru ; try eassumption ;
                         eapply AllInLCon_le ;
                         [ eapply Nat.max_lub_r ; now eapply Nat.max_lub_l |
                           eassumption | eapply Nat.max_lub_l ; now eapply Nat.max_lub_r |
                           eassumption]] ; now bsimpl.
    * now eapply wfLCon_le_id.
    * cbn.
      eapply AllInLCon_le ; [ | eassumption].
      etransitivity.
      2:{eapply Nat.max_lub_r.
         eapply Nat.max_lub_r.
         reflexivity. }
      etransitivity.
      2:{ unshelve eapply Max_Bar_le.
          + exact wl'.
          + assumption.
          + eapply AllInLCon_le ; [ | eassumption].
            eapply Nat.max_le_compat_l.
            now eapply Nat.max_lub_l.
          + intros.
            eapply ((PiRedTyPack.codomN_Ltrans hΠ)) ; try eassumption.
      }
        eapply (PiRedTyPack.codomN_Ltrans hΠ).
        now eapply wfLCon_le_id.
Defined.              

  Definition app_idN : nat.
  Proof.
    refine (max (max (max RFN RuN) (max (PiRedTyPack.domN hΠ) (PiRedTm.redN Rt))) _).
    unshelve eapply Max_Bar.
    - exact wl.
    - exact (max (max RFN RuN) (max (PiRedTyPack.domN hΠ) (PiRedTm.redN Rt))).
    - intros.
      unshelve eapply (PiRedTm.appN Rt).
      + assumption.
      + exact u.
      + exact wl'.
      + now eapply wk_id.
      + assumption.
      + eapply AllInLCon_le ; [ | eassumption].
        eapply Nat.max_lub_l ; now eapply Nat.max_lub_r.
      + eapply wfc_Ltrans ; try eassumption.
        exact (wfc_wft (PiRedTyPack.domTy hΠ)).
      + eapply AllInLCon_le ; [ | eassumption].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_r.
      + abstract (irrelevance0 ;
                  [ | unshelve eapply Ru ; try eassumption ;
                      eapply AllInLCon_le ;
                      [ eapply Nat.max_lub_l ; now eapply Nat.max_lub_l |
                        eassumption |
                        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l |
                        eassumption]] ;
                  now bsimpl).
Defined.
  
  Lemma app_id_aux : W[Γ ||-<l> tApp (PiRedTm.nf Rt) u : G[u..] | AppTy]< wl >.
  Proof.
    clear RGu.
    exists app_idN.
    intros.
    replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance0.  2: unshelve eapply (PiRedTm.app Rt).
    cbn; now bsimpl.
    - exact wl'.
    - assumption.
    - eapply AllInLCon_le ; [ | exact Ninfl'].
      unfold app_idN ; cbn.
      eapply Nat.max_lub_l ; eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
    - eapply wfc_Ltrans ; try eassumption.
      exact (wfc_wft (PiRedTyPack.domTy hΠ)).
    - irrelevance0.
      2:{ unshelve eapply LRTm_Ltrans.
          + exact l'.
          + exact wl'.
          + eapply RF ; try eassumption.
            eapply AllInLCon_le ; [ | exact Ninfl].
            cbn ; unfold AppTyN.
            eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
          + now eapply wfLCon_le_id.
          + eapply Ru.
            eapply AllInLCon_le ; [ | exact Ninfl].
            cbn ; unfold AppTyN.
            eapply Nat.max_lub_l ; now eapply Nat.max_lub_r.
      }
      now bsimpl.
    - now eapply wfLCon_le_id.
    - cbn ; unfold NormalRed.normRedΠ0_obligation_7.
      cbn.
      eapply AllInLCon_le ; [ | exact Ninfl].
      etransitivity.
      2:{eapply Nat.max_lub_r.
         eapply Nat.max_lub_r.
         cbn ; unfold AppTyN.
         reflexivity. }
      etransitivity.
      2:{ unshelve eapply Max_Bar_le.
          + exact wl'.
          + assumption.
          + eapply AllInLCon_le ; [ | exact Ninfl].
            cbn ; unfold AppTyN.
            eapply Nat.max_le_compat_l.
            now eapply Nat.max_lub_l.
          + intros.
            eapply ((PiRedTyPack.codomN_Ltrans hΠ)) ; try eassumption.
      }
      eapply (PiRedTyPack.codomN_Ltrans hΠ).
      now eapply wfLCon_le_id.
    - eapply AllInLCon_le ; [ | exact Ninfl'].
      unfold app_idN ; cbn.
      eapply Nat.max_lub_r ; eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
    - cbn.
      eapply AllInLCon_le ; [ | eassumption].
      etransitivity.
      2:{unfold app_idN.
         eapply Nat.max_lub_r.
         reflexivity. }
      etransitivity.
      2:{ unshelve eapply Max_Bar_le.
          + exact wl'.
          + assumption.
          + eapply AllInLCon_le ; [ | eassumption].
            unfold app_idN ; cbn.
            eapply Nat.max_lub_l.
            eapply Nat.max_le_compat_l.
            now econstructor.
          + intros.
            eapply (PiRedTm.appN_Ltrans Rt) ; try eassumption.
      }
      cbn.
      eapply (PiRedTm.appN_Ltrans Rt) ; try eassumption.
      now eapply wfLCon_le_id.
      Unshelve.
      + exact l'.
      + eapply RF ; try eassumption.
        cbn in *.
        unfold AppTyN in Ninfl.
        eapply AllInLCon_le ; [ | exact Ninfl].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
Qed.        

  Lemma app_id : W[Γ ||-<l''> tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    eapply WLRTmRedIrrelevantCum.
    exact app_id_aux.
  Qed.

  Lemma WappTerm0 :
      W[Γ ||-<l''> tApp t u : G[u..] | RGu]< wl >
      × W[Γ ||-<l''> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    Print redwfSubstTerm.
    split.
    - destruct app_id.
      exists (max (max RuN WNTm) RFN).
      intros.
      eapply redwfSubstTerm.
      + eapply WRedTm ; try eassumption.
        eapply AllInLCon_le ; [ | exact Ninfl'].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
      + escape.
        eapply redtmwf_app.
        split.
        * eapply ty_Ltrans ; try eassumption.
          apply Rt.
        * eapply redtm_Ltrans ; try eassumption.
          apply Rt.
        * eapply escapeTerm.
          unshelve eapply Ru ; try eassumption.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          now eapply Nat.max_lub_r.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
    - destruct app_id.
      exists (max (max RuN WNTm) RFN).
      intros.
      eapply redwfSubstTerm.
      + eapply WRedTm ; try eassumption.
        eapply AllInLCon_le ; [ | exact Ninfl'].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
      + escape.
        eapply redtmwf_app.
        split.
        * eapply ty_Ltrans ; try eassumption.
          apply Rt.
        * eapply redtm_Ltrans ; try eassumption.
          apply Rt.
        * eapply escapeTerm.
          unshelve eapply Ru ; try eassumption.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          now eapply Nat.max_lub_r.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
  Qed.
  

End AppTerm.

(*Lemma test {wl Γ F G l}
  (RΠ : W[Γ ||-<l> tProd F G]< wl >)
  : [Γ ||-Πd tProd F G ]< wl >.
Proof.
  destruct RΠ.
  unshelve econstructor.
  - exact F.
  - exact G.
  - refine (max WN _).
    unshelve eapply Max_Bar.
    + exact wl.
    + exact WN.
    + intros * tau allinl.
      refine (PiRedTyPack.domN _).
      eapply invLRΠ.
      exact (WRed wl' tau allinl).
  - intros * tau allinl delta.
    pose proof (zref := fun inf => (invLRΠ (WRed l' tau (AllInLCon_le _ _ (Nat.max_lub_l WN _ _ inf) _ allinl)))).
    pose (q:= fun inf => PiRedTyPack.domRed (wl' := l') (Δ := Δ) (invLRΠ (WRed l' tau inf))).
    cbn in q.
    assert (forall inf, LRPack l' Δ (PiRedTyPack.dom (invLRΠ (WRed l' tau inf)))⟨ρ⟩).
    intros inf.
    eapply q ; try eassumption.
    now eapply wfLCon_le_id.
    admit.
    
    unfold q.
    
      pose (t:= PiRedTyPack.domN (invLRΠ q)).*)
      
  

Lemma appTerm {wl Γ t u F G l}
  (RΠ : W[Γ ||-<l> tProd F G]< wl >)
  {RF : W[Γ ||-<l> F]< wl >}
  (Rt : W[Γ ||-<l> t : tProd F G | RΠ]< wl >)
  (Ru : W[Γ ||-<l> u : F | RF]< wl >)
  (RGu : W[Γ ||-<l> G[u..]]< wl >) : 
  W[Γ ||-<l> tApp t u : G[u..]| RGu]< wl >.
Proof.
  unshelve eapply WappTerm0.
  Print invLRΠ.
  8: irrelevance.



Lemma appTerm {wl Γ t u F G l}
  (RΠ : [Γ ||-<l> tProd F G]< wl >)
  {RF : [Γ ||-<l> F]< wl >}
  (Rt : [Γ ||-<l> t : tProd F G | RΠ]< wl >)
  (Ru : [Γ ||-<l> u : F | RF]< wl >)
  (RGu : [Γ ||-<l> G[u..]]< wl >) : 
  [Γ ||-<l> tApp t u : G[u..]| RGu]< wl >.
Proof.  
  unshelve eapply appTerm0.
  7:irrelevance.
  3: exact (invLRΠ RΠ).
  all: tea.
  irrelevance.
Qed.


Lemma appcongTerm {wl Γ t t' u u' F G l l'}
  (RΠ : [Γ ||-<l> tProd F G]< wl >) 
  {RF : [Γ ||-<l'> F]< wl >}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ]< wl >)
  (Ru : [Γ ||-<l'> u : F | RF]< wl >)
  (Ru' : [Γ ||-<l'> u' : F | RF]< wl >)
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]< wl >)
  (RGu : [Γ ||-<l'> G[u..]]< wl >)
   :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu]< wl >.
Proof.
  set (hΠ := invLRΠ RΠ); pose (RΠ' := LRPi' (normRedΠ0 hΠ)).
  assert [Γ ||-<l> t ≅ t' : tProd F G | RΠ']< wl > as [Rt Rt' ? eqApp] by irrelevance.
  set (h := invLRΠ _) in hΠ.
  epose proof (e := redtywf_whnf (PiRedTyPack.red h) whnf_tProd); 
  symmetry in e; injection e; clear e; 
  destruct h as [?????? domRed codRed codExt] ; clear RΠ Rtt'; 
  intros; cbn in *; subst. 
  assert (wfΓ : [|-Γ]< wl >) by gen_typing.
  assert [Γ ||-<l> u' : F⟨@wk_id Γ⟩ | domRed _ (@wk_id Γ) wfΓ]< wl > by irrelevance.
  assert [Γ ||-<l> u : F⟨@wk_id Γ⟩ | domRed _ (@wk_id Γ) wfΓ]< wl > by irrelevance.
  assert (RGu' : [Γ ||-<l> G[u'..]]< wl >).
  1:{
    replace G[u'..] with G[u' .: @wk_id Γ >> tRel] by now bsimpl.
    now eapply (codRed _ u' (@wk_id Γ)).
  }
  assert (RGuu' : [Γ ||-<l>  G [u'..] ≅ G[u..]  | RGu']< wl >).
  1:{
    replace G[u..] with G[u .: @wk_id Γ >> tRel] by now bsimpl.
    irrelevance0.
    2: unshelve eapply codExt.
    6: eapply LRTmEqSym; irrelevance.
    2-4: tea.
    now bsimpl.
  }
  eapply transEqTerm; eapply transEqTerm.
  - eapply (snd (appTerm0 hΠ Rt Ru RGu)).
  - unshelve epose  proof (eqApp _ u (@wk_id Γ) wfΓ _).  1: irrelevance. 
    replace (PiRedTm.nf Rt) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance.
  - unshelve epose proof (PiRedTm.eq Rt' (a:= u) (b:=u') (@wk_id Γ) wfΓ _ _ _).
    all: irrelevance.
  - replace (_)⟨_⟩ with (PiRedTm.nf Rt') by now bsimpl.
    eapply LRTmEqRedConv; tea.
    eapply LRTmEqSym.
    eapply (snd (appTerm0 hΠ Rt' Ru' RGu')).
Qed.

End Application.


