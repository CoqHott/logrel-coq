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

Record helpTy2 {Γ F G l} (wl : wfLCon) (WN : nat)
  :=
  { f : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      wfLCon;
    ub : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      f wl' tau ne ≤ε wl ;
    lesser : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      wl' ≤ε f wl' tau ne ;
    ne : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      AllInLCon WN (f wl' tau ne) ;
    dom2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      term ;
    cod2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      term ;
    red2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      [Γ |-[ ta ] tProd F G :⇒*: tProd (dom2 wl' tau ne) (cod2 wl' tau ne) ]< (f wl' tau ne) > ;
    domTy2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      [Γ |-[ ta ] (dom2 wl' tau ne) ]< (f wl' tau ne) > ;
    codTy2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      [Γ ,, (dom2 wl' tau ne) |-[ ta ] (cod2 wl' tau ne) ]< (f wl' tau ne) > ;
    eq2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
      [Γ |-[ ta ] tProd (dom2 wl' tau ne) (cod2 wl' tau ne) ≅
             tProd (dom2 wl' tau ne) (cod2 wl' tau ne)]< (f wl' tau ne) > ;
    domN2 : nat ;
    domRed2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
    forall (Δ : context) (l' : wfLCon) (ρ : Δ ≤ Γ),
           l' ≤ε (f wl' tau ne) ->
           AllInLCon (domN2) l' -> [ |-[ ta ] Δ ]< l' > ->
           [Δ ||-< l > (dom2 wl' tau ne)⟨ρ⟩ ]< l' > ;
    codomN2 : forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
    forall (Δ : context) (a : term) (l' : wfLCon) (ρ : Δ ≤ Γ)
             (τ : l' ≤ε (f wl' tau ne))
             (Ninfl : AllInLCon (domN2) l') (h : [ |-[ ta ] Δ ]< l' >),
      [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- a : (dom2 wl' tau ne)⟨ρ⟩ ]< l' > -> nat ;
(*    codomN2_Ltrans :
    forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
    forall (Δ : context) (a : term) (l' l'' : wfLCon) 
           (ρ : Δ ≤ Γ)
           (τ : l' ≤ε (f wl' tau ne))
           (τ' : l'' ≤ε (f wl' tau ne))
           (Ninfl : AllInLCon (domN2) l')
           (Ninfl' : AllInLCon (domN2) l'')
           (h : [ |-[ ta ] Δ ]< l' >) (h' : [ |-[ ta ] Δ ]< l'' >)
           (ha : [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- a : (dom2 wl' tau ne)⟨ρ⟩ ]< l' >)
           (ha' : [domRed2 wl' tau ne Δ l'' ρ τ' Ninfl' h' | Δ ||- a : (dom2 wl' tau ne)⟨ρ⟩ ]< l'' >),
      l'' ≤ε l' ->
      codomN2 wl' tau ne Δ a l'' ρ τ' Ninfl' h' ha' <=
        codomN2 wl' tau ne Δ a l' ρ τ Ninfl h ha ;
    codomN2_Ltrans' :
    forall (wl' wl'' : wfLCon) (tau : wl' ≤ε wl) (tau' : wl'' ≤ε wl)
           (ne : AllInLCon WN wl') (ne' : AllInLCon WN wl''),
    forall (Δ : context) (a : term) (l': wfLCon) 
           (ρ : Δ ≤ Γ)
           (τ : l' ≤ε (f wl' tau ne))
           (τ' : l' ≤ε (f wl'' tau' ne'))
           (Ninfl : AllInLCon domN2 l')
           (h : [ |-[ ta ] Δ ]< l' >)
           (ha : [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- a : (dom2 wl' tau ne)⟨ρ⟩ ]< l' >)
           (ha' : [domRed2 wl'' tau' ne' Δ l' ρ τ' Ninfl h | Δ ||- a : (dom2 wl'' tau' ne')⟨ρ⟩ ]< l' >),
      wl'' ≤ε wl' ->
      codomN2 wl'' tau' ne' Δ a l' ρ τ' Ninfl h ha' <=
        codomN2 wl' tau ne Δ a l' ρ τ Ninfl h ha ;*)
    codRed2 :
    forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
    forall (Δ : context) (a : term) (l' : wfLCon) (ρ : Δ ≤ Γ)
             (τ : l' ≤ε (f wl' tau ne))
             (Ninfl : AllInLCon (domN2) l')
             (h : [ |-[ ta ] Δ ]< l' >)
             (ha : [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- a : (dom2 wl' tau ne)⟨ρ⟩ ]< l' >) 
             (l'' : wfLCon),
      l'' ≤ε l' ->
      AllInLCon (codomN2 wl' tau ne Δ a l' ρ τ Ninfl h ha) l'' ->
      [Δ ||-< l > (cod2 wl' tau ne)[a .: ρ >> tRel] ]< l'' > ;
    codExt2 :
    forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
    forall (Δ : context) (a b : term) (l' : wfLCon) (ρ : Δ ≤ Γ)
             (τ : l' ≤ε (f wl' tau ne))
             (Ninfl : AllInLCon domN2 l')
             (h : [ |-[ ta ] Δ ]< l' >)
             (ha : [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- a : (dom2 wl' tau ne)⟨ρ⟩ ]< l' >),
           [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- b : (dom2 wl' tau ne)⟨ρ⟩ ]< l' > ->
           [domRed2 wl' tau ne Δ l' ρ τ Ninfl h | Δ ||- a ≅ b : (dom2 wl' tau ne)⟨ρ⟩ ]< l' > ->
           forall (l'' : wfLCon) (τ' : l'' ≤ε l')
             (Minfl : AllInLCon (codomN2 wl' tau ne Δ a l' ρ τ Ninfl h ha) l''),
             [codRed2 wl' tau ne Δ a l' ρ τ Ninfl h ha l'' τ' Minfl |
               Δ ||- (cod2 wl' tau ne)[a .: ρ >> tRel] ≅
                 (cod2 wl' tau ne)[b .: ρ >> tRel] ]< l'' > ;
  }.


Section AppTerm.
  Context {wl Γ t u F G l l'}
    (hΠ : [Γ ||-Π<l> tProd F G]< wl >)
    {RFN : nat}
    {RF : forall wl' (τ : wl' ≤ε wl) (Ninfl : AllInLCon RFN wl'),
        [Γ ||-<l'> F]< wl' > }
    (Rt : [Γ ||-<l> t : tProd F G | LRPi' (hΠ)]< wl >)
    (RuN : nat)
    (Ru : forall wl' (τ : wl' ≤ε wl)
                 (Ninfl : AllInLCon RFN wl')
                 (Ninfl' : AllInLCon RuN wl'),
        [Γ ||-<l'> u : F | RF wl' τ Ninfl ]< wl' >)
  (*  (RGu : W[Γ ||-<l''> G[u..]]< wl >) *).
    
  Definition AppTyN : nat.
  Proof.
    refine (max (max (max RFN RuN)
               (max (PiRedTyPack.domN hΠ) (PiRedTm.redN Rt))) _).
    unshelve refine (Max_Bar _ _ _).
    About Max_Bar_Bar_lub.
    + assumption.
    + exact (max (max RFN RuN)
               (max (PiRedTyPack.domN hΠ) (PiRedTm.redN Rt))).
    + intros.
      unshelve eapply (PiRedTyPack.codomN hΠ).
      * assumption.
      * exact u.
      * exact wl'.
      * exact wk_id.
      * assumption.
      * (eapply AllInLCon_le ; [ | eassumption] ;
                  eapply Nat.max_lub_l ;
                  now eapply Nat.max_lub_r).
      * eapply wfc_Ltrans ; try eassumption.
        exact (wfc_wft (PiRedTyPack.domTy hΠ)).
      * abstract (irrelevance0 ;
                  [ | unshelve eapply Ru ; try eassumption ;
                      eapply AllInLCon_le ;
                      [ eapply Nat.max_lub_l ;
                        now eapply Nat.max_lub_l | eassumption |
                        eapply Nat.max_lub_r ;
                        now eapply Nat.max_lub_l | eassumption]] ;
         assert (tProd (PiRedTyPack.dom hΠ) (PiRedTyPack.cod hΠ) =
                   tProd F G) as ePi ;
         [pose proof (eq := (PiRedTyPack.red hΠ)) ;
          eapply whredty_det ; now gen_typing |
           inversion ePi ; now bsimpl]).
  Defined.
About AppTyN_subproof.
    

  Definition AppTy : W[Γ ||-<l> G[u..]]< wl >.
  Proof.
    exists AppTyN.
    pose proof (r:= PiRedTyPack.red hΠ). 
    assert (tProd (PiRedTyPack.dom hΠ) (PiRedTyPack.cod hΠ) = tProd F G) as ePi
        by (eapply whredty_det ; gen_typing) ; clear r.
    inversion ePi ; subst ; clear ePi.
    pose proof (wfΓ := wfc_wft (PiRedTyPack.domTy hΠ)).
    intros.
    replace ((PiRedTyPack.cod hΠ)[u..]) with ((PiRedTyPack.cod hΠ)[u .: _wk_id Γ >> tRel]) by now bsimpl.
    unshelve eapply ((PiRedTyPack.codRed hΠ) wk_id).
    - unshelve eapply (Bar_lub wl wl' _ τ).
      exact (max (max RFN RuN)
               (max (PiRedTyPack.domN hΠ) (PiRedTm.redN Rt))).
      (eapply AllInLCon_le ; try eassumption ;
                unfold AppTyN ;
                now eapply Nat.le_max_l).
    - now eapply Bar_lub_ub.
    - (eapply AllInLCon_le ; [ | now eapply Bar_lub_AllInLCon] ;
                  eapply Nat.max_lub_l ;
                  now eapply Nat.max_lub_r).
    - (eapply (wfc_Ltrans)).
      2: exact (wfc_wft (PiRedTyPack.domTy hΠ)).
      now eapply Bar_lub_ub.
    - now eapply (AppTyN_subproof).
    - now eapply Bar_lub_smaller.
    - cbn.
      eapply AllInLCon_le.
      2: eassumption.
      unfold AppTyN.
      etransitivity.
      2: now eapply Nat.max_lub_r.
      etransitivity.
      2: { unshelve eapply (Max_Bar_Bar_lub).
           2: eassumption.
           + (eapply AllInLCon_le ; try eassumption ;
                unfold AppTyN ;
                now eapply Nat.le_max_l).
           + now eapply Bar_lub_ub. 
           + now eapply Bar_lub_AllInLCon.
      }
      reflexivity.
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
      + (eapply AllInLCon_le ; [ | eassumption] ;
                  eapply Nat.max_lub_l ;
         now eapply Nat.max_lub_r).
      + eapply wfc_Ltrans ; try eassumption.
        exact (wfc_wft (PiRedTyPack.domTy hΠ)).
      + eapply AllInLCon_le ; [ | eassumption].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_r.
      + eapply AppTyN_subproof.
Defined.
  
  Lemma app_id_aux :
    W[Γ ||-<l> tApp (PiRedTm.nf Rt) u : G[u..] | AppTy]< wl >.
  Proof.
    exists app_idN.
    intros.
    replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
    irrelevance0.  2: unshelve eapply (PiRedTm.app Rt).
    cbn.
    abstract (assert (tProd (PiRedTyPack.dom hΠ) (PiRedTyPack.cod hΠ) = tProd F G) as ePi ;
              [ pose proof (red := (PiRedTyPack.red hΠ)) ;
                eapply whredty_det ; now gen_typing |
                inversion ePi ; subst ; 
                now bsimpl]).
    - unshelve eapply (Bar_lub wl wl' _ τ).
      + exact (max (max RFN RuN) (max (PiRedTyPack.domN hΠ) (PiRedTm.redN Rt))).
      + (eapply AllInLCon_le ; try eassumption ;
                unfold AppTyN ;
                now eapply Nat.le_max_l).
    - now eapply Bar_lub_ub.
    - (eapply AllInLCon_le ; [ | now eapply Bar_lub_AllInLCon] ;
                  eapply Nat.max_lub_l ;
       now eapply Nat.max_lub_r).
    - (eapply (wfc_Ltrans)).
      2: exact (wfc_wft (PiRedTyPack.domTy hΠ)).
      now eapply Bar_lub_ub.
    - eapply AppTyN_subproof.
    - now eapply Bar_lub_smaller.
    - cbn.
      unfold NormalRed.normRedΠ0_obligation_7.
      cbn.
      eapply AllInLCon_le ; [ | exact Ninfl].
      unfold AppTy ; cbn ; unfold AppTyN ; cbn.
      etransitivity.
      2:{eapply Nat.max_lub_r.
         cbn ; unfold AppTyN.
         reflexivity. }
      etransitivity.
      2:{ unshelve eapply (Max_Bar_Bar_lub).
          2: eassumption.
          + (eapply AllInLCon_le ; try eassumption ;
                unfold AppTyN ;
                now eapply Nat.le_max_l).
          + now eapply Bar_lub_ub.
          + now eapply Bar_lub_AllInLCon.
          + clear Ninfl Ninfl' τ wl'.
             (intros ;
              rewrite (AllInLCon_Irrel _ _ ne0 ne') ;
              rewrite (wfLCon_le_Irrel _ _ τ τ');
              reflexivity). }
      reflexivity.
    - eapply AllInLCon_le.
      2: eapply Bar_lub_AllInLCon.
      eapply Nat.max_lub_r ; now eapply Nat.max_lub_r. 
    - cbn.
      eapply AllInLCon_le ; [ | eassumption].
      etransitivity.
      2:{unfold app_idN.
         eapply Nat.max_lub_r.
         reflexivity. }
      etransitivity.
      2:{ unshelve eapply Max_Bar_Bar_lub.
          + exact wl'.
          + assumption.
          + (eapply AllInLCon_le ; try eassumption ;
                unfold AppTyN ;
                now eapply Nat.le_max_l). 
          + now eapply Bar_lub_ub.
          + cbn. now eapply Bar_lub_AllInLCon.
          + clear Ninfl Ninfl' τ wl'.
            intros ;
              rewrite (AllInLCon_Irrel _ _ ne0 ne') ;
              rewrite (wfLCon_le_Irrel _ _ τ τ');
              reflexivity.
      }
      cbn.
      reflexivity.
Qed.        

  Lemma app_id {l''} (RGu : W[Γ ||-<l''> G[u..]]< wl >):
    W[Γ ||-<l''> tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    eapply WLRTmRedIrrelevantCum.
    exact app_id_aux.
  Qed.

  Lemma WappTerm0 {l''} (RGu : W[Γ ||-<l''> G[u..]]< wl >):
      W[Γ ||-<l''> tApp t u : G[u..] | RGu]< wl >
      × W[Γ ||-<l''> tApp t u ≅ tApp (PiRedTm.nf Rt) u : G[u..] | RGu]< wl >.
  Proof.
    Print redwfSubstTerm.
    split.
    - destruct (app_id RGu).
      exists (max (max RuN WNTm) RFN).
      intros.
      eapply redwfSubstTerm.
      + eapply WRedTm ; try eassumption.
        eapply AllInLCon_le ; [ | exact Ninfl'].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
      + escape.
        unshelve eapply redtmwf_app ; [ exact F |..].
        destruct Rt ; cbn in *.
        destruct hΠ ; cbn in *.
        split.
        * eapply ty_Ltrans ; try eassumption.
          destruct red.
          eapply ty_exp.
          -- eassumption.
          -- now destruct red0.
        * eapply redtm_Ltrans ; try eassumption.
          eapply redtm_conv.
          -- now destruct red.
          -- unshelve eapply convty_exp.
             5 : exact eq0.
             ++ eapply redty_refl.
                gen_typing.
             ++ now destruct red0. 
        * eapply escapeTerm.
          unshelve eapply Ru ; try eassumption.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          now eapply Nat.max_lub_r.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
    - destruct (app_id RGu).
      exists (max (max RuN WNTm) RFN).
      intros.
      eapply redwfSubstTerm.
      + eapply WRedTm ; try eassumption.
        eapply AllInLCon_le ; [ | exact Ninfl'].
        eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
      + escape.
        eapply redtmwf_app.
        destruct Rt ; cbn in *.
        destruct hΠ ; cbn in *.
        split.
        * eapply ty_Ltrans ; try eassumption.
          destruct red.
          eapply ty_exp.
          -- eassumption.
          -- now destruct red0.
        * eapply redtm_Ltrans ; try eassumption.
          eapply redtm_conv.
          -- now destruct red.
          -- unshelve eapply convty_exp.
             5 : exact eq0.
             ++ eapply redty_refl.
                gen_typing.
             ++ now destruct red0. 
        * eapply escapeTerm.
          unshelve eapply Ru ; try eassumption.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          now eapply Nat.max_lub_r.
          eapply AllInLCon_le ; [ | exact Ninfl'].
          eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
  Qed.
  

End AppTerm.


Definition help {wl Γ F G l} (WN : nat)
  (WRed : forall wl' : wfLCon, wl' ≤ε wl ->
                               AllInLCon WN wl' ->
                               [Γ ||-Π< l > tProd F G ]< wl' >) :
  helpTy2 (Γ := Γ) (F := F) (G := G) (l := l) wl WN.
Proof.
  unshelve econstructor.
  - intros wl' τ Ninfl.
    exact (Bar_lub wl wl' WN τ Ninfl).
  - intros.
    refine (PiRedTyPack.dom _).
    unshelve eapply WRed.
    unshelve eapply Bar_lub_ub ; try eassumption.
    unshelve eapply Bar_lub_AllInLCon.
  - intros.
    refine (PiRedTyPack.cod _).
    unshelve eapply WRed.
    unshelve eapply Bar_lub_ub ; try eassumption.
    unshelve eapply Bar_lub_AllInLCon.
  - intros.
    unshelve eapply Max_Bar.
    + exact wl.
    + exact WN.
    + intros * tau Ninfl.
      refine (PiRedTyPack.domN _).
      unshelve eapply WRed ; try eassumption.
  - cbn.
    intros * τ Ninfl h.
    refine (PiRedTyPack.domRed _ _ _ _ _) ; try eassumption.
    eapply AllInLCon_le ; [ | exact Ninfl].
    unshelve eapply
      (Max_Bar_Bar_lub _ _ (fun wl'0 tau0 Ninfl0 =>
                              PiRedTyPack.domN (WRed wl'0 tau0 Ninfl0))).
    (intros ;
     rewrite (AllInLCon_Irrel _ _ ne1 ne') ;
     now rewrite (wfLCon_le_Irrel _ _ τ0 τ')).
  - cbn.
    intros * ha.
    refine (PiRedTyPack.codomN _ _ _ _ _ _) ; try eassumption.
  - cbn.
    intros * τ' Minfl.
    refine (PiRedTyPack.codRed _ _ _ _ _ _ _ _) ; try eassumption.
  - cbn.
    intros.
    now eapply Bar_lub_ub.
  - cbn ; intros.
    now eapply Bar_lub_smaller.
  - cbn ; intros.
    now eapply Bar_lub_AllInLCon.
  - cbn.
    intros.
    refine (PiRedTyPack.red _) ; try eassumption.
  - cbn.
    intros.
    refine (PiRedTyPack.domTy _) ; try eassumption.
  - cbn.
    intros.
    refine (PiRedTyPack.codTy _) ; try eassumption.
  - cbn.
    intros.
    refine (PiRedTyPack.eq _) ; try eassumption.
  - cbn ; intros * hb hab *.
    eapply (PiRedTyPack.codExt _) ; try eassumption.
Qed.

Lemma test {wl Γ F G l}
  (RΠ : W[Γ ||-<l> tProd F G]< wl >)
  : [Γ ||-Π< l > tProd F G ]< wl >.
Proof.
  destruct RΠ.
  destruct (help _ (fun wl' tau Ninfl => invLRΠ (WRed wl' tau Ninfl))).
  assert (forall (wl' : wfLCon) (tau : wl' ≤ε wl) (ne : AllInLCon WN wl'),
             tProd F G = tProd (dom3 wl' tau ne) (cod3 wl' tau ne)) as ePi.
  intros.
  1:{ now eapply whredty_det ; gen_typing . }
  unshelve econstructor.
  - exact F.
  - exact G.
  - exact (max WN domN3).
  - intros * ? ? h.
    eapply LRCumulative'.
    2: {unshelve eapply domRed3 ; try eassumption.
        + eapply AllInLCon_le ; [ | exact Ninfl].
          now eapply Nat.le_max_l.
        + now eapply lesser0.
        + eapply AllInLCon_le ; [ | exact Ninfl].
          now eapply Nat.le_max_r. }
    + abstract
        (specialize ePi with wl' τ (AllInLCon_le WN (Init.Nat.max WN domN3) (Nat.le_max_l WN domN3) wl' Ninfl) ;
         now inversion ePi).
  - cbn.
    intros.
    unshelve eapply codomN3 ; try eassumption.
     + eapply AllInLCon_le ; [ | exact Ninfl].
          now eapply Nat.le_max_l.
     + now eapply lesser0.
     + eapply AllInLCon_le ; [ | exact Ninfl].
       now eapply Nat.le_max_r.
     + irrelevance0.
       2: exact ha.
       exact (eq_sym (test_subproof wl Γ F G WN dom3 cod3 domN3 ePi Δ wl' ρ τ Ninfl)).
  - cbn.
    intros.
    eapply LRCumulative'.
    2:{ unshelve eapply codRed3.
        4 : exact τ.
        9 : exact τ'.
        all : try eassumption. }
    abstract
      (pose proof (ePi' := ePi wl' τ (AllInLCon_le WN (Init.Nat.max WN domN3) (Nat.le_max_l WN domN3) wl' Ninfl)) ; now inversion ePi').
  - econstructor.
    2: eapply redty_refl .
    all: unshelve eapply wft_ϝ_Bar ; try exact WN.
    all: intros * f allinl.
    all: unshelve eapply wft_Ltrans ; try exact (f0 wl' f allinl).
    all: try now eapply lesser0.
    all: destruct (red3 wl' f allinl).
    all: now eapply redty_ty_src.
  - unshelve eapply wft_ϝ_Bar ; try exact WN.
    intros * f allinl.
    unshelve eapply wft_Ltrans ; try exact (f0 wl' f allinl).
    1: now eapply lesser0.
    replace F with (dom3 wl' f allinl).
    1: now eapply domTy3.
    abstract
        (specialize ePi with wl' f allinl ;
         now inversion ePi).
  - unshelve eapply wft_ϝ_Bar ; try exact WN.
    intros * f allinl.
    unshelve eapply wft_Ltrans ; try exact (f0 wl' f allinl).
    1: now eapply lesser0.
    replace F with (dom3 wl' f allinl).
    replace G with (cod3 wl' f allinl).
    1: now eapply codTy3.
    all: abstract
        (specialize ePi with wl' f allinl ;
         now inversion ePi).
  - unshelve eapply convty_ϝ_Bar ; try exact WN.
    intros * f allinl.
    unshelve eapply convty_Ltrans ; try exact (f0 wl' f allinl).
    1: now eapply lesser0.
    replace (tProd F G) with (tProd (dom3 wl' f allinl) (cod3 wl' f allinl)).
    1: now eapply eq3.
    now eapply (eq_sym (ePi _ _ _)).
  - cbn.
    intros * hb hab *.
    pose proof (ePi' := ePi wl' τ (AllInLCon_le WN (Init.Nat.max WN domN3) (Nat.le_max_l WN domN3) wl' Ninfl)) ; inversion ePi' ; subst.
    irrelevance0.
    2:{ unshelve eapply codExt3.
        9 : irrelevance0 ; [ | exact hb] ; reflexivity.
        8: irrelevance0 ; [ | exact hab] ; reflexivity.
        all: try eassumption.
    }
    reflexivity.
Qed.
      
  

Lemma appTerm {wl Γ t u F G l}
  (RΠ : W[Γ ||-<l> tProd F G]< wl >)
  {RF : W[Γ ||-<l> F]< wl >}
  (Rt : W[Γ ||-<l> t : tProd F G | RΠ]< wl >)
  (Ru : W[Γ ||-<l> u : F | RF]< wl >)
  (RGu : W[Γ ||-<l> G[u..]]< wl >) : 
  W[Γ ||-<l> tApp t u : G[u..]| RGu]< wl >.
Proof.
  unshelve eapply WappTerm0.
  4: now eapply test.
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


