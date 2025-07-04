From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Split Neutral Weakening Monotonicity Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties Monotonicity.
From LogRel.Substitution.Introductions Require Import Universe.

Set Universe Polymorphism.

Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.

Lemma subst_wk_id_tail Γ P t : P[t .: @wk_id Γ >> tRel] = P[t..].
Proof. setoid_rewrite id_ren; now bsimpl. Qed.


Set Printing Primitive Projection Parameters.

Section PolyValidity.

  Context `{GenericTypingProperties}.

  Lemma mkPolyRed {Γ wl l A B} (wfΓ : [|-Γ]< wl >)
    (RA : forall Δ wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >), [Δ ||-<l> A⟨ρ⟩]< wl' >)
    (RB : forall Δ a wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >) (Ha : [Δ ||-<l> a : _ | RA Δ wl' ρ f wfΔ]< wl' >),
        W[Δ ||-<l> B[a .: ρ >> tRel]]< wl' >)
    (RBext : forall Δ a b wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >)
                    (Ra : [Δ ||-<l> a : _ | RA Δ wl' ρ f wfΔ]< wl' >)
                    (Rb : [Δ ||-<l> b : _ | RA Δ wl' ρ f wfΔ]< wl' >)
                    (Req: [Δ ||-<l> a ≅ b : _ | RA Δ wl' ρ f wfΔ]< wl' >),
                    W[Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a wl' ρ f wfΔ Ra]< wl' >) :
    PolyRed wl Γ l A B.
  Proof.
    assert [Γ |- A]< wl > by (eapply escape ; now eapply instKripke').
    unshelve econstructor; tea.
    - intros ; now eapply RB.
    - cbn ; intros.
      now eapply RB.
    - intros ; eapply RBext ; [exact ha |..] ; eassumption.
    - unshelve epose proof (X := RB _ (tRel 0) wl (@wk1 Γ A) (wfLCon_le_id _) _ _).
      + now gen_typing.
      + eapply var0; tea ; now rewrite wk1_ren_on .
      + enough (B = B[tRel 0 .: @wk1 Γ A >> tRel]) as ->.  
        2: setoid_rewrite wk1_ren; rewrite scons_eta'; now asimpl.
        now Wescape.
    - cbn in * ; intros.
      now eapply RBext.
  Qed.

  Lemma mkPolyRed' {Γ wl l A B} (RA : [Γ ||-<l> A]< wl >) 
    (RB : forall Δ a wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >),
        [Δ ||-<l> a : _ | wk_Ltrans ρ f wfΔ RA]< wl' > -> W[Δ ||-<l> B[a .: ρ >> tRel]]< wl' >)
    (RBext : forall Δ a b wl' (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|- Δ]< wl' >) (Ra : [Δ ||-<l> a : _ | wk_Ltrans ρ f wfΔ RA]< wl' >),
      [Δ ||-<l> b : _ | wk_Ltrans ρ f wfΔ RA]< wl' > ->
      [Δ ||-<l> a ≅ b : _ | wk_Ltrans ρ f wfΔ RA]< wl' > ->
      W[Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a wl' ρ f wfΔ Ra]< wl' >) :
    PolyRed wl Γ l A B.
  Proof.
    unshelve eapply mkPolyRed; tea.
    3: escape; gen_typing.
    1: intros ; now eapply wk_Ltrans.
    - intros ; now eapply RB.
    - intros ; now eapply RBext.
  Qed.


  Lemma polyCodSubstRed {Γ wl l F G} (RF : [Γ ||-<l> F]< wl >) : 
    PolyRed wl Γ l F G -> forall t, [Γ ||-<l> t : _ | RF]< wl > -> W[Γ ||-<l> G[t..]]< wl >.
  Proof.
    intros PFG ??. 
    escape. assert (wfΓ : [|- Γ]< wl >) by gen_typing.
    erewrite <- subst_wk_id_tail.
    unshelve econstructor.
    - unshelve eapply (PolyRed.posTree PFG wk_id (wfLCon_le_id _) wfΓ).
      2: irrelevance. 
    - now eapply (PolyRed.posRed PFG wk_id _ wfΓ).
  Qed.

  Lemma polyCodSubstExtRed {Γ wl l F G} (RF : [Γ ||-<l> F]< wl >) (PFG : PolyRed wl Γ l F G) (RG := polyCodSubstRed RF PFG) :
    forall t u (Rt : [Γ ||-<l> t : _ | RF]< wl >), [Γ ||-<l> u : _ | RF]< wl > -> [Γ ||-<l> t ≅ u : _ | RF]< wl > -> 
    W[Γ ||-<l> G[t..] ≅ G[u..]| RG t Rt]< wl >.
  Proof.
    intros. escape. assert (wfΓ : [|- Γ]< wl >) by gen_typing.
    unshelve Wirrelevance0 ; [eassumption | ..].
    3: erewrite <- subst_wk_id_tail; reflexivity.
    1,2: unshelve econstructor.
    - eapply DTree_fusion.
      + eapply (PolyRed.posTree (a := t) PFG wk_id (wfLCon_le_id _) wfΓ).
        irrelevance.
      + eapply (PolyRed.posTree (a := u) PFG wk_id (wfLCon_le_id _) wfΓ).
        irrelevance.
    - unshelve eapply (PolyRed.posExtTree PFG wk_id (wfLCon_le_id _) wfΓ).
      5: irrelevance.
      1,2: now irrelevance.
    - intros.
      now eapply (PolyRed.posRed PFG wk_id _ wfΓ), over_tree_fusion_l.
    - intros ; irrelevanceRefl.
      erewrite <- subst_wk_id_tail.
      unshelve eapply (PolyRed.posExt PFG wk_id (wfLCon_le_id _) wfΓ).
      1,3,4: irrelevance.
      3: eassumption.
      1: eapply over_tree_fusion_l ; exact Hover.
      1: eapply over_tree_fusion_r ; exact Hover.
  Qed.  


  Lemma polyRedId {Γ wl l F G} : PolyRed wl Γ l F G -> [Γ ||-<l> F]< wl > × W[Γ ,, F ||-<l> G]< wl >.
  Proof.
    intros [?? RF ? RG]; split.
    - rewrite <- (wk_id_ren_on Γ F).
      eapply RF ; [now eapply wfLCon_le_id | now gen_typing].
    - replace G with G[tRel 0 .: @wk1 Γ F >> tRel].
      2: bsimpl; rewrite scons_eta'; now asimpl.
      econstructor ; eapply RG.
      Unshelve.
      + now eapply wfLCon_le_id.
      + now gen_typing.
      + eapply var0; tea; now bsimpl.
  Qed.

  Lemma WpolyRedId {Γ wl l F G} : WPolyRed wl Γ l F G -> W[Γ ||-<l> F]< wl > × W[Γ ,, F ||-<l> G]< wl >.
  Proof.
    intros [d Hd] ; split.
    - exists d ; intros wl' Ho ; specialize (Hd _ Ho) as [?? RF ? RG].
      rewrite <- (wk_id_ren_on Γ F).
      eapply RF ; [now eapply wfLCon_le_id | now gen_typing].
    - pattern wl.
      unshelve eapply split_to_over_tree ; [exact d | | ].
      + intros ; now eapply Split.
      + intros wl' Ho ; specialize (Hd _ Ho) as [?? RF ? RG].
        replace G with G[tRel 0 .: @wk1 Γ F >> tRel].
        2: bsimpl; rewrite scons_eta'; now asimpl.
        econstructor ; eapply RG.
        Unshelve.
        * now eapply wfLCon_le_id.
        * now gen_typing.
        * eapply var0; tea; now bsimpl.
Qed.

  Lemma polyRedEqId {Γ wl l F F' G G'} (PFG : PolyRed wl Γ l F G) (RFG := polyRedId PFG) :
    PolyRedEq PFG F' G' -> [Γ ||-<l> F ≅ F' | fst RFG]< wl > × W[Γ ,, F ||-<l> G ≅ G' | snd RFG]< wl >.
  Proof.
    intros [RFF' ? RGG']; destruct RFG; escape; split.
    - rewrite <- (wk_id_ren_on Γ F'); irrelevance0.
      2: unshelve eapply RFF'; [ now eapply wfLCon_le_id | gen_typing].
      now apply wk_id_ren_on.
    - replace G' with G'[tRel 0 .: @wk1 Γ F >> tRel].
      2: bsimpl; rewrite scons_eta'; now asimpl.
      unshelve econstructor ; intros.
      1: eapply DTree_fusion ; [eapply (PolyRedPack.posTree PFG (wk1 F)) | eapply posTree].
      1,2: eapply var0 ; tea.
      1: now bsimpl.
      2: irrelevance0.
      3: eapply RGG'. 
      2: bsimpl; rewrite scons_eta'; now asimpl.
      Unshelve.
      2: eapply over_tree_fusion_r ; exact Hover'.
      2,4: now eapply wfLCon_le_id.
      2,3: now gen_typing.
      1: now bsimpl.
      eapply over_tree_fusion_l ; exact Hover'. 
  Qed.

  Lemma WpolyRedEqId {Γ wl l F F' G G'} (PFG : WPolyRed wl Γ l F G) (RFG := WpolyRedId PFG) :
    WPolyRedEq PFG F' G' -> W[Γ ||-<l> F ≅ F' | fst RFG]< wl > × W[Γ ,, F ||-<l> G ≅ G' | snd RFG]< wl >.
  Proof.
    intros [d Hd] ; split.
    - exists (DTree_fusion _ (WPol wl Γ l F G PFG) d).
      intros wl' HoF Hover.
      pose proof (Ho := over_tree_fusion_l Hover).
      pose proof (Ho' := over_tree_fusion_r Hover).
      specialize (Hd _ Ho Ho') as [RFF' ? RGG'].
      destruct RFG; escape. 
      rewrite <- (wk_id_ren_on Γ F'); irrelevance0.
      2: unshelve eapply RFF'; [ now eapply wfLCon_le_id | eapply wfc_Ltrans]. 
      1: now apply wk_id_ren_on.
      1: now eapply over_tree_le.
      Wescape ; now gen_typing.      
    - destruct RFG as [HF HG] ; cbn.
      revert HG ; pattern wl.
      unshelve eapply split_to_over_tree ; [exact (DTree_fusion _ (WPol wl Γ l F G PFG) d) | | ].
      + intros ; unshelve eapply EqSplit' ; eauto.
        1: intros m; eapply WLtrans ; [ | eassumption].
        now eapply LCon_le_step, wfLCon_le_id.
      + intros wl'  Hover HG.
        pose proof (Ho := over_tree_fusion_l Hover).
        pose proof (Ho' := over_tree_fusion_r Hover).
        specialize (Hd _ Ho Ho') as [RFF' ? RGG'].
        destruct PFG as [d' Hd'] ; cbn in *.
        replace G' with G'[tRel 0 .: @wk1 Γ F >> tRel].
        2: bsimpl; rewrite scons_eta'; now asimpl.
        pose (PFG := Hd' _ Ho).
        unshelve econstructor ; intros.
        1: eapply DTree_fusion ; [eapply (PolyRedPack.posTree PFG (wk1 F)) | eapply posTree].
        1,2: eapply var0 ; tea.
        1: now bsimpl.
        1: Wescape ; eapply wft_Ltrans ; [ now eapply over_tree_le | eassumption].
        2: Wescape ; eapply wft_Ltrans ; [ now eapply over_tree_le | eassumption].
        2: irrelevance0.
        3: eapply RGG'. 
        2: bsimpl; rewrite scons_eta'; now asimpl.
        Unshelve.
        5: now eapply wk1.
        1: now bsimpl.
        1: eapply over_tree_fusion_r ; exact Hover'.
        1,3: now eapply wfLCon_le_id.
        1,2: eapply wfc_Ltrans ; [now eapply over_tree_le | Wescape ; now gen_typing].
        eapply over_tree_fusion_l ; exact Hover'. 
  Qed.
    

  Lemma polyRedSubst {wl Γ l A B t} (PAB : PolyRed wl Γ l A B) 
    (Rt : forall Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
      [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ f wfΔ ]< wl' >)
    (Rtext : forall Δ wl' a b (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), 
      [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
      [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
      [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
      [Δ ||-<l> t[a .: ρ >> tRel] ≅ t[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ f wfΔ ]< wl' >)
    : PolyRed wl Γ l A B[t]⇑.
  Proof.
    destruct PAB.
    unshelve econstructor ; [tea | | | | tea |tea | ] ; cbn in *.
    1:{ intros ; eapply (posTree Δ k' t[a .: ρ >> tRel] ρ f).
      1: eapply Rt ; irrelevanceRefl ; eassumption. }
    1:{ intros; rewrite liftSubst_scons_eq.
        pose proof (X1 := over_tree_le Ho).
        pose proof (X2 := wfLCon_le_trans X1 f).
        unshelve eapply posRed ; [ | exact f | eassumption |.. ].
        1: eapply Rt ; irrelevanceRefl ; eassumption.
        exact Ho. }
    2:{ pattern wl ; eapply split_to_over_tree.
        + intros ; now eapply wft_ϝ.
        + intros wl' Hover.
          unshelve epose proof (posRed _ t _ (@wk1 Γ A) (wfLCon_le_id _) _ _ _ Hover).
          * escape; gen_typing.
          * replace t with t[tRel 0 .: @wk1 Γ A >> tRel].
            2:{ bsimpl; rewrite scons_eta'; now asimpl. }
            eapply Rt.
            eapply var0; tea; now rewrite wk1_ren_on.
          * escape.
            replace (B[_]) with B[t .: @wk1 Γ A >> tRel]; tea.
            now setoid_rewrite wk1_ren. }
    2:{ intros; irrelevance0; rewrite liftSubst_scons_eq;[reflexivity|].
        unshelve eapply posExt ; cbn in *.
        2,3: eassumption.
        1,3: eapply Rt ; now irrelevanceRefl.
        2: eapply Rtext ; now irrelevanceRefl.
        1,2: eassumption.
        exact Hoeq. }
  Qed.

  Lemma polyRedEqSubst {Γ wl l A B t u} (PAB : PolyRed wl Γ l A B) 
    (Rt : forall Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), 
        [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
        [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ f wfΔ ]< wl' >)
    (Ru : forall Δ wl' a (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), 
        [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
        [Δ ||-<l> u[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ f wfΔ ]< wl' >)
    (Rtu : forall Δ wl' a b (ρ : Δ ≤ Γ) (f : wl' ≤ε wl) (wfΔ : [|-Δ]< wl' >), 
        [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
        [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
        [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ f wfΔ]< wl' > ->
        [Δ ||-<l> t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ f wfΔ ]< wl' >)
    (PABt : PolyRed wl Γ l A B[t]⇑)
    : PolyRedEq PABt A B[u]⇑.
  Proof.
    unshelve econstructor.
    2: intros; now eapply reflLRTyEq.
    2:{ intros; irrelevance0; rewrite liftSubst_scons_eq; [reflexivity|].
        unshelve eapply PolyRed.posExt; cycle 1.
        4,5: eassumption.
        3: eapply Rt; now irrelevanceRefl.
        2: eapply Ru; now irrelevanceRefl.
        2: eapply Rtu; try eapply reflLRTmEq; now irrelevanceRefl.
        3: eapply over_tree_fusion_r ; exact Ho'.
        1: do 2 eapply over_tree_fusion_l ; exact Ho'.
        eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho'.
    }
  Qed.
  
  Context {l wl Γ F G} (VΓ : [||-v Γ]< wl >)
    (VF : [Γ ||-v< l > F | VΓ ]< wl >)
    (VG : [Γ ,, F ||-v< l > G | validSnoc' VΓ VF]< wl >).

  Context {Δ σ wl' f} (tΔ : [ |-[ ta ] Δ]< wl' >) (Vσ : [VΓ | Δ ||-v σ : _ | tΔ | f]< wl >).
  
  Lemma substPolyRed : WPolyRed wl' Δ l F[σ] G[up_term_term σ].
  Proof.
    pose proof (Vuσ := liftSubstS' VF Vσ).
    instValid Vσ; instValid Vuσ; Wescape.
    exists (DTree_fusion _ (WT _ RVF) (WT _ RVG)).
    intros wl'' Hover.
    pose proof (HoF := over_tree_fusion_l Hover).
    pose proof (HoG := over_tree_fusion_r Hover).
    unshelve econstructor.
    5,6: now eapply wft_Ltrans ; [ eapply over_tree_le | eassumption].
    1: intros; eapply wk ; [eassumption | eapply RVF, le_over_tree ; eassumption].
    2:{ cbn; intros ??? ρ f' wfΔ' ha wl''' Hover'.
        rewrite eq_subst_2.
        unshelve eapply (validTy VG).
        3: eassumption.
        1: exact (f' •ε (over_tree_le Hover) •ε f).
        eapply consWkSubstS.
        1: eapply subst_Ltrans ; eassumption.
        1: now eapply TmLogtoW.
        exact Hover'.
    }
    2:{ cbn; intros ???? ρ f' wfΔ' ha hb hab wl''' Hoa Hob Hoeq.
      irrelevance0; rewrite eq_subst_2.
      1: reflexivity.
      eapply (validTyExt VG).
      exact Hoeq.
    }
    Unshelve.
    2: exact Hoa.
    2:eapply (consWkSubstS VF ρ) ; [ eapply subst_Ltrans ; eassumption | ].
    2: now eapply TmLogtoW.
    2: unshelve eapply (consWkSubstSEq' VF _ _ ρ).
    3: now eapply TmEqLogtoW.
    2: now eapply eqsubst_Ltrans, (reflSubst _ _ _ Vσ).
    Unshelve.
    all: eapply wfc_Ltrans ; [| eassumption].
    all: exact (f' •ε over_tree_le Hover).
  Qed. 

  Lemma substEqPolyRedEq {F' G'} (VF' : [Γ ||-v< l > F' | VΓ ]< wl >)
    (VG' : [Γ ,, F' ||-v< l > G' | validSnoc' VΓ VF']< wl >)
    (VFF' : [Γ ||-v< l > F ≅ F' | VΓ | VF]< wl >)
    (VGG' : [Γ ,, F ||-v< l > G ≅ G' | validSnoc' VΓ VF | VG]< wl >)
    : WPolyRedEq substPolyRed F'[σ] G'[up_term_term σ].
  Proof.
    instValid Vσ.
    unshelve econstructor ; [ | unshelve econstructor].
    3:{ intros; irrelevanceRefl.
        unshelve eapply wkEq ; [eassumption | eapply RVF | eapply RVFF' ].
        all: eapply le_over_tree ; [eassumption | ].
        eapply over_tree_fusion_l ; exact Ho'.
        eapply over_tree_fusion_r ; exact Ho'.
    }
    2:{ intros ??? ρ f' wfΔ' ha wl'' Hoa Hoeq.
        irrelevance0; rewrite eq_subst_2.
        1: reflexivity.
        unshelve epose proof (Vabwkσ := consWkSubstSEq' VF _ _ ρ wfΔ' _).
        7: unshelve eapply subst_Ltrans ; [ .. | exact Vσ].
        6: unshelve eapply eqsubst_Ltrans ; exact (reflSubst _ _ _ Vσ).
        6: eapply TmLogtoW ; exact ha.
        2: eapply wfc_Ltrans ; [ | eassumption ].
        2,3: exact (f' •ε over_tree_le Ho).
        2: unshelve eapply validTyEq ; [ | | | eassumption | ..].
        4,7: eassumption.
        2: exact (f' •ε over_tree_le Ho •ε f).
        2: eapply consWkSubstS ; [ eapply subst_Ltrans ; eassumption | ].
        2: eapply TmLogtoW ; exact ha.
        2: eapply over_tree_fusion_l ; exact Hoeq.
        2: eapply over_tree_fusion_r ; exact Hoeq.
        Unshelve.
        1: eassumption.
        eapply wfc_Ltrans ; [ exact (f' •ε over_tree_le Ho) | eassumption ].
    }
Qed.        

  Context {σ'} (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ | f]< wl >) (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ| f]< wl >).

  Lemma substPolyRedEq : WPolyRedEq substPolyRed F[σ'] G[up_term_term σ'].
  Proof.
    instAllValid Vσ Vσ' Vσσ'.
    econstructor ; intros ; unshelve econstructor.
    2:{ intros; irrelevanceRefl ; eapply wkEq, REVF.
        eapply le_over_tree, over_tree_fusion_r ; [ eassumption | exact Ho'].
    }
    2:{ intros ??? ρ f' wfΔ' ha wl'' Ho'' Hoeq.
        irrelevance0; rewrite eq_subst_2.
        1: reflexivity.
        unshelve eapply (validTyExt VG).
        3: eassumption.
        1: exact (f' •ε over_tree_le Ho •ε f).
        2: eapply over_tree_fusion_l ; exact Hoeq.
        4: eapply over_tree_fusion_r ; exact Hoeq.
        1,2: eapply consWkSubstS.
        1,3: unshelve eapply subst_Ltrans ; [ .. | exact Vσ + exact Vσ'].
        2: eapply WLRTmRedConv.
        1,3: eapply TmLogtoW ; exact ha.
        1: Wirrelevance0 ; [reflexivity | eapply WwkEq_Ltrans ; eassumption].
        unshelve eapply (consWkSubstSEq' VF).
        1:unshelve eapply eqsubst_Ltrans ; exact Vσσ'.
        eapply WreflLRTmEq, TmLogtoW ; exact ha.
        Unshelve.
        1,8: eassumption.
        1: eapply over_tree_fusion_l, le_over_tree ; [ eauto | exact Ho'].
        1,2: eapply wfc_Ltrans ; [ | eassumption].
        3: eapply Wwk_Ltrans ; [ | eassumption | eassumption].
        all: exact (f' •ε over_tree_le Ho).
    }
Qed.        

End PolyValidity.


