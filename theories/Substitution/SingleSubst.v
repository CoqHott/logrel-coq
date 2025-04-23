From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Split Weakening Neutral Monotonicity Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion.

Set Universe Polymorphism.

Section SingleSubst.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma singleSubstComm G t σ : G[t..][σ] = G[t[σ] .: σ].
Proof. now asimpl. Qed.


Lemma substS {wl Γ F G t l} {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VG : [Γ,, F ||-v<l> G | validSnoc' VΓ VF]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) :
  [Γ ||-v<l> G[t..] | VΓ]< wl >.
Proof.
  opector; intros.
  1: rewrite singleSubstComm.
  - unshelve eapply validTy. 3,4,5:  tea.
    3: eassumption.
    now eapply consSubstSvalid.
  - rewrite (singleSubstComm G t σ').
    Wirrelevance0. 1: symmetry; apply singleSubstComm.
    eapply validTyExt.
    1: eapply consSubstS; now  eapply validTm.
    now eapply consSubstSEqvalid.
    Unshelve. all: eassumption.
Qed.

Lemma substSEq {wl Γ F F' G G' t t' l} {VΓ : [||-v Γ]< wl >} 
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  {VF' : [Γ ||-v<l> F' | VΓ]< wl >}
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF]< wl >)
  (VΓF := validSnoc' VΓ VF)
  (VΓF' := validSnoc' VΓ VF')
  {VG : [Γ,, F ||-v<l> G | VΓF]< wl >}
  (VG' : [Γ,, F' ||-v<l> G' | VΓF']< wl >)
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >)
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF']< wl >)
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]< wl >)
  (VGt := substS VG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ | VGt]< wl >.
Proof.
  constructor; intros.
  assert (VtF' : [Γ ||-v<l> t : F' | VΓ | VF']< wl >) by now eapply conv.
  pose proof (consSubstSvalid Vσ Vt').
  pose proof (consSubstSvalid Vσ VtF').
  rewrite (singleSubstComm G' t' σ) ; Wirrelevance0.
  1: symmetry; apply singleSubstComm.
  eapply WtransEq.
  - unshelve now eapply validTyEq.
    3: now eapply consSubstSvalid.
  - eapply validTyExt; tea.
    unshelve econstructor.
    1: eapply reflSubst.
    eapply validTmEq.
    now eapply convEq.
    Unshelve. all: tea.
Qed.



Lemma substSTm {wl Γ F G t f l} {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VΓF := validSnoc' VΓ VF)
  {VG : [Γ,, F ||-v<l> G | VΓF]< wl >}
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) 
  (Vf : [Γ ,, F ||-v<l> f : G | VΓF | VG]< wl >)
  (VGt := substS VG Vt) :
  [Γ ||-v<l> f[t..] : G[t..] | VΓ | VGt]< wl >.
Proof.
  constructor; intros; rewrite !singleSubstComm; Wirrelevance0. 
  1,3: symmetry; apply singleSubstComm.
  - now eapply validTm.
  - eapply validTmExt; tea.
    1: now apply consSubstSvalid.
    now apply consSubstSEqvalid.
    Unshelve. 1,2,4: eassumption.
    now apply consSubstSvalid.
Qed.

Lemma substSTmEq {wl Γ F F' G G' t t' h h' l} (VΓ : [||-v Γ]< wl >) 
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VF' : [Γ ||-v<l> F' | VΓ]< wl >)
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF]< wl >)
  (VΓF := validSnoc' VΓ VF)
  (VΓF' := validSnoc' VΓ VF')
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VG' : [Γ,, F' ||-v<l> G' | VΓF']< wl >)
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >)
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF']< wl >)
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]< wl >) 
  (Vh : [Γ ,, F ||-v<l> h : G | VΓF | VG]< wl >)
  (Vh' : [Γ ,, F' ||-v<l> h' : G' | VΓF' | VG']< wl >)
  (Vhh' : [Γ ,, F ||-v<l> h ≅ h' : G | VΓF | VG]< wl >) :
  [Γ ||-v<l> h[t..] ≅ h'[t'..] : G[t..] | VΓ | substS VG Vt]< wl >.
Proof.
  constructor; intros; rewrite !singleSubstComm; Wirrelevance0. 
  1: symmetry; apply singleSubstComm.
  eapply WtransEqTerm.
  + unshelve now eapply validTmEq.
    3: now eapply consSubstSvalid.
  + assert (Vσt : [Δ ||-v (t[σ] .: σ) : _ | VΓF' | wfΔ | f]< wl >)
     by (eapply consSubstSvalid; tea; now eapply conv).
    assert (Vσt' : [Δ ||-v (t'[σ] .: σ) : _ | VΓF' | wfΔ | f]< wl >)
     by (eapply consSubstSvalid; tea; now eapply conv).
    assert (Vσtσt' : [Δ ||-v (t[σ] .: σ) ≅ (t'[σ] .: σ) : _ | VΓF' | wfΔ | Vσt | f]< wl >).
    1:{
      constructor.
      - fsimpl; epose (reflSubst _ _ _ Vσ) ; now eapply irrelevanceSubstEq.
      - fsimpl; eapply validTmEq. now eapply convEq.
    }
    eapply WLRTmEqRedConv.
    2: eapply (validTmExt Vh' _ _ Vσt Vσt' Vσtσt').
    eapply WLRTyEqSym. now eapply validTyEq.
    Unshelve. 3: now eapply consSubstSvalid.
Qed.

(* Skipping a series of lemmas on single substitution of a weakened term *)


Lemma liftSubstComm G t σ : G[t]⇑[σ] = G[t[σ] .: ↑ >> σ].
Proof. now bsimpl. Qed.


Lemma substLiftS {wl Γ F G t l} (VΓ : [||-v Γ]< wl >)
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) :
  [Γ ,, F ||-v<l> G[t]⇑ | VΓF]< wl >.
Proof.
  assert (h : forall Δ σ wl' f (wfΔ: [|- Δ]< wl' >)
    (vσ: [VΓF | Δ ||-v σ : Γ,, F | wfΔ | f]< wl >),
    [VΓF | Δ ||-v (t[σ] .: ↑ >> σ) : _ | wfΔ | f]< wl >).
  1:{
    unshelve econstructor.
    + asimpl; now eapply projT1.
    + cbn. Wirrelevance0.
      2: now eapply validTm.
      now bsimpl.
  }
  opector; intros.
  - rewrite liftSubstComm.
    unshelve eapply validTy; cycle 2; tea; now eapply h.
  - rewrite (liftSubstComm _ _ σ').
    Wirrelevance0.
    2: unshelve eapply validTyExt.
    rewrite (liftSubstComm _ _ σ) ; reflexivity.
    7: now eapply h.
    2: now eapply (h _ _ _ _ _ vσ').
    1: tea.
    constructor.
    + fsimpl; eapply irrelevanceSubstEq; exact (fst vσσ').
    + cbn. Wirrelevance0.
      2: now eapply validTmExt.
      now bsimpl.
      Unshelve. all:tea.
Qed.

Lemma substLiftSEq {wl Γ F G G' t l} (VΓ : [||-v Γ]< wl >)
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VG' : [Γ,, F ||-v<l> G' | VΓF]< wl >)
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t]⇑ | VΓF | substLiftS _ VF VG Vt]< wl >.
Proof.
  constructor; intros.
  assert (Vσt : [Δ ||-v (t[σ] .: ↑ >> σ) : _ | VΓF | wfΔ | f]< wl >). 1:{
    unshelve econstructor.
    + fsimpl. now eapply projT1.
    + fsimpl. instValid Vσ. Wirrelevance.
  }
  instValid Vσt. Wirrelevance0.
  2:{ rewrite (liftSubstComm _ _ σ). eassumption. }
  now bsimpl.
Qed.

Lemma substLiftSEq' {wl Γ F G G' t t' l} (VΓ : [||-v Γ]< wl >)
  (VF : [Γ ||-v<l> F | VΓ]< wl >)
  (VΓF := validSnoc' VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF]< wl >)
  (VG' : [Γ,, F ||-v<l> G' | VΓF]< wl >)
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG]< wl >)
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) 
  (Vt' : [Γ,, F ||-v<l> t' : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >)
  (Vtt' : [Γ,, F ||-v<l> t ≅ t' : F⟨@wk1 Γ F⟩ | VΓF | VF']< wl >) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t']⇑ | VΓF | substLiftS _ VF VG Vt]< wl >.
Proof.
  eapply transValidTyEq.
  1: eapply substLiftSEq; [| exact VGeq]; tea.
  constructor; intros; Wirrelevance0; rewrite liftSubstComm ; [reflexivity|].
  instValid Vσ.
  eapply validTyExt.
  + unshelve eapply consSubstS.
    6: now eapply projT1.
    3: exact VF. 
    Wirrelevance.
  + unshelve eapply consSubstSEq'.
    1: now eapply projT1.
    1,3: Wirrelevance.
    eapply reflSubst.
    Unshelve. 3: tea. now eapply substLiftS.
Qed.


Lemma singleSubstPoly {wl Γ F G t l lF}
  (RFG : PolyRed wl Γ l F G)
  {RF : W[Γ ||-<lF> F]< wl >}
  (Rt : W[Γ ||-<lF> t : F | RF]< wl >) :
  W[Γ ||-<l> G[t..]]< wl >.
Proof.
  replace G[t..] with G[t .: wk_id (Γ:=Γ) >> tRel] by now bsimpl.
  pattern wl ; unshelve eapply split_to_over_tree ; [ | intros ??? ; exact Split | ].
  - eapply DTree_fusion.
    + exact (WT _ RF).
    + exact (WTTm _ Rt).
  - intros wl' Hover.
    econstructor ; intros wl'' Hover'.
    unshelve eapply (PolyRed.posRed RFG).
    5: exact Hover'.
    2: eapply wfc_Ltrans ; [now eapply over_tree_le | ] ; Wescape; now gen_typing.
    1: now eapply over_tree_le.
    irrelevance0 ; [ | now eapply Rt, over_tree_fusion_r].
    now bsimpl.
    Unshelve.
    now eapply over_tree_fusion_l.
Qed.


Lemma singleSubstΠ1 {wl Γ F G t l lF}
  (ΠFG : W[Γ ||-<l> tProd F G]< wl >)
  {RF : W[Γ ||-<lF> F]< wl >}
  (Rt : W[Γ ||-<lF> t : F | RF]< wl >) :
  W[Γ ||-<l> G[t..]]< wl >.
Proof.
  pattern wl ; unshelve eapply split_to_over_tree ; [ | intros ??? ; exact Split | ].
  1: exact (WT _ ΠFG).
  intros wl' Hover.
  eapply singleSubstPoly; tea.
  - pose (Hyp:= WRed _ ΠFG _ Hover).
    now eapply (ParamRedTy.polyRed (normRedΠ0 (invLRΠ Hyp))).
  - now eapply WTm_Ltrans.
    Unshelve.
    now eapply over_tree_le.
Qed.


Lemma singleSubstΣ1 {wl Γ F G t l lF}
  (ΠFG : W[Γ ||-<l> tSig F G]< wl >)
  {RF : W[Γ ||-<lF> F]< wl >}
  (Rt : W[Γ ||-<lF> t : F | RF]< wl >) :
  W[Γ ||-<l> G[t..]]< wl >.
Proof.
  pattern wl ; unshelve eapply split_to_over_tree ; [ | intros ??? ; exact Split | ].
  1: exact (WT _ ΠFG).
  intros wl' Hover.
  eapply singleSubstPoly; tea.
  - pose (Hyp:= WRed _ ΠFG _ Hover).
    now eapply (ParamRedTy.polyRed (normRedΣ0 (invLRΣ Hyp))).
  - now eapply WTm_Ltrans.
    Unshelve.
    now eapply over_tree_le.
Qed.

Lemma singleSubstPoly2 {wl Γ F F' G G' t t' l lF lF'}
  {RFG : PolyRed wl Γ l F G}
  (RFGeq : PolyRedEq RFG F' G')
  {RF : [Γ ||-<lF> F]< wl >}
  {RF' : [Γ ||-<lF'> F']< wl >}
  (Rt : [Γ ||-<lF> t : F | RF]< wl >) 
  (Rt' : [Γ ||-<lF'> t' : F' | RF']< wl >) 
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF]< wl >)
  (RGt : W[Γ ||-<lF> G[t..]]< wl >)
  (RGt' : W[Γ ||-<lF'> G'[t'..]]< wl >) :
  W[Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ]< wl >.
Proof.
  assert (wfΓ : [|-Γ]< wl >) by (escape ; gen_typing).
  assert [Γ ||-<l> t' : F⟨wk_id (Γ:=Γ)⟩ | PolyRed.shpRed RFG wk_id (wfLCon_le_id _) wfΓ]< wl >.
  {
    eapply LRTmRedConv; tea.
    eapply LRTyEqSym. 
    replace F' with F'⟨wk_id (Γ := Γ)⟩ by now bsimpl.
    eapply (PolyRedEq.shpRed RFGeq).
  }
  eapply WtransEq.
  2: (replace G'[t'..] with G'[t' .: wk_id (Γ:=Γ) >> tRel] by now bsimpl).
  2: econstructor ; intros ; irrelevance0 ; [ | unshelve eapply (PolyRedEq.posRed RFGeq wk_id)].
  econstructor ; intros ; irrelevance0 ; [ | unshelve eapply (PolyRed.posExt (a:= t) RFG wk_id)].
  1: now bsimpl.
  3,14: eassumption.
  1,10 : now eapply wfLCon_le_id.
  2,10: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Hover'.
  5: eapply over_tree_fusion_l, over_tree_fusion_r ; exact Hover'.
  5: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Hover'.
  7: eapply over_tree_fusion_r, over_tree_fusion_r ; exact Hover'.
  3,6: eassumption.
  1,2: irrelevance0 ; [ | eassumption] ; now bsimpl.
  reflexivity.
  Unshelve.
  1: now eapply wfLCon_le_id.
  1: assumption.
  3-5: now econstructor.
  2: econstructor ; intros.
  2: unshelve eapply (PolyRed.posRed RFG).
  4,5: eassumption.
Qed.

Lemma singleSubstΠ2 {wl Γ F F' G G' t t' l lF lF'}
  {ΠFG : W[Γ ||-<l> tProd F G]< wl >}
  (ΠFGeq : W[Γ ||-<l> tProd F G ≅ tProd F' G' | ΠFG]< wl >)
  {RF : W[Γ ||-<lF> F]< wl >}
  {RF' : W[Γ ||-<lF'> F']< wl >}
  (Rt : W[Γ ||-<lF> t : F | RF]< wl >) 
  (Rt' : W[Γ ||-<lF'> t' : F' | RF']< wl >) 
  (Rteq : W[Γ ||-<lF> t ≅ t' : F | RF]< wl >)
  (RGt : W[Γ ||-<lF> G[t..]]< wl >)
  (RGt' : W[Γ ||-<lF'> G'[t'..]]< wl >) :
  W[Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ]< wl >.
Proof.
  revert RGt RGt'.
  pattern wl ; unshelve eapply split_to_over_tree.
  - do 2 eapply DTree_fusion ; [do 2 eapply DTree_fusion | ..].
    + now eapply ΠFG.
    + now eapply ΠFGeq.
    + now eapply RF.
    + now eapply RF'.
    + now eapply Rt.
    + now eapply Rt'.
    + now eapply Rteq.
  - intros wl'' n ne Hl Hr RGt'.
    unshelve eapply EqSplit' ; [ | | | intros m ; eapply Hl].
    1: intros m.
    all: eapply WLtrans ; [ | eassumption].
    all: now eapply LCon_le_step, wfLCon_le_id.
  - cbn ; intros wl' Hover RGt RGt'.
    eapply singleSubstPoly2; tea.
    + unshelve epose (hΠ := normRedΠ0 (invLRΠ (WRed _ ΠFG _ _))).
      2: now do 4 eapply over_tree_fusion_l.
      assert (heq : [Γ ||-<l> tProd F G ≅ tProd F' G' | LRPi' hΠ]< wl' >).
      { irrelevanceRefl ; unshelve eapply ΠFGeq.
        1: now do 4 eapply over_tree_fusion_l.
        1: eapply over_tree_fusion_r ; now do 3 eapply over_tree_fusion_l.
      }
      destruct heq as [?? red' ?? polyRed]; cbn in *.
      assert (h' :=redtywf_whnf red' whnf_tProd).
      symmetry in h'; injection h'; clear h'; intros ;  subst.
      exact polyRed.
    + unshelve eapply Rt.
      * eapply over_tree_fusion_l, over_tree_fusion_r ; now do 2 eapply over_tree_fusion_l.
      * now eapply over_tree_fusion_r, over_tree_fusion_l.
    + unshelve eapply Rt'.
      * do 2 eapply over_tree_fusion_r ; now do 2 eapply over_tree_fusion_l.
      * now eapply over_tree_fusion_l, over_tree_fusion_r.
    + unshelve eapply Rteq.
      now do 2 eapply over_tree_fusion_r.
Qed.
      
      
Lemma substSΠaux {wl Γ F G t l} 
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >)
  (Δ : context) (σ : nat -> term) wl' f
  (wfΔ : [ |-[ ta ] Δ]< wl' >) (vσ : [VΓ | Δ ||-v σ : Γ | wfΔ | f]< wl >) :
  W[Δ ||-< l > G[up_term_term σ][t[σ]..]]< wl' >.
Proof.
  eapply singleSubstΠ1.
  unshelve eapply (validTy VΠFG); tea.
  now eapply validTm.
  Unshelve. all: eassumption.
Qed.

Lemma singleSubstComm' G t σ : G[t..][σ] = G[up_term_term σ][t[σ]..].
Proof. now asimpl. Qed.

Lemma substSΠ {wl Γ F G t l} 
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) :
  [Γ ||-v<l> G[t..] | VΓ]< wl >.
Proof.
  opector; intros.
  - rewrite singleSubstComm'; now eapply substSΠaux.
  - rewrite (singleSubstComm' _ t σ').
    Wirrelevance0. 1: symmetry; apply singleSubstComm'.
    eapply singleSubstΠ2.
    5: now eapply substSΠaux.
    1: now eapply (validTyExt VΠFG).
    1,2: now eapply validTm.
    1: now eapply validTmExt.
    Unshelve. all: tea.
    now eapply substSΠaux.
Qed.

Lemma substSΠeq {wl Γ F F' G G' t u l} 
  {VΓ : [||-v Γ]< wl >}
  {VF : [Γ ||-v<l> F | VΓ]< wl >}
  {VF' : [Γ ||-v<l> F' | VΓ]< wl >}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]< wl >}
  (VΠFG' : [Γ ||-v<l> tProd F' G' | VΓ]< wl >)
  (VΠFGeq : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ | VΠFG]< wl >)
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]< wl >) 
  (Vu : [Γ ||-v<l> u : F' | VΓ | VF']< wl >) 
  (Vtu : [Γ ||-v<l> t ≅ u : F | VΓ | VF]< wl >) 
  (VGt := substSΠ VΠFG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[u..] | VΓ | VGt]< wl >.
Proof.
  constructor; intros.
  rewrite (singleSubstComm' G').
  Wirrelevance0.
  1: symmetry; apply singleSubstComm'.
  eapply singleSubstΠ2.
  1: now eapply (validTyEq VΠFGeq).
  3: now eapply validTmEq.
  1,2: now eapply validTm.
  now eapply substSΠaux.
  Unshelve. all: tea.
  now eapply substSΠaux.
Qed.


End SingleSubst.
