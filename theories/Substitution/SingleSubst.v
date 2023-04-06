From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion.

Set Universe Polymorphism.

Section SingleSubst.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma singleSubstComm G t σ : G[t..][σ] = G[t[σ] .: σ].
Proof. now asimpl. Qed.


Lemma substS {Γ F G t l} {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VG : [Γ,, F ||-v<l> G | validSnoc VΓ VF])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] | VΓ].
Proof.
  opector; intros; rewrite singleSubstComm.
  - unshelve eapply validTy. 3,4:  tea.
    now eapply consSubstSvalid.
  - irrelevance0. 1: symmetry; apply singleSubstComm.
    eapply validTyExt.
    1: eapply consSubstS; now  eapply validTm.
    now eapply consSubstSEqvalid.
    Unshelve. all: eassumption.
Qed.

Lemma substSEq {Γ F F' G G' t t' l} {VΓ : [||-v Γ]} 
  {VF : [Γ ||-v<l> F | VΓ]}
  {VF' : [Γ ||-v<l> F' | VΓ]}
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VΓF := validSnoc VΓ VF)
  (VΓF' := validSnoc VΓ VF')
  {VG : [Γ,, F ||-v<l> G | VΓF]}
  (VG' : [Γ,, F' ||-v<l> G' | VΓF'])
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF'])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF])
  (VGt := substS VG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ | VGt].
Proof.
  constructor; intros.
  assert (VtF' : [Γ ||-v<l> t : F' | VΓ | VF']) by now eapply conv.
  pose proof (consSubstSvalid _ _ Vσ _ Vt').
  pose proof (consSubstSvalid _ _ Vσ _ VtF').
  rewrite singleSubstComm; irrelevance0.
  1: symmetry; apply singleSubstComm.
  eapply transEq.
  - unshelve now eapply validTyEq.
    2: now eapply consSubstSvalid.
  - eapply validTyExt; tea.
    unshelve econstructor.
    1: eapply reflSubst.
    eapply validTmEq.
    now eapply convEq.
    Unshelve. all: tea.
    now eapply validTy.
Qed.




Lemma substSTm {Γ F G t f l} {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ,, F ||-v<l> G | VΓF]}
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) 
  (Vf : [Γ ,, F ||-v<l> f : G | VΓF | VG])
  (VGt := substS VG Vt) :
  [Γ ||-v<l> f[t..] : G[t..] | VΓ | VGt].
Proof.
  constructor; intros; rewrite !singleSubstComm; irrelevance0. 
  1,3: symmetry; apply singleSubstComm.
  - now eapply validTm.
  - eapply validTmExt; tea.
    1: now apply consSubstSvalid.
    now apply consSubstSEqvalid.
    Unshelve. 1,3: eassumption.
    now apply consSubstSvalid.
Qed.

Lemma substSTmEq {Γ F F' G G' t t' f f' l} (VΓ : [||-v Γ]) 
  (VF : [Γ ||-v<l> F | VΓ])
  (VF' : [Γ ||-v<l> F' | VΓ])
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VΓF := validSnoc VΓ VF)
  (VΓF' := validSnoc VΓ VF')
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VG' : [Γ,, F' ||-v<l> G' | VΓF'])
  (VGG' : [Γ ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF'])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) 
  (Vf : [Γ ,, F ||-v<l> f : G | VΓF | VG])
  (Vf' : [Γ ,, F' ||-v<l> f' : G' | VΓF' | VG'])
  (Vff' : [Γ ,, F ||-v<l> f ≅ f' : G | VΓF | VG]) :
  [Γ ||-v<l> f[t..] ≅ f'[t'..] : G[t..] | VΓ | substS VG Vt].
Proof.
  constructor; intros; rewrite !singleSubstComm; irrelevance0. 
  1: symmetry; apply singleSubstComm.
  eapply transEqTerm.
  + unshelve now eapply validTmEq.
    2: now eapply consSubstSvalid.
  + assert (Vσt : [Δ ||-v (t[σ] .: σ) : _ | VΓF' | wfΔ])
     by (eapply consValid; tea; now eapply conv).
    assert (Vσt' : [Δ ||-v (t'[σ] .: σ) : _ | VΓF' | wfΔ])
     by (eapply consValid; tea; now eapply conv).
    assert (Vσtσt' : [Δ ||-v (t[σ] .: σ) ≅ (t'[σ] .: σ) : _ | VΓF' | wfΔ | Vσt]).
    1:{
      constructor.
      - bsimpl; epose (reflSubst _  _ Vσ); now eapply irrelevanceSubstEq.
      - bsimpl; eapply validTmEq. now eapply convEq.
    }
    eapply LRTmEqRedConv.
    2: eapply (validTmExt Vf' _ Vσt Vσt' Vσtσt').
    eapply LRTyEqSym. now eapply validTyEq.
    Unshelve. 2: now eapply consValid.
Qed.

(* Skipping a series of lemmas on single substitution of a weakened term *)


Lemma liftSubstComm G t σ : G[t]⇑[σ] = G[t[σ] .: ↑ >> σ].
Proof. now bsimpl. Qed.


Lemma substLiftS {Γ F G t l} (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ | VΓF].
Proof.
  assert (h : forall Δ σ (wfΔ: [|- Δ])
    (vσ: [VΓF | Δ ||-v σ : Γ,, F | wfΔ]),
    [VΓF | Δ ||-v (t[σ] .: ↑ >> σ) : _ | wfΔ ]).
  1:{
    unshelve econstructor.
    + asimpl; now eapply validTail.
    + cbn. irrelevance0.
      2: now eapply validTm.
      now bsimpl.
  }
  opector; intros; rewrite liftSubstComm.
  - unshelve eapply validTy; cycle 2; tea; now eapply h.
  - irrelevance0.
    2: unshelve eapply validTyExt.
    8: now eapply h.
    4: now eapply (h _ _  _ vσ).
    1: now bsimpl.
    1: tea.
    constructor.
    + asimpl; eapply irrelevanceSubstEq; now eapply eqTail.
    + cbn. irrelevance0.
      2: now eapply validTmExt.
      now bsimpl.
      Unshelve. all:tea.
Qed.

Lemma substLiftSEq {Γ F G G' t l} (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G | VΓF])
  (VG' : [Γ,, F ||-v<l> G' | VΓF])
  (VGeq : [Γ,, F ||-v<l> G ≅ G' | VΓF | VG])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t]⇑ | VΓF | substLiftS _ VF VG Vt].
Proof.
  constructor; intros; rewrite liftSubstComm.
  assert (Vσt : [Δ ||-v (t[σ] .: ↑ >> σ) : _ | VΓF | wfΔ ]). 1:{
    unshelve econstructor.
    + bsimpl. now eapply validTail.
    + bsimpl. instValid Vσ. irrelevance.
  }
  instValid Vσt. irrelevance.
Qed.

Lemma singleSubstPoly {Γ F G t l lF}
  (RFG : PolyRed Γ l F G)
  {RF : [Γ ||-<lF> F]}
  (Rt : [Γ ||-<lF> t : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  replace G[t..] with G[t .: wk_id (Γ:=Γ) >> tRel] by now bsimpl.
  unshelve eapply (PolyRed.posRed RFG).
  1: escape; gen_typing.
  irrelevance0; tea.
  now bsimpl.
Qed.

Lemma singleSubstΠ1 {Γ F G t l lF}
  (ΠFG : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<lF> F]}
  (Rt : [Γ ||-<lF> t : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  eapply singleSubstPoly; tea.
  eapply (ParamRedTy.polyRed (normRedΠ0 (invLRΠ ΠFG))).
Qed.

Lemma singleSubstΣ1 {Γ F G t l lF}
  (ΠFG : [Γ ||-<l> tSig F G])
  {RF : [Γ ||-<lF> F]}
  (Rt : [Γ ||-<lF> t : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  eapply singleSubstPoly; tea.
  eapply (ParamRedTy.polyRed (normRedΣ0 (invLRΣ ΠFG))).
Qed.

Lemma singleSubstPoly2 {Γ F F' G G' t t' l lF lF'}
  {RFG : PolyRed Γ l F G}
  (RFGeq : PolyRedEq RFG F' G')
  {RF : [Γ ||-<lF> F]}
  {RF' : [Γ ||-<lF'> F']}
  (Rt : [Γ ||-<lF> t : F | RF]) 
  (Rt' : [Γ ||-<lF'> t' : F' | RF']) 
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]])
  (RGt' : [Γ ||-<lF'> G'[t'..]]) :
  [Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ].
Proof.
  assert (wfΓ : [|-Γ]) by (escape ; gen_typing).
  assert [Γ ||-<l> t' : F⟨wk_id (Γ:=Γ)⟩ | PolyRed.shpRed RFG wk_id wfΓ].
  {
    eapply LRTmRedConv; tea.
    eapply LRTyEqSym. 
    replace F' with F'⟨wk_id (Γ := Γ)⟩ by now bsimpl.
    eapply (PolyRedEq.shpRed RFGeq).
  }
  eapply transEq.
  2: (replace G'[t'..] with G'[t' .: wk_id (Γ:=Γ) >> tRel] by now bsimpl); eapply (PolyRedEq.posRed RFGeq).
  irrelevance0.
  2: eapply (PolyRed.posExt RFG).
  3: irrelevance0; tea; now bsimpl.
  1: now bsimpl.
  eassumption.
  Unshelve. all: tea.
  irrelevance0; tea; now bsimpl.
Qed.

Lemma singleSubstΠ2 {Γ F F' G G' t t' l lF lF'}
  {ΠFG : [Γ ||-<l> tProd F G]}
  (ΠFGeq : [Γ ||-<l> tProd F G ≅ tProd F' G' | ΠFG])
  {RF : [Γ ||-<lF> F]}
  {RF' : [Γ ||-<lF'> F']}
  (Rt : [Γ ||-<lF> t : F | RF]) 
  (Rt' : [Γ ||-<lF'> t' : F' | RF']) 
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]])
  (RGt' : [Γ ||-<lF'> G'[t'..]]) :
  [Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ].
Proof.
  eapply singleSubstPoly2; tea.
  pose (hΠ := normRedΠ0 (invLRΠ ΠFG)).
  assert (heq : [Γ ||-<l> tProd F G ≅ tProd F' G' | LRPi' hΠ]) by irrelevance.
  destruct heq as [?? red' ? polyRed]; cbn in *.
  assert (h' :=redtywf_whnf red' whnf_tProd).
  symmetry in h'; injection h'; clear h'; intros ;  subst.
  exact polyRed.
Qed.

Lemma substSΠaux {Γ F G t l} 
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Δ : context) (σ : nat -> term) 
  (wfΔ : [ |-[ ta ] Δ]) (vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) :
  [Δ ||-< l > G[up_term_term σ][t[σ]..]].
Proof.
  eapply singleSubstΠ1.
  eapply (validTy VΠFG); tea.
  now eapply validTm.
  Unshelve. all: eassumption.
Qed.

Lemma singleSubstComm' G t σ : G[t..][σ] = G[up_term_term σ][t[σ]..].
Proof. now asimpl. Qed.

Lemma substSΠ {Γ F G t l} 
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  (VΠFG : [Γ ||-v<l> tProd F G | VΓ])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] | VΓ].
Proof.
  opector; intros.
  - rewrite singleSubstComm'; now eapply substSΠaux.
  - rewrite singleSubstComm'.
    irrelevance0. 1: symmetry; apply singleSubstComm'.
    eapply singleSubstΠ2.
    1: eapply (validTyExt VΠFG).
    1, 2: tea.
    1, 2: now eapply validTm.
    1: now eapply validTmExt.
    now eapply substSΠaux.
    Unshelve. all: tea.
    now eapply substSΠaux.
Qed.

Lemma substSΠeq {Γ F F' G G' t u l} 
  {VΓ : [||-v Γ]}
  {VF : [Γ ||-v<l> F | VΓ]}
  {VF' : [Γ ||-v<l> F' | VΓ]}
  {VΠFG : [Γ ||-v<l> tProd F G | VΓ]}
  (VΠFG' : [Γ ||-v<l> tProd F' G' | VΓ])
  (VΠFGeq : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ | VΠFG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) 
  (Vu : [Γ ||-v<l> u : F' | VΓ | VF']) 
  (Vtu : [Γ ||-v<l> t ≅ u : F | VΓ | VF]) 
  (VGt := substSΠ VΠFG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[u..] | VΓ | VGt].
Proof.
  constructor; intros.
  rewrite singleSubstComm'.
  irrelevance0.
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