From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Reduction NormalRed Induction Transitivity.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaValidity.
  Context `{GenericTypingProperties}.
  Context {l Γ F G} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ,, F ||-v< l > G | validSnoc VΓ VF]).

  Lemma SigRed {Δ σ} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : _ | wfΔ])
    : [ Δ ||-< l > (tSig F G)[σ] ].
  Proof.
    eapply LRSig'.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    escape; cbn; econstructor; tea;
    destruct (polyRedId p);
    destruct (polyRedEqId p (substPolyRedEq VΓ VF VG _ Vσ Vσ (reflSubst _ _ Vσ))); escape.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
    - gen_typing.
  Defined.

  Lemma SigEqRed {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (Vσ : [VΓ | Δ ||-v σ : _ | tΔ])
    (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ])
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ])
    : [ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F G)[σ'] | SigRed tΔ Vσ ].
  Proof.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    pose (p' := substPolyRed VΓ VF VG _ Vσ').
    pose (peq := substPolyRedEq VΓ VF VG _ Vσ Vσ' Vσσ').
    destruct (polyRedId p); destruct (polyRedId p'); destruct (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
  Defined.

  Lemma SigValid : [Γ ||-v< l > tSig F G | VΓ].
  Proof. unshelve econstructor; intros; [now eapply SigRed| now eapply SigEqRed].  Defined.
  
End SigmaValidity.

Section SigmaCongValidity.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G' l}
    (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< l > F | VΓ ])
    (VG : [ Γ ,, F ||-v< l > G | validSnoc VΓ VF ])
    (VF' : [ Γ ||-v< l > F' | VΓ ])
    (VG' : [ Γ ,, F' ||-v< l > G' | validSnoc VΓ VF' ])
    (VFF' : [ Γ ||-v< l > F ≅ F' | VΓ | VF ])
    (VGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF | VG ]).

  Lemma SigCongRed {Δ σ} (wfΔ : [|- Δ]) (Vσ : [VΓ | Δ ||-v σ : _ | wfΔ])
    : [ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F' G')[σ] | validTy (SigValid VΓ VF VG) wfΔ Vσ ].
  Proof.
    pose (p := substPolyRed VΓ VF VG _ Vσ).
    pose (p' := substPolyRed VΓ VF' VG' _ Vσ).
    pose (peq := substEqPolyRedEq VΓ VF VG _ Vσ VF' VG' VFF' VGG').
    destruct (polyRedId p); destruct (polyRedId p'); destruct (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
  Qed.

  Lemma SigCong : [ Γ ||-v< l > tSig F G ≅ tSig F' G' | VΓ | SigValid VΓ VF VG ].
  Proof.  econstructor; intros; eapply SigCongRed.  Qed.

End SigmaCongValidity.


Lemma up_subst_single {t σ a} : t[up_term_term σ][a..] = t[a .: σ].
Proof. now asimpl. Qed.

Lemma wk_id_shift {t a Γ} : t[a .: @wk_id Γ >> tRel] = t[a..].
Proof. now bsimpl. Qed.

Lemma split_valid_subst_wk_id {Γ G σ} :
 G[σ] = G[up_term_term (↑ >> σ)][σ var_zero .: (@wk_id Γ) >> tRel].
Proof.  now rewrite wk_id_shift, up_subst_single, scons_eta'. Qed.

Section SigInjValid.
  Context `{GenericTypingProperties}.
  Context {l Γ F G} (VΓ : [||-v Γ]) (VΣ : [Γ ||-v<l> tSig F G | VΓ]).
  
  Lemma domSigValid : [Γ ||-v<l> F | VΓ].
  Proof.
    unshelve econstructor.
    - intros ??? Vσ; instValid Vσ.
      apply (polyRedId (normRedΣ0 (invLRΣ RVΣ))).
    - intros ???? Vσ Vσ' Vσσ' ; instAllValid Vσ Vσ' Vσσ'.
      set (P := (polyRedId _)); destruct P.
      pose (X := normEqRedΣ _ REVΣ); fold subst_term in *.
      irrelevanceRefl; apply (polyRedEqId _ X).
  Qed.

  Lemma codSigValid : [Γ,, F ||-v<l> G | validSnoc VΓ domSigValid ].
  Proof.
    pose (domSigValid).
    assert (h : forall (Δ : context) (σ : nat -> term) (wfΔ : [ |-[ ta ] Δ]),
      [validSnoc VΓ domSigValid | Δ ||-v σ : Γ,, F | wfΔ] -> [Δ ||-< l > G[σ]]).
    1:{
      intros ?? wfΔ Vσ; instValid (validTail Vσ).
      pose (p := normRedΣ0 (invLRΣ RVΣ)); fold subst_term in *.
      erewrite split_valid_subst_wk_id.
      unshelve eapply (PolyRed.posRed p (wk_id) wfΔ).
      irrelevance0; [|exact (validHead Vσ)]; now rewrite wk_id_ren_on.
    }
    unshelve econstructor; tea.
    intros ??? wfΔ Vσ Vσ' Vσσ' ; instAllValid (validTail Vσ) (validTail Vσ') (eqTail Vσσ').
    pose (p := normRedΣ0 (invLRΣ RVΣ));
    pose (q := normEqRedΣ _ REVΣ); fold subst_term in *.
    irrelevance0.
    1: now erewrite split_valid_subst_wk_id.
    assert [PolyRed.shpRed p wk_id wfΔ | Δ ||- σ' var_zero : (ParamRedTy.dom p)⟨wk_id⟩].
    1:{
      eapply LRTmRedConv.
      2: exact (validHead Vσ').
      rewrite wk_id_ren_on; cbn.
      now eapply LRTyEqSym.
    }
    eapply transEq; cycle 1.
    + erewrite split_valid_subst_wk_id.
      unshelve eapply (PolyRedEq.posRed q wk_id wfΔ).
      irrelevance.
    + unshelve eapply (PolyRed.posExt p wk_id wfΔ); tea.
      1: irrelevance0; [|exact (validHead Vσ)]; now rewrite wk_id_ren_on.
      irrelevance0; [|exact (eqHead Vσσ')]; now rewrite wk_id_ren_on.
  Qed.
  
End SigInjValid.



Section SigTmValidity.

  Context `{GenericTypingProperties}.
  Context {Γ F G} (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< one > F | VΓ ])
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ])
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc VΓ VF | VU ]) .

  Lemma sigTmEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (Vσ : [VΓ | Δ ||-v σ : _ | tΔ])
    (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ])
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ ])
    : [Δ |-[ ta ] tSig F[σ] G[up_term_term σ] ≅ tSig F[σ'] G[up_term_term σ'] : U].
  Proof.
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vureaσ' := liftSubstSrealign' VF Vσσ' Vσ').
    pose proof (Vuσσ' := liftSubstSEq' VF Vσσ').
    instAllValid Vσ Vσ' Vσσ'; instAllValid Vuσ Vureaσ' Vuσσ'; escape.
    eapply convtm_sig; tea.
  Qed.

  Lemma SigRedU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< one > (tSig F G)[σ] : U | validTy (UValid VΓ) tΔ Vσ ].
  Proof.
    pose proof (Vσσ := reflSubst _ _ Vσ).
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vuσσ := liftSubstSEq' VF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; escape.
    econstructor; cbn.
    - apply redtmwf_refl; cbn in *; now eapply ty_sig.
    - constructor.
    - now eapply convtm_sig.
    - cbn. unshelve refine (LRCumulative (SigRed _ _ _ tΔ Vσ));
      unshelve eapply univValid; tea; try irrValid.
  Defined.

  Lemma SigValidU : [ Γ ||-v< one > tSig F G : U | VΓ | UValid VΓ ].
  Proof.
    econstructor.
    - intros Δ σ tΔ Vσ.
      exact (SigRedU tΔ Vσ).
    - intros Δ σ σ' tΔ Vσ Vσ' Vσσ'.
      pose proof (univValid (l' := zero) _ _ VFU) as VF0.
      pose proof (irrelevanceValidity (validSnoc VΓ VF)
                    (validSnoc (l := zero) VΓ VF0)
                    (univValid (l' := zero) _ _ VGU)) as VG0.
      unshelve econstructor ; cbn.
      + exact (SigRedU tΔ Vσ).
      + exact (SigRedU tΔ Vσ').
      + exact (LRCumulative (SigRed VΓ VF0 VG0 tΔ Vσ)).
      + exact (sigTmEq tΔ Vσ Vσ' Vσσ').
      + exact (LRCumulative (SigRed VΓ VF0 VG0 tΔ Vσ')).
      + pose proof (SigEqRed VΓ VF0 VG0 tΔ Vσ Vσ' Vσσ').
        irrelevanceCum.
  Qed.

End SigTmValidity.


Section SigTmCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G'}
    (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< one > F | VΓ ])
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ])
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc VΓ VF | VU ])
    (VF' : [ Γ ||-v< one > F' | VΓ ])
    (VU' : [ Γ ,, F' ||-v< one > U | validSnoc VΓ VF' ])
    (VF'U : [ Γ ||-v< one > F' : U | VΓ | UValid VΓ ])
    (VG'U : [ Γ ,, F' ||-v< one > G' : U | validSnoc VΓ VF' | VU' ])
    (VFF' : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VGG' : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ]).

  Lemma SigCongTm : [ Γ ||-v< one > tSig F G ≅ tSig F' G' : U | VΓ | UValid VΓ ].
  Proof.
    econstructor.
    intros Δ σ tΔ Vσ.
    pose proof (univValid (l' := zero) _ _ VFU) as VF0.
    pose proof (univValid (l' := zero) _ _ VF'U) as VF'0.
    pose proof (Vσσ := reflSubst _ _ Vσ).
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vuσσ := liftSubstSEq' VF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; escape.
    pose proof (irrelevanceValidity (validSnoc VΓ VF)
                  (validSnoc (l := zero) VΓ VF0)
                  (univValid (l' := zero) _ _ VGU)) as VG0.
    pose proof (irrelevanceValidity (validSnoc VΓ VF')
                  (validSnoc (l := zero) VΓ VF'0)
                  (univValid (l' := zero) _ _ VG'U)) as VG'0.
    unshelve econstructor ; cbn.
    - exact (SigRedU VΓ VF VU VFU VGU tΔ Vσ).
    - exact (SigRedU VΓ VF' VU' VF'U VG'U tΔ Vσ).
    - exact (LRCumulative (SigRed VΓ VF0 VG0 tΔ Vσ)).
    - now eapply convtm_sig.
    - exact (LRCumulative (SigRed VΓ VF'0 VG'0 tΔ Vσ)).
    - enough ([ Δ ||-< zero > (tSig F G)[σ] ≅ (tSig F' G')[σ] | SigRed VΓ VF0 VG0 tΔ Vσ]) by irrelevanceCum.
      refine (SigCongRed VΓ VF0 VG0 VF'0 VG'0 _ _ tΔ Vσ).
      + exact (univEqValid VΓ (UValid VΓ) VF0 VFF').
      + pose proof (univEqValid (validSnoc VΓ VF) VU (univValid (l' := zero) _ _ VGU) VGG') as VGG'0.
        refine (irrelevanceEq _ _ _ _ VGG'0).
  Qed.

End SigTmCongruence.

Section ProjRed.
  Context `{GenericTypingProperties}.

  Lemma fstRed {l Δ F G} {p}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (RF : [Δ ||-<l> F])
    (Rp : [Δ ||-<l> p : _ | LRSig' (normRedΣ0 RΣ)]) :
    ([Δ ||-<l> tFst p : _ | RF] × [Δ ||-<l> tFst p ≅ tFst Rp.(SigRedTm.nf) : _ | RF]) × [Δ ||-<l> tFst Rp.(SigRedTm.nf) : _ | RF].
  Proof.
    assert [Δ ||-<l> tFst Rp.(SigRedTm.nf) : _ | RF].
    1:{
      assert (wfΔ : [|-Δ]) by (escape; gen_typing).
      pose (r := SigRedTm.fstRed Rp (@wk_id Δ) wfΔ).
      rewrite wk_id_ren_on in r.
      irrelevance.
    }
    split; tea.
    irrelevanceRefl.
    eapply redSubstTerm; tea. 
    eapply redtm_fst; now destruct (SigRedTm.red Rp).
  Qed.

  Lemma fstRedEq {l Δ F G} {p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (RF : [Δ ||-<l> F])
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rpp' : [Δ ||-<l> p ≅ p' : _ | RΣn]) 
    (Rp := SigRedTmEq.redL Rpp')
    (Rp' := SigRedTmEq.redR Rpp') :
    [× [Δ ||-<l> tFst p ≅ tFst Rp.(SigRedTm.nf) : _ | RF],
    [Δ ||-<l> tFst p' ≅ tFst Rp'.(SigRedTm.nf) : _ | RF] &
    [Δ ||-<l> tFst Rp.(SigRedTm.nf) ≅ tFst Rp'.(SigRedTm.nf) : _ | RF]].
  Proof.
    split.
    - now eapply fstRed.
    - now eapply fstRed.
    - assert (wfΔ : [|-Δ]) by (escape; gen_typing).
      epose (e := SigRedTmEq.eqFst Rpp' wk_id wfΔ).
      do 2 rewrite wk_id_ren_on in e.
      irrelevance.
  Qed.

  
  Lemma sndRed {l Δ F G} {p}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (RF : [Δ ||-<l> F])
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rp : [Δ ||-<l> p : _ | LRSig' (normRedΣ0 RΣ)])
    (RGfstp : [Δ ||-<l> G[(tFst p)..]]) 
    (RGfstpEq : [Δ ||-<l> G[(tFst p)..] ≅ G[(tFst Rp.(SigRedTm.nf))..] | RGfstp]) :
    [Δ ||-<l> tSnd p : _ | RGfstp] × [Δ ||-<l> tSnd p ≅ tSnd Rp.(SigRedTm.nf) : _ | RGfstp].
  Proof.
    eapply redSubstTerm. 
    2: eapply redtm_snd; now destruct (SigRedTm.red Rp).
    assert (wfΔ : [|-Δ]) by (escape; gen_typing).
    eapply LRTmRedConv; cycle 1.
    + pose proof (r := SigRedTm.sndRed Rp (@wk_id Δ) wfΔ).
      rewrite <- (wk_id_ren_on Δ (SigRedTm.nf Rp)).
      eassumption.
    + unshelve eapply LRTyEqSym. 2: tea.
      rewrite wk_id_shift; rewrite wk_id_ren_on; tea.
  Qed.

  Lemma sndRedEq {l Δ F G} {p p'}
    (RΣ : [Δ ||-Σ<l> tSig F G])
    (RF : [Δ ||-<l> F])
    (RΣn := LRSig' (normRedΣ0 RΣ))
    (Rpp' : [Δ ||-<l> p ≅ p' : _ | RΣn]) 
    (Rp := SigRedTmEq.redL Rpp')
    (Rp' := SigRedTmEq.redR Rpp')
    (RGfstp : [Δ ||-<l> G[(tFst p)..]]) 
    (RGfstpEq : [Δ ||-<l> G[(tFst p)..] ≅ G[(tFst Rp.(SigRedTm.nf))..] | RGfstp])
    (RGfstp' : [Δ ||-<l> G[(tFst p')..]]) 
    (RGfstpEq' : [Δ ||-<l> G[(tFst p')..] ≅ G[(tFst Rp'.(SigRedTm.nf))..] | RGfstp']) :
    [× [Δ ||-<l> tSnd p ≅ tSnd Rp.(SigRedTm.nf) : _ | RGfstp],
    [Δ ||-<l> tSnd p' ≅ tSnd Rp'.(SigRedTm.nf) : _ | RGfstp'] &
    [Δ ||-<l> tSnd Rp.(SigRedTm.nf) ≅ tSnd Rp'.(SigRedTm.nf) : _ | RGfstp]].
  Proof.
    split.
    - now eapply sndRed.
    - now eapply sndRed.
    - assert (wfΔ : [|-Δ]) by (escape; gen_typing).
      eapply LRTmEqRedConv; cycle 1.
      + epose proof (e := SigRedTmEq.eqSnd Rpp' wk_id wfΔ).
        rewrite <- (wk_id_ren_on Δ (SigRedTm.nf Rp)).
        rewrite <- (wk_id_ren_on Δ (SigRedTm.nf Rp')).
        tea.
    + unshelve eapply LRTyEqSym. 2: tea.
      rewrite wk_id_shift; rewrite wk_id_ren_on; tea.
  Qed.


  Context {l Γ F G } (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ,, F ||-v< l > G | validSnoc VΓ VF])
    (VΣ := SigValid VΓ VF VG).

  Lemma fstValid {p} (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]): [Γ ||-v<l> tFst p : _ | VΓ | VF].
  Proof.
    unshelve econstructor.
    - intros ?? wfΔ Vσ.
      instValid Vσ.
      pose proof (invLRΣ RVΣ); refold.
      unshelve eapply fstRed. 2: tea. irrelevance.
    - intros ??? wfΔ Vσ Vσ' Vσσ'.
      instAllValid Vσ Vσ' Vσσ'.
      pose (RΣinv := invLRΣ RVΣ); normRedΣin REVp; fold subst_term in *.
      destruct (fstRedEq RΣinv RVF REVp).
      eapply LREqTermHelper; tea; eapply reflLRTyEq.
  Qed.  
  
  Lemma fstCongValid {p p'} 
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ])
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ]) 
    (Vpp' : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ])
    : [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VF].
  Proof.
    constructor; intros ?? wfΔ Vσ.
    instValid Vσ; instValidExt Vσ (reflSubst _ _ Vσ).
    pose (RΣinv := invLRΣ RVΣ); normRedΣin RVpp'; fold subst_term in *.
    destruct (fstRedEq RΣinv RVF RVpp').
    eapply LREqTermHelper; tea.
  Qed.  
  
  Lemma sndValid {p} (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ])
    (VGfst := substS VG (fstValid Vp)) : 
    [Γ ||-v<l> tSnd p : _ | VΓ | VGfst].
  Proof.
    unshelve econstructor.
    - intros ?? wfΔ Vσ.
      instValid Vσ.
      pose (RΣinv := invLRΣ RVΣ); normRedΣin RVp; fold subst_term in *.
      destruct (fstRed RΣinv RVF RVp) as [[Rfstp Rfstpeq] Rfstnf].
      pose (Vpσ := consSubstS _ _ Vσ VF Rfstp).
      pose (Vnfσ := consSubstS _ _ Vσ VF Rfstnf).
      pose (Veqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VF Rfstp Rfstpeq).
      instAllValid Vpσ Vnfσ Veqσ.
      unshelve epose (fst (sndRed RΣinv RVF RVp _ _)).
      + now rewrite up_subst_single.
      + irrelevance0; rewrite up_subst_single; tea; reflexivity.
      + irrelevance.
    - intros ??? wfΔ Vσ Vσ' Vσσ'.
      pose proof (Vfstp := fstValid Vp).
      instAllValid Vσ Vσ' Vσσ'.
      pose (RΣinv := invLRΣ RVΣ); pose (RΣinv' := invLRΣ RVΣ0).
      normRedΣin RVp; normRedΣin RVp0; normRedΣin REVp; fold subst_term in *.
      destruct (fstRed RΣinv RVF REVp.(SigRedTmEq.redL)) as [[Rfstp Rfstpeq] Rfstnf].
      pose (Vpσ := consSubstS _ _ Vσ VF Rfstp).
      pose (Vnfσ := consSubstS _ _ Vσ VF Rfstnf).
      pose (Veqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VF Rfstp Rfstpeq).
      instAllValid Vpσ Vnfσ Veqσ.
      destruct (fstRed RΣinv RVF REVp.(SigRedTmEq.redR)) as [[Rfstp' Rfstpeq'] Rfstnf'].
      pose (Vpσ' := consSubstS _ _ Vσ VF Rfstp').
      pose (Vnfσ' := consSubstS _ _ Vσ VF Rfstnf').
      pose (Veqσ' := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VF Rfstp' Rfstpeq').
      instAllValid Vpσ' Vnfσ' Veqσ'.
      unshelve epose  proof(r := sndRedEq RΣinv RVF REVp _ _ _ _).
      + now rewrite up_subst_single.
      + irrelevance0; rewrite up_subst_single; tea; reflexivity.
      + now rewrite up_subst_single.
      + irrelevance0; rewrite up_subst_single; tea; reflexivity.
      + destruct r; irrelevance0; cycle 1.
        1: eapply LREqTermHelper.
        1,2,4: tea.
        2: now rewrite singleSubstComm'.
        epose (Veqσ0 := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VF Rfstp REVfstp).
        instAllValid Vpσ Vpσ' Veqσ0.
        irrelevance0; rewrite up_subst_single; tea; reflexivity.
  Qed.  

  Lemma sndCongValid {p p'} 
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ])
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ]) 
    (Vpp' : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ])
    (VGfst := substS VG (fstValid Vp)) : 
    [Γ ||-v<l> tSnd p ≅ tSnd p' : _ | VΓ | VGfst].
  Proof.
    constructor; intros ?? wfΔ Vσ.
    pose proof (VGfsteq:= substSEq (reflValidTy _ VF) VG (reflValidTy _ VG) (fstValid Vp) (fstValid Vp') (fstCongValid Vp Vp' Vpp')). 
    cbn in VGfsteq.
    instValid Vσ ; instValidExt Vσ (reflSubst _ _ Vσ).
    pose (RΣinv := invLRΣ RVΣ); normRedΣin RVpp'; fold subst_term in *.
    destruct (fstRed RΣinv RVF RVpp'.(SigRedTmEq.redL)) as [[Rfstp Rfstpeq] Rfstnf].
    pose (Vpσ := consSubstS _ _ Vσ VF Rfstp).
    pose (Vnfσ := consSubstS _ _ Vσ VF Rfstnf).
    pose (Veqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VF Rfstp Rfstpeq).
    instAllValid Vpσ Vnfσ Veqσ.
    destruct (fstRed RΣinv RVF RVpp'.(SigRedTmEq.redR)) as [[Rfstp' Rfstpeq'] Rfstnf'].
    pose (Vpσ' := consSubstS _ _ Vσ VF Rfstp').
    pose (Vnfσ' := consSubstS _ _ Vσ VF Rfstnf').
    pose (Veqσ' := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VF Rfstp' Rfstpeq').
    instAllValid Vpσ' Vnfσ' Veqσ'.
    unshelve epose  proof(r := sndRedEq RΣinv RVF RVpp' _ _ _ _).
    + now rewrite up_subst_single.
    + irrelevance0; rewrite up_subst_single; tea; reflexivity.
    + now rewrite up_subst_single.
    + irrelevance0; rewrite up_subst_single; tea; reflexivity.
    + destruct r; irrelevance0; cycle 1.
      1: eapply LREqTermHelper.
      1,2,4: tea.
      2: now rewrite singleSubstComm'.
      irrelevance0; rewrite up_subst_single; change (tFst ?p[?σ]) with (tFst p)[σ]; rewrite <- singleSubstComm; tea.
      reflexivity. 
  Qed.  

  
End ProjRed.



Section PairRed.
  Context `{GenericTypingProperties}.

  Lemma pairFstRed {Γ A B a b l}
    (RA : [Γ ||-<l> A])
    (RB : [Γ ,, A ||-<l> B])
    (RBa : [Γ ||-<l> B[a..]])
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
    [Γ ||-<l> tFst (tPair A B a b) : _ | RA] × [Γ ||-<l> tFst (tPair A B a b) ≅ a : _ | RA].
  Proof.
    escape.
    eapply redSubstTerm; tea.
    eapply redtm_fst_beta; tea.
  Qed.

  Lemma pairSndRed {Γ A B a b l}
    (RA : [Γ ||-<l> A])
    (RB : [Γ ,, A ||-<l> B])
    (RBa : [Γ ||-<l> B[a..]])
    (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ])
    (RBconv : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ])
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
    [Γ ||-<l> tSnd (tPair A B a b) : _ | RBfst ] × [Γ ||-<l> tSnd (tPair A B a b) ≅ b : _ | RBfst].
  Proof.
    escape.
    eapply redSubstTerm; tea.
    2: eapply redtm_snd_beta; tea.
    now eapply LRTmRedConv.
  Qed.


  Lemma pairRed {Γ A B a b l}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣ := normRedΣ0 RΣ0)
    (RA : [Γ ||-<l> A])
    (RBa : [Γ ||-<l> B[a..]])
    (RBconv : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ])
    (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ])
    (Ra : [Γ ||-<l> a : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ]) :
    [Γ ||-<l> tPair A B a b : _ | LRSig' RΣ].
  Proof.
    destruct (polyRedId RΣ); escape. 
    unshelve eexists (tPair A B a b) _.
    + intros ? ρ wfΔ.
      rewrite wk_fst; irrelevanceRefl; unshelve eapply wkTerm.
      1:tea. 
      2: unshelve eapply pairFstRed; tea.
    + eapply redtmwf_refl; cbn.
      eapply ty_pair; tea.
    + constructor; apply PiRedTyPack.eqdom.
    + eapply convtm_eta_sig; tea.
      * now eapply ty_pair.
      * constructor; unshelve eapply escapeEq, reflLRTyEq; [|tea].
      * now eapply ty_pair.
      * constructor; unshelve eapply escapeEq, reflLRTyEq; [|tea].
      * enough [Γ |- tFst (tPair A B a b) ≅ a : A].
        1: transitivity a; tea; now symmetry.
        eapply convtm_exp.
        1: now eapply redtywf_refl.
        1: now eapply redtm_fst_beta.
        1: now eapply redtmwf_refl.
        eapply escapeEqTerm; now eapply reflLRTmEq.
      * enough [Γ |- tSnd (tPair A B a b) ≅ b : B[(tFst (tPair A B a b))..]].
        1: transitivity b; tea; now symmetry.
        eapply convtm_conv; tea.
        eapply convtm_exp.
        1: now eapply redty_refl.
        1: eapply redtm_conv; [| now symmetry]; now eapply redtm_snd_beta.
        1: now eapply redtm_refl.
        eapply escapeEqTerm; now eapply reflLRTmEq.
    + intros ? ρ wfΔ.
      irrelevance0.
      2: rewrite wk_snd; eapply wkTerm; now eapply pairSndRed.
      now rewrite subst_ren_subst_mixed.
      Unshelve. all: tea.
  Qed.


  Lemma sigEtaRed {Γ A B l p p'}
    (RΣ0 : [Γ ||-Σ<l> tSig A B])
    (RΣ := LRSig' (normRedΣ0 RΣ0))
    (RA : [Γ ||-<l> A])
    (RBfst : [Γ ||-<l> B[(tFst p)..]])
    (RBfst' : [Γ ||-<l> B[(tFst p')..]])
    (Rp : [Γ ||-<l> p : _ | RΣ])
    (Rp' : [Γ ||-<l> p' : _ |  RΣ])
    (RBfstEq0 : [Γ ||-<l> B[(tFst p)..] ≅ B[(tFst p')..] | RBfst])
    (RBfstnf : [Γ ||-<l> B[(tFst Rp.(SigRedTm.nf))..]])
    (RBfstEq : [Γ ||-<l> B[(tFst p)..] ≅ B[(tFst Rp.(SigRedTm.nf))..] | RBfst])
    (RBfstEq' : [Γ ||-<l> B[(tFst p')..] ≅ B[(tFst Rp'.(SigRedTm.nf))..] | RBfst'])
    (Rfstpp' : [Γ ||-<l> tFst p ≅ tFst p' : _ | RA])
    (Rsndpp' : [Γ ||-<l> tSnd p ≅ tSnd p' : _ | RBfst]) :
    [Γ ||-<l> p ≅ p' : _ | RΣ].
  Proof.
    exists Rp Rp'.
    - destruct (polyRedId (normRedΣ0 RΣ0)) as [_ RB].
      assert ([Γ ||-<l> SigRedTm.nf Rp : _ | RΣ] × [Γ ||-<l> p ≅ SigRedTm.nf Rp : _ | RΣ]) as [Rnf Rpnf].
      1: eapply (redTmFwdConv Rp (SigRedTm.red Rp)), isPair_whnf, isWfPair_isPair, SigRedTm.isfun.
      assert ([Γ ||-<l> SigRedTm.nf Rp' : _ | RΣ]× [Γ ||-<l> p' ≅ SigRedTm.nf Rp' : _ | RΣ]) as [Rnf' Rpnf'].
      1: eapply (redTmFwdConv Rp' (SigRedTm.red Rp')), isPair_whnf, isWfPair_isPair, SigRedTm.isfun.
      destruct (fstRed RΣ0 RA Rp) as [[Rfstp Rfsteq] Rfstnf].
      destruct (fstRed RΣ0 RA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
      destruct (sndRed RΣ0 RA Rp RBfst RBfstEq).
      destruct (sndRed RΣ0 RA Rp' RBfst' RBfstEq').
      escape.
      eapply convtm_eta_sig; tea.
      1,2: now eapply SigRedTm.isfun.
      + transitivity (tFst p).
        1: now symmetry.
        transitivity (tFst p'); tea.
      + eapply convtm_conv; tea.
        transitivity (tSnd p).
        1: now symmetry.
        transitivity (tSnd p'); tea.
        eapply convtm_conv; tea.
        now symmetry.
    - intros; do 2 rewrite wk_fst. 
      irrelevanceRefl. eapply wkTermEq.
      destruct (fstRed RΣ0 RA Rp) as [[Rfstp Rfsteq] Rfstnf].
      destruct (fstRed RΣ0 RA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
      eapply transEqTerm; tea.
      eapply transEqTerm; tea.
      now eapply LRTmEqSym.
      Unshelve. tea.
    - intros. do 2 rewrite wk_snd.
      eapply LRTmEqRedConv.
      2:{
        eapply wkTermEq. 
        destruct (sndRed RΣ0 RA Rp RBfst RBfstEq).
        destruct (sndRed RΣ0 RA Rp' RBfst' RBfstEq').
        eapply transEqTerm; tea.
        eapply LRTmEqRedConv; tea.
        eapply transEqTerm; tea.
        now eapply LRTmEqSym.
        Unshelve. tea.
      }
      rewrite wk_fst, <- subst_ren_subst_mixed.
      eapply wkEq. cbn.
      eapply LRTyEqSym.
      eapply transEq; tea.
      now eapply LRTyEqSym.
      Unshelve. tea.
  Qed.

  Lemma subst_sig {A B σ} : (tSig A B)[σ] = (tSig A[σ] B[up_term_term σ]).
  Proof. reflexivity. Qed.

  Lemma subst_pair {A B a b σ} : (tPair A B a b)[σ] = (tPair A[σ] B[up_term_term σ] a[σ] b[σ]).
  Proof. reflexivity. Qed.
  
  Lemma subst_fst {p σ} : (tFst p)[σ] = tFst p[σ].
  Proof. reflexivity. Qed.
  
  Lemma subst_snd {p σ} : (tSnd p)[σ] = tSnd p[σ].
  Proof. reflexivity. Qed.
  
  Lemma pairFstRedEq {Γ A A' B B' a a' b b' l}
    (RA : [Γ ||-<l> A])
    (RA' : [Γ ||-<l> A'])
    (RAA' :[Γ ||-<l> A ≅ A' | RA])
    (RB : [Γ ,, A ||-<l> B])
    (RB' : [Γ ,, A' ||-<l> B'])
    (RBa : [Γ ||-<l> B[a..]])
    (RBa' : [Γ ||-<l> B'[a'..]])
    (Ra : [Γ ||-<l> a : A | RA])
    (Ra' : [Γ ||-<l> a' : A' | RA'])
    (Raa' : [Γ ||-<l> a ≅ a' : A | RA])
    (Rb : [Γ ||-<l> b : _ | RBa ])
    (Rb' : [Γ ||-<l> b' : _ | RBa' ]) :
    [Γ ||-<l> tFst (tPair A B a b) ≅ tFst (tPair A' B' a' b') : _ | RA].
  Proof.
    destruct (pairFstRed RA RB RBa Ra Rb).
    destruct (pairFstRed RA' RB' RBa' Ra' Rb').
    eapply transEqTerm; tea.
    eapply transEqTerm; tea.
    eapply LRTmEqRedConv.
    + now eapply LRTyEqSym.
    + now eapply LRTmEqSym.
  Qed.
  
  Lemma pairSndRedEq {Γ A A' B B' a a' b b' l}
    (RA : [Γ ||-<l> A])
    (RA' : [Γ ||-<l> A'])
    (RAA' :[Γ ||-<l> A ≅ A' | RA])
    (RB : [Γ ,, A ||-<l> B])
    (RB' : [Γ ,, A' ||-<l> B'])
    (RBa : [Γ ||-<l> B[a..]])
    (RBa' : [Γ ||-<l> B'[a'..]])
    (RBaBa' : [Γ ||-<l> B[a..] ≅ B'[a'..] | RBa ])
    (RBfst : [Γ ||-<l> B[(tFst (tPair A B a b))..] ])
    (RBconv : [Γ ||-<l> B[a..] ≅ B[(tFst (tPair A B a b))..] | RBa ])
    (RBfst' : [Γ ||-<l> B'[(tFst (tPair A' B' a' b'))..] ])
    (RBconv' : [Γ ||-<l> B'[a'..] ≅ B'[(tFst (tPair A' B' a' b'))..] | RBa' ])
    (Ra : [Γ ||-<l> a : A | RA])
    (Ra' : [Γ ||-<l> a' : A' | RA'])
    (Rb : [Γ ||-<l> b : _ | RBa ])
    (Rb' : [Γ ||-<l> b' : _ | RBa' ]) 
    (Rbb' : [Γ ||-<l> b ≅ b' : _ | RBa]) :
    [Γ ||-<l> tSnd (tPair A B a b) ≅ tSnd (tPair A' B' a' b') : _ | RBfst].
  Proof.
    destruct (pairSndRed RA RB RBa RBfst RBconv Ra Rb).
    destruct (pairSndRed RA' RB' RBa' RBfst' RBconv' Ra' Rb').
    eapply transEqTerm; tea.
    eapply LRTmEqRedConv; tea.
    eapply transEqTerm; tea.
    eapply LRTmEqRedConv; cycle 1.
    + now eapply LRTmEqSym.
    + eapply LRTyEqSym; eapply transEq; cycle 1; tea.
  Qed.


  Lemma pairFstValid {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tFst (tPair A B a b) : _ | VΓ | VA] ×
    [Γ ||-v<l> tFst (tPair A B a b) ≅ a : _ | VΓ | VA].
  Proof.
    assert (h : forall {Δ σ} (wfΔ : [|-  Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]),
      [validTy VA wfΔ Vσ | Δ ||- (tFst (tPair A B a b))[σ] : A[σ]] ×
      [validTy VA wfΔ Vσ | Δ ||- (tFst (tPair A B a b))[σ] ≅ a[σ] : A[σ]]).
    1:{
      intros ?? wfΔ Vσ; instValid Vσ.
      pose (RVΣ0 := normRedΣ0 (invLRΣ RVΣ)).
      pose (RVB := snd (polyRedId RVΣ0)).
      unshelve eapply pairFstRed; tea; fold subst_term.
      + now rewrite <- singleSubstComm'.
      + irrelevance0; tea; now rewrite singleSubstComm'.
    }
    split; unshelve econstructor.
    - apply h.
    - intros ??? wfΔ Vσ Vσ' Vσσ'.
      instAllValid Vσ Vσ' Vσσ'. 
      pose (RΣ := normRedΣ0 (invLRΣ RVΣ));
      pose (RΣ' := normRedΣ0 (invLRΣ RVΣ0)); fold subst_term in *.
      pose (RVB := snd (polyRedId RΣ)).
      pose (RVB' := snd (polyRedId RΣ')).
      unshelve eapply pairFstRedEq; tea; fold subst_term.
      1,2: now rewrite <- singleSubstComm'.
      all: irrelevance0; tea; now rewrite singleSubstComm'.
    - apply h.
  Qed.
  
  Lemma pairSndValid {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa])
    (Vfstall := pairFstValid VΓ VA VB Va Vb)
    (VBfst := substS VB (fst Vfstall)) :
    [Γ ||-v<l> tSnd (tPair A B a b) : _ | VΓ | VBfst] ×
    [Γ ||-v<l> tSnd (tPair A B a b) ≅ b : _ | VΓ | VBfst].
  Proof.
    pose proof (VBfsteq := substSEq (reflValidTy _ VA) VB (reflValidTy _ VB) Va (fst Vfstall) (symValidTmEq (snd (Vfstall)))).
    cbn in VBfsteq.
    assert (h : forall {Δ σ} (wfΔ : [|-  Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]),
      [validTy VBfst wfΔ Vσ | Δ ||- (tSnd (tPair A B a b))[σ] : _ ] ×
      [validTy VBfst wfΔ Vσ | Δ ||- (tSnd (tPair A B a b))[σ] ≅ b[σ] : _ ]).
    1:{
      intros ?? wfΔ Vσ ; instValid Vσ.
      pose (RVΣ0 := normRedΣ0 (invLRΣ RVΣ)).
      pose (RVB := snd (polyRedId RVΣ0)); fold subst_term in *.
      irrelevance0. 1: now rewrite singleSubstComm'.
      unshelve eapply pairSndRed; tea; fold subst_term.
      + now rewrite <- singleSubstComm'.
      + rewrite <- subst_pair, <- subst_fst; irrelevance0;
        rewrite <- singleSubstComm'; tea; reflexivity.
        Unshelve. now rewrite <- singleSubstComm'.
      + irrelevance0; tea; now rewrite <- singleSubstComm'.
    }
    split; unshelve econstructor.
    - apply h.
    - intros ??? wfΔ Vσ Vσ' Vσσ' ; instAllValid Vσ Vσ' Vσσ'.
      pose (RΣ := normRedΣ0 (invLRΣ RVΣ)).
      pose (RΣ' := normRedΣ0 (invLRΣ RVΣ0)).
      pose (RB := snd (polyRedId RΣ)); 
      pose (RB' := snd (polyRedId RΣ')); fold subst_term in *.
      irrelevance0. 1: now rewrite singleSubstComm'.
      unshelve eapply pairSndRedEq; tea; fold subst_term.
      1,2: now rewrite <- singleSubstComm'.
      all: try (irrelevance0; tea; now rewrite <- singleSubstComm').
      all: rewrite <- subst_pair, <- subst_fst.
      2: rewrite <- singleSubstComm'; tea.
      all: irrelevance0; rewrite <- singleSubstComm'; try reflexivity; tea.
      Unshelve. now rewrite <- singleSubstComm'.
    - apply h.
  Qed.


  Lemma pairValid {Γ A B a b l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b : _ | VΓ | VΣ].
  Proof.
    destruct (pairFstValid VΓ VA VB Va Vb) as [Vfst Vfsteq].
    destruct (pairSndValid VΓ VA VB Va Vb) as [Vsnd Vsndeq].
    pose proof (VBfst := substS VB Vfst).
    pose proof (VBfsteq := substSEq (reflValidTy _ VA) VB (reflValidTy _ VB) Va Vfst (symValidTmEq Vfsteq)).
    cbn in VBfsteq.
    assert (pairSubstRed : forall (Δ : context) (σ : nat -> term) (wfΔ : [ |-[ ta ] Δ])
      (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]),
      [Δ ||-<l> (tPair A B a b)[σ] : (tSig A B)[σ] | validTy VΣ wfΔ Vσ]).
    1:{
      intros ?? wfΔ Vσ.
      instValid Vσ; instValidExt Vσ (reflSubst _ _ Vσ).
      pose (RVΣ0 := normRedΣ0 (invLRΣ RVΣ)).
      pose (RVB := snd (polyRedId RVΣ0)); fold subst_term in *.
      pose (Vaσ := consSubstSvalid Vσ Va); instValid Vaσ.
      rewrite <- up_subst_single in RVB0.
      assert (RVb' : [RVB0 | Δ ||- b[σ] : B[up_term_term σ][(a[σ])..]])
        by (irrelevance0; tea; apply  singleSubstComm').
      unshelve epose (p := pairFstRed RVA RVB RVB0 RVa RVb').
      destruct p as [Rfst Rfsteq%LRTmEqSym].
      pose proof (Vfstσ := consSubstS _ _ Vσ VA Rfst).
      epose proof (Veqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VA RVa Rfsteq).
      instValid Vfstσ; instValidExt Vfstσ Veqσ.
      unshelve epose (pairRed RVΣ0 RVA RVB0 _ _ RVa RVb'); fold subst_term in *.
      3: irrelevance.
      + rewrite <- up_subst_single in REVB.
        irrelevance0; tea; now rewrite up_subst_single.
      + now rewrite <- up_subst_single in RVB1.
    }
    unshelve econstructor.
    1: intros; now eapply pairSubstRed.
    intros ??? wfΔ Vσ Vσ' Vσσ'.
    instAllValid Vσ Vσ' Vσσ'.
    set (p := _[_]); set (p' := _[_]).
    pose (RΣ := normRedΣ RVΣ); pose (RΣ' := normRedΣ RVΣ0); fold subst_term in *.
    pose proof (Rp0 := pairSubstRed _ _ wfΔ Vσ).
    pose proof (Rp0' := pairSubstRed _ _ wfΔ Vσ').
    assert (Rp : [Δ ||-<l> p : _ | RΣ]) by irrelevance.
    assert (Rp' : [Δ ||-<l> p' : _ | RΣ]).
    1: eapply LRTmRedConv; [|exact (pairSubstRed _ _ wfΔ Vσ')]; now eapply LRTyEqSym.
    irrelevance0.
    1: symmetry; apply subst_sig.
    destruct (fstRed (invLRΣ RVΣ) RVA Rp) as [[Rfstp Rfsteq] Rfstnf].
    destruct (fstRed (invLRΣ RVΣ) RVA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
    pose (Vfstpσ := consSubstS _ _ Vσ VA Rfstp).
    pose (Vfstnfσ := consSubstS _ _ Vσ VA Rfstnf).
    pose proof (Vfsteqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VA Rfstp Rfsteq).
    epose (Vfstpσ' := consSubstS _ _ Vσ VA Rfstp').
    pose (Vfstnfσ' := consSubstS _ _ Vσ VA Rfstnf').
    pose proof (Vfsteqσ' := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VA Rfstp' Rfsteq').
    pose (Vuσ := liftSubstS' VA Vσ).
    pose (Vuσ' := liftSubstS' VA Vσ').
    pose (Vurσ' := liftSubstSrealign' VA Vσσ' Vσ').
    instValid Vuσ; instValid Vuσ'; instValid Vurσ'.
    assert(Rfstpp' : [RVA | Δ ||- tFst p ≅ tFst p' : A[σ]]). 
    1:{
      eapply pairFstRedEq; tea; irrelevance0; tea; fold subst_term.
      1,2: now rewrite singleSubstComm'.
      Unshelve. all: fold subst_term. 
      2: tea.
      1,2: now rewrite <- singleSubstComm'.
    }
    pose proof (Vfstppσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VA Rfstp Rfstpp').
    instAllValid Vfstpσ Vfstnfσ Vfsteqσ.
    instAllValid Vfstpσ' Vfstnfσ' Vfsteqσ'.
    instValidExt Vfstpσ' Vfstppσ.
    rewrite <- up_subst_single in RVB2.
    rewrite <- up_subst_single in RVB3, REVB.
    rewrite <- up_subst_single in RVB4.
    rewrite <- up_subst_single in RVB5, REVB0.
    rewrite <- up_subst_single in REVB1.
    eapply (sigEtaRed _ RVA RVB2 RVB4 Rp Rp');tea.
    + irrelevance0; tea; now rewrite up_subst_single.
    + irrelevance0; tea; now rewrite up_subst_single.
    + irrelevance0; tea; now rewrite up_subst_single.
    + unshelve eapply pairSndRedEq; tea; fold subst_term.
      7-9: irrelevance0; tea; now rewrite singleSubstComm'.
      1,2: now rewrite <- singleSubstComm'.
      1: irrelevance0; fold subst_term; now rewrite <- singleSubstComm'.
      2: rewrite <- subst_pair, <- subst_fst, <- singleSubstComm'; tea.
      all: rewrite <- subst_pair, <- subst_fst; irrelevance0; 
        rewrite <- singleSubstComm'; try reflexivity; tea.
  Qed.

  Lemma sigEtaValid {Γ A B p p' l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ])
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ])
    (Vfstpp' : [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VA])
    (Vfst := fstValid VΓ VA VB Vp)
    (VBfst := substS VB Vfst)
    (Vsndpp' : [Γ ||-v<l> tSnd p ≅ tSnd p' : _| VΓ | VBfst]) :
    [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ].
  Proof.
    pose proof (Vfst' := fstValid VΓ VA VB Vp').
    pose proof (VBfst' := substS VB Vfst').
    pose proof (VBfsteq := substSEq (reflValidTy _ VA) VB (reflValidTy _ VB) Vfst Vfst' Vfstpp').
    cbn in VBfsteq.
    constructor; intros ?? wfΔ Vσ; instValid Vσ.
    pose proof (RΣ0 := invLRΣ RVΣ).
    pose (RΣ := LRSig' (normRedΣ0 RΣ0)).
    fold subst_term in *.
    assert (Rp : [Δ ||-<l> p[σ] : _ | RΣ]) by irrelevance.
    assert (Rp' : [Δ ||-<l> p'[σ] : _ | RΣ]) by irrelevance.
    destruct (fstRed RΣ0 RVA Rp) as [[Rfstp Rfsteq] Rfstnf].
    destruct (fstRed RΣ0 RVA Rp') as [[Rfstp' Rfsteq'] Rfstnf'].
    pose (Vfstpσ := consSubstS _ _ Vσ VA Rfstp).
    pose (Vfstnfσ := consSubstS _ _ Vσ VA Rfstnf).
    pose proof (Vfsteqσ := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VA Rfstp Rfsteq).
    epose (Vfstpσ' := consSubstS _ _ Vσ VA Rfstp').
    pose (Vfstnfσ' := consSubstS _ _ Vσ VA Rfstnf').
    pose proof (Vfsteqσ' := consSubstSEq' _ _ Vσ (reflSubst _ _ Vσ) VA Rfstp' Rfsteq').
    instAllValid Vfstpσ Vfstnfσ Vfsteqσ.
    instAllValid Vfstpσ' Vfstnfσ' Vfsteqσ'.
    irrelevance0.
    1: now rewrite subst_sig.
    unshelve eapply (sigEtaRed RΣ0 RVA _ _ Rp Rp') ; tea.
    1,2: rewrite <- subst_fst,<- singleSubstComm'; tea.
    + irrelevance0; rewrite <- subst_fst, <- singleSubstComm'; try reflexivity; tea.
    + now rewrite up_subst_single.
    + irrelevance0; rewrite up_subst_single; try reflexivity; tea.
    + irrelevance0; rewrite up_subst_single; try reflexivity; tea.
    + irrelevance0. 1: now rewrite <- subst_fst, <- singleSubstComm'. tea.
  Qed. 


  
End PairRed.




