From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst.

Set Universe Polymorphism.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Program Definition normRedΠ0 {Γ nF F G l} (h : [Γ ||-Π<l> tProd nF F G])
  : [Γ ||-Π<l> tProd nF F G] :=
  {| PiRedTyPack.na := nF ; 
     PiRedTyPack.dom := F ;
     PiRedTyPack.cod := G |}.
Solve All Obligations with 
  intros;
  assert (wΠ : whnf (tProd nF F G)) by constructor;
  pose proof (e := redtywf_whnf (PiRedTyPack.red h) wΠ);
  symmetry in e; injection e; clear e; 
  destruct h as [??????? domRed codRed codExt] ; 
  intros; cbn in *; subst; eassumption + now eapply domRed + 
  (unshelve eapply codRed ; tea ; irrelevance)
  + ( irrelevance0; [reflexivity| unshelve eapply codExt; tea]; irrelevance).

Definition normRedΠ {Γ nF F G l} (h : [Γ ||-<l> tProd nF F G])
  : [Γ ||-<l> tProd nF F G] :=
  LRPi' _ (normRedΠ0 (invLRΠ h)).

Lemma app_id {Γ t u nF F G l}
  (RΠ : [Γ ||-<l> tProd nF F G])
  (RF : [Γ ||-<l> F])
  (Rt : [Γ ||-<l> t : tProd nF F G | normRedΠ RΠ])
  (Ru : [Γ ||-<l> u : F | RF])
  (RGu : [Γ ||-<l> G[u..]]) :
    [Γ ||-<l> tApp (PiRedTm.nf Rt) u : G[u..] | RGu].
Proof.
  assert (wfΓ := wfc_wft (escape_ RF)).
  replace (PiRedTm.nf _) with (PiRedTm.nf Rt)⟨@wk_id Γ⟩ by now bsimpl.
  irrelevance0.  2: eapply (PiRedTm.app Rt).
  cbn; now bsimpl.
  Unshelve. 1: eassumption.
  cbn; irrelevance0; tea; now bsimpl.
Qed.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Typeclasses Opaque ConvType.
Typeclasses Opaque RedTerm.

Lemma appValid {Γ nF F G t u l}
  (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΠFG : [Γ ||-v<l> tProd nF F G | VΓ])
  (Vt : [Γ ||-v<l> t : tProd nF F G | VΓ | VΠFG])
  (Vu : [Γ ||-v<l> u : F | VΓ | VF]) :
  [Γ ||-v<l> tApp t u : G[u..] | VΓ | substSΠ VΓ VF VΠFG Vu].
Proof.
  opector; intros.
  - pose (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ)); refold. 
    assert (Rt :[Δ ||-<l> t[σ] : (tProd nF F G)[σ] | RΠFG ])
    by (epose proof (validTm Vt wfΔ Vσ); irrelevance).
    pose proof (Ru := validTm Vu wfΔ Vσ).
    unshelve irrelevance0.
    3: now eapply substSΠaux.
    1: now bsimpl.
    eapply redSubstTerm. 
    2:{
      eapply redtmwf_app; refold.
      1: exact (PiRedTm.red Rt).
      cbn;  eapply escapeTerm_; exact Ru.
    }
    eapply app_id; tea.
  - pose (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ)); refold. 
      assert (Rt :[Δ ||-<l> t[σ] : (tProd nF F G)[σ] | RΠFG ])
      by (epose proof (validTm Vt wfΔ Vσ); irrelevance).
      pose proof (Ru := validTm Vu wfΔ Vσ).

  
  unshelve irrelevance0.
    3: eapply (substSΠaux VΓ VF VΠFG Vu _ _ wfΔ Vσ).
    1: now bsimpl.
    eapply transEqTerm; [| eapply transEqTerm; eapply LRTmEqSym].
    +       eapply redSubstTerm. 
      2:{
        eapply redtmwf_app; refold.
        1: exact (PiRedTm.red Rt).
        cbn;  eapply escapeTerm_; exact Ru.
      }
      eapply app_id; tea.

    eapply redSubstEqTerm.