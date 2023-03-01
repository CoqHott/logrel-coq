From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.

Set Universe Polymorphism.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Definition Block (A : Type) := A.

Ltac block H :=
  let T := type of H in (change T with (Block T) in H).

Ltac unblock := unfold Block in *.

Ltac instValid wfΔ vσ :=
  repeat lazymatch goal with
  | [H : typeValidity _ _ _ _ |- _] => 
    let X := fresh "R" H in
    pose (X := validTy H wfΔ vσ) ;
    block H
  | [H : termValidity _ _ _ _ _ _ |- _] => 
    let X := fresh "R" H in
    pose (X := validTm H wfΔ vσ) ;
    block H
  end; unblock.


Lemma appValid {Γ nF F G t u l}
  (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΠFG : [Γ ||-v<l> tProd nF F G | VΓ])
  (Vt : [Γ ||-v<l> t : tProd nF F G | VΓ | VΠFG])
  (Vu : [Γ ||-v<l> u : F | VΓ | VF]) 
  (VGu := substSΠ VΠFG Vu) :
  [Γ ||-v<l> tApp t u : G[u..] | VΓ | VGu].
Proof. 
  opector; intros.
  - instValid wfΔ Vσ.
    epose (appTerm RVΠFG RVt RVu (substSΠaux VΠFG Vu _ _ wfΔ Vσ)); refold.
    irrelevance. 
  - instValid wfΔ Vσ; instValid wfΔ Vσ'.
    epose app
  irrelevance0.
    2:

  assert (forall Δ σ (wfΔ : [|-Δ]) (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ])
    (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ))
    (Rt : [Δ ||-<l> t[σ] : (tProd nF F G)[σ] | RΠFG ])
    (RGu := substSΠaux VΠFG Vu _ _ wfΔ Vσ)
    A (RA : [Δ ||-<l> A])
    (Gueq : [Δ ||-<l> G[up_term_term σ][u[σ]..] ≅ A | RGu]),
    [RA | Δ ||- (tApp t u)[σ] : _] × 
    [RA | Δ ||- (tApp t u)[σ] ≅ tApp (PiRedTm.nf Rt) u[σ] : _]
  ).
  1:{
    refold; intros.
    eapply redSubstTerm. 
    2:{
      eapply redtmwf_conv.
      2: now eapply escapeEq_.
      eapply redtmwf_app; refold.
      1: exact (PiRedTm.red Rt).
      cbn;  eapply escapeTerm_; now eapply validTm.
    }
    eapply LRTmRedConv; tea.
    eapply app_id; tea; now eapply validTm.
    Unshelve. all: tea.
  }
  opector; intros.
  - unshelve eapply X; tea.
    1: epose proof (validTm Vt wfΔ Vσ); irrelevance.
    rewrite singleSubstComm'; eapply LRTyEqRefl_.
  - pose (RΠFG := normRedΠ (validTy VΠFG wfΔ Vσ)); refold. 
    assert [Δ ||-<l> t[σ] ≅ t[σ'] : (tProd nF F G)[σ] | RΠFG ] as [Rt Rt' ? eqApp]
      by (epose proof (validTmExt Vt wfΔ Vσ Vσ' Vσσ'); irrelevance).
    pose (RGu := substSΠaux VΠFG Vu _ _ wfΔ Vσ).
    assert [Δ ||-<l> _ ≅ G[u..][σ] | RGu]
      by (rewrite singleSubstComm'; eapply LRTyEqRefl_).
    unshelve epose proof (X _ _ wfΔ Vσ Rt _ _ X0).
    1: now eapply substSΠ. cbn in X1.
    assert [Δ ||-<l> _ ≅ G[u..][σ'] | RGu].
    {
      rewrite singleSubstComm'.
      irrelevance0. 1: reflexivity.
      eapply singleSubstΠ2.
       * now eapply (validTyExt VΠFG).
       * now eapply validTm.
       * now eapply validTm.
       * now eapply validTmExt.
       * now eapply substSΠaux.
      Unshelve. 2,3:tea. now eapply substSΠaux.
    }
    unshelve epose proof (X _ _ wfΔ Vσ' Rt' _ _ X2).
    2: now eapply substSΠaux.
    1:{ 
     eapply LRTmRedConv.
     2: exact (Rt' : [_ ||-<_> _ : _ | RΠFG ]).
     pose proof (validTyExt VΠFG _ _ Vσ' Vσσ'); irrelevance.
    }
    cbn in X1.
    pose proof (Ru := validTm Vu wfΔ Vσ).
    pose proof (symmetrySubstEq _ _ wfΔ _ _ Vσ' Vσσ').
    assert (Ru' : [validTy VF wfΔ Vσ| Δ ||- u[σ'] : F[σ]])
      by (epose proof (validTm Vu wfΔ Vσ'); eapply LRTmRedConv; tea; now eapply validTyExt).
    unshelve irrelevance0.
    3: eapply (substSΠaux VΓ VF VΠFG Vu _ _ wfΔ Vσ).
    1: now bsimpl.
    eapply transEqTerm; [| eapply transEqTerm; cycle 1].
    + eapply redSubstTerm. 
      2:{
        eapply redtmwf_app; refold.
        1: exact (PiRedTm.red Rt).
        cbn;  eapply escapeTerm_; exact Ru.
      }
      eapply app_id; tea.
    +  eapply LRTmEqSym ; eapply LRTmEqRedConv.
      2:{
        eapply redSubstTerm.
        2:{
          eapply redtmwf_app; refold.
          1: exact (PiRedTm.red Rt').
          cbn;  eapply escapeTerm_; exact Ru'.
        } 
        eapply app_id; tea. 
      } 
      eapply singleSubstΠ2; tea; refold.
      * now eapply (validTyEq (reflValidTy _ VΠFG) wfΔ Vσ).
      * eapply LRTmEqSym; now eapply (validTmExt Vu).
      * now eapply substSΠaux.
      Unshelve. refold; cbn. 
      eapply singleSubstΠ1; tea.
    + refold.
      replace (PiRedTm.nf Rt) with (PiRedTm.nf Rt)⟨@wk_id Δ⟩ by now bsimpl.
      replace (PiRedTm.nf Rt') with (PiRedTm.nf Rt')⟨@wk_id Δ⟩ by now bsimpl.
      irrelevance0. 
      2: eapply eqApp. (PiRedTmEq.eqApp Rtt').
  cbn; now bsimpl.
  Unshelve. 1: eassumption.
  cbn; irrelevance0; tea; now bsimpl.

    eapply redSubstEqTerm.