From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedValues Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Universe Poly.

Set Universe Polymorphism.

(* Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed. *)

Section PolyRedPi.
  Context `{GenericTypingProperties}.

  Lemma LRPiPoly0 {Γ l A B} (PAB : PolyRed Γ l A B) : [Γ ||-Π<l> tProd A B].
  Proof.
    econstructor; tea; pose proof (polyRedId PAB) as []; escape.
    + eapply redtywf_refl; gen_typing.
    + eapply convty_prod; tea; unshelve eapply escapeEq; tea; eapply reflLRTyEq.
  Defined.

  Definition LRPiPoly {Γ l A B} (PAB : PolyRed Γ l A B) : [Γ ||-<l> tProd A B] := LRPi' (LRPiPoly0 PAB).

  Lemma LRPiPolyEq0 {Γ l A A' B B'} (PAB : PolyRed Γ l A B) (Peq : PolyRedEq PAB A' B') :
    [Γ |- A'] -> [Γ ,, A' |- B'] ->
    [Γ ||-Π tProd A B ≅ tProd A' B' | LRPiPoly0 PAB].
  Proof.
    econstructor; cbn; tea.
    + eapply redtywf_refl; gen_typing.
    + pose proof (polyRedEqId PAB Peq) as []; escape.
      eapply convty_prod; tea.
      eapply escape; now apply (polyRedId PAB).
  Qed.

  Lemma LRPiPolyEq {Γ l A A' B B'} (PAB : PolyRed Γ l A B) (Peq : PolyRedEq PAB A' B') :
    [Γ |- A'] -> [Γ ,, A' |- B'] ->
    [Γ ||-<l> tProd A B ≅ tProd A' B' | LRPiPoly PAB].
  Proof.
    now eapply LRPiPolyEq0.
  Qed.

  Lemma LRPiPolyEq' {Γ l A A' B B'} (PAB : PolyRed Γ l A B) (Peq : PolyRedEq PAB A' B') (RAB : [Γ ||-<l> tProd A B]):
    [Γ |- A'] -> [Γ ,, A' |- B'] ->
    [Γ ||-<l> tProd A B ≅ tProd A' B' | RAB].
  Proof.
    intros; irrelevanceRefl; now eapply LRPiPolyEq.
  Qed.
  
End PolyRedPi.


Section PiTyValidity.

  Context `{GenericTypingProperties}.
  Context {l Γ F G} (vΓ : [||-v Γ])
    (vF : [Γ ||-v< l > F | vΓ ])
    (vG : [Γ ,, F ||-v< l > G | validSnoc vΓ vF]).

  Lemma PiRed {Δ σ} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > (tProd F G)[σ] ].
  Proof.
    eapply LRPi'.
    pose (p := substPolyRed vΓ vF vG _ vσ).
    escape; cbn; econstructor; tea;
    destruct (polyRedId p);
    destruct (polyRedEqId p (substPolyRedEq vΓ vF vG _ vσ vσ (reflSubst _ _ vσ))); escape.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
  Defined.

  Lemma PiEqRed1 {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    (vσ' : [vΓ | Δ ||-v σ' : _ | tΔ])
    (vσσ' : [vΓ | Δ ||-v σ ≅ σ' : _ | tΔ | vσ])
    : [ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F G)[σ'] | PiRed tΔ vσ ].
  Proof.
    pose (p := substPolyRed vΓ vF vG _ vσ).
    pose (p' := substPolyRed vΓ vF vG _ vσ').
    pose (peq := substPolyRedEq vΓ vF vG _ vσ vσ' vσσ').
    destruct (polyRedId p); destruct (polyRedId p'); destruct (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
  Defined.

  Lemma PiValid : [Γ ||-v< l > tProd F G | vΓ].
  Proof.
    unshelve econstructor.
    - intros Δ σ. eapply PiRed.
    - intros Δ σ σ'. eapply PiEqRed1.
  Defined.

End PiTyValidity.


Section PiTyCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G' l}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< l > F | vΓ ])
    (vG : [ Γ ,, F ||-v< l > G | validSnoc vΓ vF ])
    (vF' : [ Γ ||-v< l > F' | vΓ ])
    (vG' : [ Γ ,, F' ||-v< l > G' | validSnoc vΓ vF' ])
    (vFF' : [ Γ ||-v< l > F ≅ F' | vΓ | vF ])
    (vGG' : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc vΓ vF | vG ]).

  Lemma PiEqRed2 {Δ σ} (tΔ : [ |-[ ta ] Δ]) (vσ : [vΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< l > (tProd F G)[σ] ≅ (tProd F' G')[σ] | validTy (PiValid vΓ vF vG) tΔ vσ ].
  Proof.
    pose (p := substPolyRed vΓ vF vG _ vσ).
    pose (p' := substPolyRed vΓ vF' vG' _ vσ).
    pose (peq := substEqPolyRedEq vΓ vF vG _ vσ vF' vG' vFF' vGG').
    destruct (polyRedId p); destruct (polyRedId p'); destruct (polyRedEqId p peq).
    escape; econstructor; cbn; tea.
    - apply redtywf_refl; gen_typing.
    - gen_typing.
  Qed.

  Lemma PiCong : [ Γ ||-v< l > tProd F G ≅ tProd F' G' | vΓ | PiValid vΓ vF vG ].
  Proof.
    econstructor. intros Δ σ. eapply PiEqRed2.
  Qed.

End PiTyCongruence.


Section PiTmValidity.

  Context `{GenericTypingProperties}.
  Context {Γ F G} (VΓ : [||-v Γ])
    (VF : [ Γ ||-v< one > F | VΓ ])
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFU : [ Γ ||-v< one > F : U | VΓ | UValid VΓ ])
    (VGU : [ Γ ,, F ||-v< one > G : U | validSnoc VΓ VF | VU ]) .
    (* (VF := univValid (l':=zero) _ _ vFU)
    (VG := univValid (l':=zero) _ _ vGU). *)

  Lemma prodTyEqU {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (Vσ : [VΓ | Δ ||-v σ : _ | tΔ])
    (Vσ' : [VΓ | Δ ||-v σ' : _ | tΔ])
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ | Vσ ])
    : [Δ |-[ ta ] tProd F[σ] G[up_term_term σ] ≅ tProd F[σ'] G[up_term_term σ'] : U].
  Proof.
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vureaσ' := liftSubstSrealign' VF Vσσ' Vσ').
    pose proof (Vuσσ' := liftSubstSEq' VF Vσσ').
    instAllValid Vσ Vσ' Vσσ'; instAllValid Vuσ Vureaσ' Vuσσ'; escape.
    eapply convtm_prod; tea.
  Qed.

  Lemma PiRedU {Δ σ} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ : _ | tΔ])
    : [ Δ ||-< one > (tProd F G)[σ] : U | validTy (UValid VΓ) tΔ Vσ ].
  Proof.
    pose proof (Vσσ := reflSubst _ _ Vσ).
    pose proof (Vuσ := liftSubstS' VF Vσ).
    pose proof (Vuσσ := liftSubstSEq' VF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; escape.
    econstructor; cbn.
    - apply redtmwf_refl; cbn in *; now eapply ty_prod.
    - constructor.
    - now eapply convtm_prod.
    - cbn. unshelve refine (LRCumulative (PiRed _ _ _ tΔ Vσ));
      unshelve eapply univValid; tea; try irrValid.
  Defined.

  Lemma PiValidU : [ Γ ||-v< one > tProd F G : U | VΓ | UValid VΓ ].
  Proof.
    econstructor.
    - intros Δ σ tΔ Vσ.
      exact (PiRedU tΔ Vσ).
    - intros Δ σ σ' tΔ Vσ Vσ' Vσσ'.
      pose proof (univValid (l' := zero) _ _ VFU) as VF0.
      pose proof (irrelevanceValidity (validSnoc VΓ VF)
                    (validSnoc (l := zero) VΓ VF0)
                    (univValid (l' := zero) _ _ VGU)) as VG0.
      unshelve econstructor ; cbn.
      + exact (PiRedU tΔ Vσ).
      + exact (PiRedU tΔ Vσ').
      + exact (LRCumulative (PiRed VΓ VF0 VG0 tΔ Vσ)).
      + exact (prodTyEqU tΔ Vσ Vσ' Vσσ').
      + exact (LRCumulative (PiRed VΓ VF0 VG0 tΔ Vσ')).
      + pose proof (PiEqRed1 VΓ VF0 VG0 tΔ Vσ Vσ' Vσσ').
        irrelevanceCum.
  Qed.

End PiTmValidity.


Section PiTmCongruence.

  Context `{GenericTypingProperties}.
  Context {Γ F G F' G'}
    (vΓ : [||-v Γ])
    (vF : [ Γ ||-v< one > F | vΓ ])
    (vU : [ Γ ,, F ||-v< one > U | validSnoc vΓ vF ])
    (vFU : [ Γ ||-v< one > F : U | vΓ | UValid vΓ ])
    (vGU : [ Γ ,, F ||-v< one > G : U | validSnoc vΓ vF | vU ])
    (vF' : [ Γ ||-v< one > F' | vΓ ])
    (vU' : [ Γ ,, F' ||-v< one > U | validSnoc vΓ vF' ])
    (vF'U : [ Γ ||-v< one > F' : U | vΓ | UValid vΓ ])
    (vG'U : [ Γ ,, F' ||-v< one > G' : U | validSnoc vΓ vF' | vU' ])
    (vFF' : [ Γ ||-v< one > F ≅ F' : U | vΓ | UValid vΓ ])
    (vGG' : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc vΓ vF | vU ]).

  Lemma PiCongTm : [ Γ ||-v< one > tProd F G ≅ tProd F' G' : U | vΓ | UValid vΓ ].
  Proof.
    econstructor.
    intros Δ σ tΔ Vσ.
    pose proof (univValid (l' := zero) _ _ vFU) as vF0.
    pose proof (univValid (l' := zero) _ _ vF'U) as vF'0.
    pose proof (Vσσ := reflSubst _ _ Vσ).
    pose proof (Vuσ := liftSubstS' vF Vσ).
    pose proof (Vuσσ := liftSubstSEq' vF Vσσ).
    instAllValid Vσ Vσ Vσσ; instAllValid Vuσ Vuσ Vuσσ; escape.
    pose proof (irrelevanceValidity (validSnoc vΓ vF)
                  (validSnoc (l := zero) vΓ vF0)
                  (univValid (l' := zero) _ _ vGU)) as vG0.
    pose proof (irrelevanceValidity (validSnoc vΓ vF')
                  (validSnoc (l := zero) vΓ vF'0)
                  (univValid (l' := zero) _ _ vG'U)) as vG'0.
    unshelve econstructor ; cbn.
    - exact (PiRedU vΓ vF vU vFU vGU tΔ Vσ).
    - exact (PiRedU vΓ vF' vU' vF'U vG'U tΔ Vσ).
    - exact (LRCumulative (PiRed vΓ vF0 vG0 tΔ Vσ)).
    - now eapply convtm_prod.
    - exact (LRCumulative (PiRed vΓ vF'0 vG'0 tΔ Vσ)).
    - enough ([ Δ ||-< zero > (tProd F G)[σ] ≅ (tProd F' G')[σ] | PiRed vΓ vF0 vG0 tΔ Vσ]) by irrelevanceCum.
      refine (PiEqRed2 vΓ vF0 vG0 vF'0 vG'0 _ _ tΔ Vσ).
      + exact (univEqValid vΓ (UValid vΓ) vF0 vFF').
      + pose proof (univEqValid (validSnoc vΓ vF) vU (univValid (l' := zero) _ _ vGU) vGG') as vGG'0.
        refine (irrelevanceEq _ _ _ _ vGG'0).
  Qed.

End PiTmCongruence.

