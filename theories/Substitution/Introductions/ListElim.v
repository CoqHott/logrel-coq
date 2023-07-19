
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application Universe NormalRed SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var List Poly.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.




Section ListElimRed.
Context `{GenericTypingProperties}.


Lemma consEqRedParam
  {Γ A P hd tl l}
  (RA: [Γ ||-< l > A])
  (RLA: [Γ ||-< l > tList A]) :
  [Γ |- P] ->
  [RA | Γ ||- A ≅ P] ->
  [RA | Γ ||- hd : A] ->
  [RLA | Γ ||- tl : tList A] ->
  [RLA | Γ ||- tCons A hd tl : tList A ] ×
  [RLA | Γ ||- tCons P hd tl : tList A ] ×
  [RLA | Γ ||- tCons A hd tl ≅ tCons P hd tl : tList A ].
Proof.
  intros.
  assert [Γ ||-<l> A ≅ A | RA ] by now eapply LRTyEqRefl_.
  escape; split; [|split].
  1,2: now eapply consRed.
  eapply consEqRed; tea.
  1,2 : now eapply LREqTermRefl_.
Qed.


(* Definition elimListProp {Γ l} A {RLiA : [Γ ||-List<l> tList A]} 
  (P hnil hcons t : term) (Rt : ListProp Γ _ RLiA t) : term.
Proof.
  destruct Rt as [  | | x ].
  - exact hnil.
  - exact (tApp (tApp (tApp hcons hd) tl) (tListElim A P hnil hcons tl)).
  - exact (tListElim A P hnil hcons x).
Defined. *)

Lemma appTerm' {Γ t u F G l X}
  (RΠ : [Γ ||-<l> tProd F G])
  {RF : [Γ ||-<l> F]}
  (Rt : [Γ ||-<l> t : tProd F G | RΠ])
  (Ru : [Γ ||-<l> u : F | RF])
  (eq : X = G[u..])
  (RX : [Γ ||-<l> X]) : 
  [Γ ||-<l> tApp t u : X | RX].
Proof. 
  irrelevance0; [symmetry; tea|].
  unshelve eapply appTerm; cycle 1; tea.
  Unshelve. now rewrite <- eq.
Qed. 


Lemma mkPolyRed {Γ l A B} (wfΓ : [|-Γ])
  (RA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩]) 
  (RB : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> a : _ | RA Δ ρ wfΔ] -> [Δ ||-<l> B[a .: ρ >> tRel]])
  (RBext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (Ra : [Δ ||-<l> a : _ | RA Δ ρ wfΔ]),
    [Δ ||-<l> b : _ | RA Δ ρ wfΔ] ->
    [Δ ||-<l> a ≅ b : _ | RA Δ ρ wfΔ] -> [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a ρ wfΔ Ra]) :
  PolyRed Γ l A B.
Proof.
  assert [Γ |- A] by (eapply escape; now eapply instKripke).
  unshelve econstructor; tea.
  unshelve epose proof (RB _ (tRel 0) (@wk1 Γ A) _ _).
  + gen_typing.
  + eapply var0; tea; now rewrite wk1_ren_on.
  + enough (B = B[tRel 0 .: @wk1 Γ A >> tRel]) as -> by now escape.
    setoid_rewrite wk1_ren; rewrite scons_eta'; now asimpl.
Qed.

Lemma mkPolyRed' {Γ l A B} (RA : [Γ ||-<l> A]) 
  (RB : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> a : _ | wk ρ wfΔ RA] -> [Δ ||-<l> B[a .: ρ >> tRel]])
  (RBext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (Ra : [Δ ||-<l> a : _ | wk ρ wfΔ RA]),
    [Δ ||-<l> b : _ | wk ρ wfΔ RA] ->
    [Δ ||-<l> a ≅ b : _ | wk ρ wfΔ RA] -> [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel] | RB Δ a ρ wfΔ Ra]) :
  PolyRed Γ l A B.
Proof.
  unshelve eapply mkPolyRed; tea.
  escape; gen_typing.
Qed.


Lemma polyRedArrExt {Γ l A B C} : PolyRed Γ l A B -> PolyRed Γ l A C -> PolyRed Γ l A (arr B C).
Proof.
  intros [tyA tyB RA RB RBext] [_ tyC RA' RC RCext].
  opector; tea.
  2: now eapply wft_simple_arr.
  + intros; rewrite subst_arr; refold.
    apply ArrRedTy; [eapply RB| eapply RC]; now irrelevanceRefl.
    Unshelve. all: tea.
  + intros.
    irrelevance0; rewrite subst_arr; [refold; reflexivity|]; refold.
    eapply arrRedCong.
    1,2: eapply escape; first [eapply RB| eapply RC]; now irrelevanceRefl.
    1,2: first [eapply RBext| eapply RCext]; now irrelevanceRefl.
    Unshelve. all: now irrelevanceRefl + tea.
Qed.

Lemma liftSubst_scons_eq {t u v: term} σ : t[u]⇑[v .: σ] = t[u[v .: σ] .: σ].
Proof. now bsimpl. Qed.

Lemma polyRedSubst {Γ l A B t} (PAB : PolyRed Γ l A B) 
  (Rt : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
    [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
  (Rtext : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
    [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> t[a .: ρ >> tRel] ≅ t[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
  : PolyRed Γ l A B[t]⇑.
Proof.
  destruct PAB; opector; tea.
  + intros; rewrite liftSubst_scons_eq.
    unshelve eapply posRed; tea; eapply Rt; now irrelevanceRefl.
  + unshelve epose proof (posRed _ t (@wk1 Γ A) _ _).
    - escape; gen_typing.
    - replace t with t[tRel 0 .: @wk1 Γ A >> tRel].
      2:{ bsimpl; rewrite scons_eta'; now asimpl. }
      eapply Rt.
      eapply var0; tea; now rewrite wk1_ren_on.
    - escape. 
      replace (B[_]) with B[t .: @wk1 Γ A >> tRel]; tea.
      now setoid_rewrite wk1_ren.
  + intros; irrelevance0; rewrite liftSubst_scons_eq;[reflexivity|].
    unshelve eapply posExt; tea; eapply Rt + eapply Rtext; now irrelevanceRefl.
Qed.

Lemma polyRedEqArrExt {Γ l A A' B B' C C'}
  (PAB : PolyRed Γ l A B) (PAC : PolyRed Γ l A C) 
  (PAB' : PolyRed Γ l A' B') (PAC' : PolyRed Γ l A' C') 
  (PABC : PolyRed Γ l A (arr B C))
  (PABeq : PolyRedEq PAB A' B')
  (PACeq : PolyRedEq PAC A' C')
  : PolyRedEq PABC A' (arr B' C').
Proof.
  constructor.
  + intros; irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
  + intros; irrelevance0; rewrite subst_arr; refold; [reflexivity|].
    apply arrRedCong.
    * eapply escape; unshelve eapply (PolyRed.posRed); cycle 1; tea.
      eapply LRTmRedConv; tea; irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
    * eapply escape; unshelve eapply (PolyRed.posRed); cycle 1; tea.
      eapply LRTmRedConv; tea. irrelevanceRefl; now unshelve eapply (PolyRedEq.shpRed PABeq).
    * unshelve eapply (PolyRedEq.posRed PABeq); tea; now irrelevanceRefl.
    * unshelve eapply (PolyRedEq.posRed PACeq); tea; now irrelevanceRefl.
Qed.

Lemma polyRedEqSubst {Γ l A B t u} (PAB : PolyRed Γ l A B) 
  (Rt : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
    [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> t[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
  (Ru : forall Δ a (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
    [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> u[a .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
  (Rtu : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
    [Δ ||-<l> a : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> a ≅ b : _ | PolyRed.shpRed PAB ρ wfΔ] ->
    [Δ ||-<l> t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _ | PolyRed.shpRed PAB ρ wfΔ ])
  (PABt : PolyRed Γ l A B[t]⇑)
  : PolyRedEq PABt A B[u]⇑.
Proof.
  constructor.
  - intros; eapply LRTyEqRefl_.
  - intros; irrelevance0; rewrite liftSubst_scons_eq; [reflexivity|].
    unshelve eapply PolyRed.posExt; cycle 1; tea.
    + eapply Rt; now irrelevanceRefl.
    + eapply Ru; now irrelevanceRefl.
    + eapply Rtu; try eapply LREqTermRefl_; now irrelevanceRefl.
Qed.


Section PolyRedConsHypSubst.
  Context {Γ l A P} (RA : [Γ ||-<l> A]) (PolyP : PolyRed Γ l (tList A) P).

  Section ForHead.
    Context {hd : term} (Rhd : [Γ ||-<l> hd : _ | RA]).

    Lemma consHypSubstConsRed (Δ : context) (a : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) :
      [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- a : (tList A)⟨ρ⟩] ->
      [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- (tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0))[ a .: ρ >> tRel] : (tList A)⟨ρ⟩].
    Proof. 
      intros; cbn; refold.
      rewrite 2! shift_subst_scons.
      unshelve eapply consRed; refold.
      2: eapply escape.
      1,2: now eapply wk.
      all: cbn; refold.
      - eapply  LRTyEqRefl_.
      - now eapply wkTerm.
      - tea.
    Qed.


    Lemma consHypSubstConsRedEq (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) :
      [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- a : (tList A)⟨ρ⟩] ->
      [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- b : (tList A)⟨ρ⟩] ->
      [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- a ≅ b : (tList A)⟨ρ⟩] ->
      [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- (tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0))[ a .: ρ >> tRel] ≅ (tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0))[b .: ρ >> tRel] : (tList A)⟨ρ⟩].
    Proof.
      intros; cbn; refold.
      rewrite 4! shift_subst_scons.
      unshelve eapply consEqRed.
      5,6: eapply escape; now eapply wk.
      all:  try now eapply wk.
      1: now eapply (PolyRed.shpRed PolyP).
      6:  eapply LREqTermRefl_.
      all: (now eapply wkTerm) + eapply LRTyEqRefl_ + tea.
    Qed.

    Lemma polyRedSubstConstConsHyp : PolyRed Γ l (tList A) (P[tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0)]⇑).
    Proof.
      unshelve eapply polyRedSubst; tea.
      + eapply consHypSubstConsRed.
      + eapply consHypSubstConsRedEq.
    Qed.

    Lemma polyRedArrConsHyp : PolyRed Γ l (tList A) (arr P P[tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0)]⇑).
    Proof.
      eapply polyRedArrExt; tea; eapply polyRedSubstConstConsHyp.
    Qed.

  End ForHead.

  Context {hd hd' : term} (Rhd : [Γ ||-<l> hd : _ | RA]) (Rhd' : [Γ ||-<l> hd' : _ | RA]) (Rhdeq : [Γ ||-<l> hd ≅ hd' : _ | RA]).
    
  Lemma consHypSubstConsRedEq' (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) :
    [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- a : (tList A)⟨ρ⟩] ->
    [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- b : (tList A)⟨ρ⟩] ->
    [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- a ≅ b : (tList A)⟨ρ⟩] ->
    [PolyRed.shpRed PolyP ρ wfΔ | Δ ||- (tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0))[ a .: ρ >> tRel] ≅ (tCons A⟨↑⟩ hd'⟨↑⟩ (tRel 0))[b .: ρ >> tRel] : (tList A)⟨ρ⟩].
  Proof.
    intros; cbn; refold.
    rewrite 4! shift_subst_scons.
    unshelve eapply consEqRed.
    5,6: eapply escape; now eapply wk.
    all:  try now eapply wk.
    1: now eapply (PolyRed.shpRed PolyP).
    6: now eapply wkTermEq.
    all: (now eapply wkTerm) + eapply LRTyEqRefl_ + tea.
  Qed.

  Lemma polyRedEqArrConsHyp (Psubsthd : PolyRed Γ l (tList A) (arr P P[tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0)]⇑)) :
    PolyRedEq Psubsthd (tList A) (arr P P[tCons A⟨↑⟩ hd'⟨↑⟩ (tRel 0)]⇑).
  Proof.
    unshelve eapply polyRedEqArrExt; tea.
    1,2: now eapply polyRedSubstConstConsHyp.
    1: constructor; intros; eapply LRTyEqRefl_.
    eapply polyRedEqSubst.
    1,2: now eapply consHypSubstConsRed.
    eapply consHypSubstConsRedEq'.
  Qed.  

End PolyRedConsHypSubst.


Lemma LRPiPoly0 {Γ l A B} (PAB : PolyRed Γ l A B) : [Γ ||-Π<l> tProd A B].
Proof.
  econstructor; tea; pose proof (polyRedId PAB) as []; escape.
  + eapply redtywf_refl; gen_typing.
  + eapply convty_prod; tea; unshelve eapply escapeEq; tea; eapply LRTyEqRefl_.
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

Section ElimConsHyp.
Context {Γ l A P} {hnil hcons hd tl : term}
    (ih := tListElim A P hnil hcons tl)
  (hP : [Γ,, tList A |- P])
  (hPrefl : [Γ,, tList A |- P ≅ P])
  (RA : [Γ ||-<l> A])
  (RLiA0 : [Γ ||-List<l> tList A])
  (RLiA := normList0 RLiA0)
  (RLA := LRList' RLiA)
  (RP : forall t, [Γ ||-<l> t : _ | RLA] -> [Γ ||-<l> P[t..]])
  (PolyP : PolyRed Γ l (tList A) P).


  Lemma elimConsHypTyRed : [Γ ||-<l> elimConsHypTy A P].
  Proof.
    unfold elimConsHypTy.
    assert (h : forall a {Δ Γ} (ρ : Δ ≤ Γ),
     (tProd (tList A⟨↑⟩) (arr P⟨up_ren ↑⟩ P[tCons A⟨↑⟩⟨↑⟩ (tRel 1) (tRel 0) .: (↑ >> ↑) >> tRel])) [a .: ρ >> tRel]
     = tProd (tList A)⟨ρ⟩ (arr P⟨wk_up (tList A) ρ⟩ P⟨wk_up (tList A) ρ⟩[tCons A⟨ρ⟩⟨↑⟩ a⟨↑⟩ (tRel 0)]⇑)).
    1:{ intros. cbn; f_equal; [|f_equal].
      + now rewrite shift_subst_scons.
      + bsimpl; rewrite rinstInst'_term; asimpl; reflexivity.
      + bsimpl; rewrite !rinstInst'_term.
        cbn. asimpl. reflexivity.
    }
    assert (hred : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]),
      [wk ρ wfΔ RA | Δ ||- a : A⟨ρ⟩] ->
      PolyRed Δ l (tList A)⟨ρ⟩ (arr P⟨wk_up (tList A) ρ⟩ P⟨wk_up (tList A) ρ⟩[tCons A⟨ρ⟩⟨↑⟩ a⟨↑⟩ (tRel 0)]⇑)).
    1:{
      intros; unshelve eapply polyRedArrConsHyp; refold.
      + now eapply wk.
      + rewrite wk_list; now eapply wkPoly.
      + cbn; refold; now irrelevanceRefl.
    }
    eapply LRPiPoly. unshelve eapply mkPolyRed'; tea.
    1:  intros; rewrite h; now eapply LRPiPoly.
    intros; irrelevance0; rewrite h; [reflexivity|].
    unshelve eapply LRPiPolyEq.
    - now eapply hred.
    - cbn; refold. eapply polyRedEqArrConsHyp; tea.
      rewrite wk_list at 1; now eapply wkPoly.
    - eapply wft_wk; now escape.
    - unshelve epose proof (polyRedId (hred Δ b ρ wfΔ _)) as [_]; tea.
      now escape.
  Qed.
  
  Lemma elimConsHypAppRed
    (Rtycons : [Γ ||-<l> elimConsHypTy A P]) 
    (Rhcons : [Γ ||-<l> hcons : _ | Rtycons])
    (Rhd : [Γ ||-<l> hd : _ | RA])
    (Rtl : [Γ ||-<l> tl : _ | RLA])
    (Rih : [Γ ||-<l> ih : _ | RP tl Rtl]) 
    (Rcons : [Γ ||-<l> tCons A hd tl : _ | RLA]) :
    [Γ ||-<l> tApp (tApp (tApp hcons hd) tl) ih : _ | RP _ Rcons].
  Proof.
    eapply appTerm'. 2: tea.
    eapply appTerm'. 2: tea.
    eapply appTerm'. 1,2: tea.
    1: cbn; f_equal; clear; now asimpl.
    1: cbn; f_equal; clear; now asimpl.
    clear; now asimpl.
    Unshelve.
    + replace (tProd _ _) with (arr P[tl..] P[(tCons A hd tl)..]).
      2:{ asimpl; cbn. rewrite <- 2!rinstInst'_term. reflexivity. }
      apply ArrRedTy; eapply RP; tea.
    + set (T := P⟨_⟩[_]).
      replace (tProd T _) with (arr P P[(tCons A⟨↑⟩ hd⟨↑⟩ (tRel 0))]⇑).
      2:{ unfold T; asimpl. rewrite !rinstInst'_term, scons_eta'. asimpl. reflexivity. }
      eapply LRPiPoly.
      eapply polyRedArrConsHyp; tea.
  Qed.

End ElimConsHyp.

Context {Γ l A P hnil hcons}
  (RA : [Γ ||-<l> A])
  (RLiA0 : [Γ ||-List<l> tList A])
  (RLiA := normList0 RLiA0)
  (RLA := LRList' RLiA)
  (RP : forall t, [Γ ||-<l> t : _ | RLA] -> [Γ ||-<l> P[t..]])
  (RPeq : forall t u (Rt : [Γ ||-<l> t : _ | RLA]), [Γ ||-<l> u : _ | RLA] -> [Γ ||-<l> t ≅ u : _ | RLA] -> [Γ ||-<l> P[t..] ≅ P[u..]| RP t Rt])
  (PolyP : PolyRed Γ l (tList A) P)
  (Rtynil : [Γ ||-<l> P[(tNil A)..]])
  (Rhnil : [Γ ||-<l> hnil : _ | Rtynil])
  (Rtycons : [Γ ||-<l> elimConsHypTy A P])
  (Rhcons : [Γ ||-<l> hcons : _ | Rtycons]).

Definition listElimProp  t (Rt : ListProp Γ _ RLiA t) : term.
Proof.
  destruct Rt as [  | | x ].
  - exact hnil.
  - exact (tApp (tApp (tApp hcons hd) tl) (tListElim A P hnil hcons tl)).
  - exact (tListElim A P hnil hcons x).
Defined.

Lemma elimListRed : 
  (forall t (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt),
    [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × 
    [Γ ||-<l> tListElim A P hnil hcons t ≅ tListElim A P hnil hcons (ListRedTm.nf Rt) : _ | RPl]) ×
  (forall t (Pt : ListProp Γ _ RLiA t) (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt),
    [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × [Γ ||-<l> tListElim A P hnil hcons t ≅ listElimProp t Pt : _ | RPl]).
Proof.
  pose proof (polyRedId PolyP) as [_ ?].
  assert (hP : [Γ,, tList A |- P]) by now escape.
  assert (hPrefl : [Γ,, tList A |- P ≅ P]) by (eapply escapeEq; now eapply LRTyEqRefl_).
  eapply ListRedInduction.
  + intros.
    eapply redSubstTerm; cycle 1.
    1: destruct red; escape; now eapply redtm_listelim.
    pose proof (wnf := ListProp_whnf prop).
    set (Rt := Build_ListRedTm _ _ _ _  : [Γ ||-<l> t : _ | RLA]).
    pose proof (redTmFwdConv Rt red wnf) as [Rnf Rtnf].
    eapply LRTmRedConv.
    1: unshelve eapply RPeq; cycle 3; [now eapply LRTmEqSym|..]; tea.
    apply (fst (X _)).
  + intros.
    assert [Γ ||-<l> A ≅ P0 | RA] by irrelevance.
    eapply redSubstTerm; cycle 1.
    1: cbn; escape; now eapply redtm_listElimNil.
    eapply LRTmRedConv; tea.
    assert [Γ ||-<l> A ≅ A | RA] by now eapply LRTyEqRefl_.
    escape; irrelevanceRefl; unshelve eapply RPeq.
    1,2: now eapply nilRed.
    eapply nilEqRed; tea.
  + intros ??????? Rtl **. 
    assert [Γ ||-<l> A ≅ P0 | RA] by irrelevance.
    assert [Γ ||-<l> hd : _ | RA] by irrelevance.
    change [Γ ||-<l> tl : _ | RLA] in Rtl.
    eapply redSubstTerm; cycle 1.
    - cbn; escape; eapply redtm_listElimCons; tea.
      1,2: eapply ty_conv; tea.
      now eapply convty_list.
    - eapply LRTmRedConv; cycle 1.
      * eapply elimConsHypAppRed; tea.
        exact (fst X).
        Unshelve. 2: tea. eapply consRed; tea; [now escape| eapply LRTyEqRefl_].
      * pose proof (consEqRedParam RA RLA w X0 X1 Rtl) as [? []].
        irrelevance0.
        2: unshelve eapply RPeq; cycle 2; tea.
        now asimpl.
  + intros.
    assert [Γ ||-<l> A ≅ A | RA] by now eapply LRTyEqRefl_.
    assert [Γ ||-<l> hnil ≅ hnil : _ | Rtynil] by now eapply LREqTermRefl_.
    assert [Γ ||-<l> hcons ≅ hcons : _ | Rtycons] by now eapply LREqTermRefl_.
    escape; eapply completeness.
    1,2: now eapply ty_listElim.
    now eapply convneu_listElim.
  Qed.


End ListElimRed.
