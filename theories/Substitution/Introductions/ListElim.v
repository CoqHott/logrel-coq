
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

Lemma appcongTerm' {Γ t t' u u' F F' G l l' X}
  (RΠ : [Γ ||-<l> tProd F G]) 
  {RF : [Γ ||-<l'> F]}
  {RF' : [Γ ||-<l'> F']}
  (RFF' : [Γ ||-<l'> F ≅ F' | RF])
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ])
  (Ru : [Γ ||-<l'> u : F | RF])
  (Ru' : [Γ ||-<l'> u' : F' | RF'])
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> X])
   : X = G[u..] ->
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : X | RGu].
Proof.
  intros eq.
  irrelevance0 ; [symmetry; apply eq|].
  eapply appcongTerm; tea.
  eapply LRTmRedConv; tea.
  now eapply LRTyEqSym.
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

  Context {A' P'} {hnil' hcons' hd' tl' : term}
      (ih' := tListElim A' P' hnil' hcons' tl')
    (RA' : [Γ ||-<l> A'])
    (RAA' : [Γ ||-<l> A ≅ A' | RA])
    (RLiA0' : [Γ ||-List<l> tList A'])
    (RLiA' := normList0 RLiA0')
    (RLA' := LRList' RLiA')
    (RLAeq : [Γ ||-<l> _ ≅ tList A' | RLA])
    (RP' : forall t, [Γ ||-<l> t : _ | RLA'] -> [Γ ||-<l> P'[t..]])
    (* (RPeq' : forall t u (Rt : [Γ ||-<l> t : _ | RLA']), [Γ ||-<l> u : _ | RLA'] -> [Γ ||-<l> t ≅ u : _ | RLA'] -> [Γ ||-<l> P'[t..] ≅ P'[u..]| RP' t Rt]) *)
    (RPP' : forall t u (Rt : [Γ ||-<l> t : _ | RLA]), [Γ ||-<l> u : _ | RLA] -> [Γ ||-<l> t ≅ u : _ | RLA] -> [Γ ||-<l> P[t..] ≅ P'[u..]| RP t Rt]).
    (* (PolyP' : PolyRed Γ l (tList A') P')
    (PolyPeq : PolyRedEq PolyP (tList A') P'). *)


  Lemma elimConsHypAppEqRed
    (Rtycons : [Γ ||-<l> elimConsHypTy A P])
    (Rhcons : [Γ ||-<l> hcons : _ | Rtycons])
    (Rtycons' : [Γ ||-<l> elimConsHypTy A' P'])
    (Rhcons' : [Γ ||-<l> hcons' : _ | Rtycons'])
    (Rhconseq : [Γ ||-<l> hcons ≅ hcons' : _ | Rtycons])

    (Rhd : [Γ ||-<l> hd : _ | RA])
    (Rhd' : [Γ ||-<l> hd' : _ | RA'])
    (Rhdeq : [Γ ||-<l> hd ≅ hd' : _ | RA])

    (Rtl : [Γ ||-<l> tl : _ | RLA])
    (Rtl' : [Γ ||-<l> tl' : _ | RLA'])
    (Rtleq : [Γ ||-<l> tl ≅ tl' : _ | RLA])

    (Rih : [Γ ||-<l> ih : _ | RP tl Rtl]) 
    (Rih' : [Γ ||-<l> ih' : _ | RP' tl' Rtl']) 
    (Riheq : [Γ ||-<l> ih ≅ ih' : _ | RP tl Rtl]) 

    (Rcons : [Γ ||-<l> tCons A hd tl : _ | RLA]) 
    (Rcons' : [Γ ||-<l> tCons A' hd' tl' : _ | RLA']) 
    (Rconseq : [Γ ||-<l> tCons A hd tl ≅ tCons A' hd' tl' : _ | RLA]) 
    
    : [Γ ||-<l> tApp (tApp (tApp hcons hd) tl) ih ≅ tApp (tApp (tApp hcons' hd') tl') ih' : _ | RP _ Rcons].
  Proof.
    eapply appcongTerm'; cycle 2; tea; [shelve|..].
    1: eapply RPP'; tea; eapply LRTmRedConv; tea; now eapply LRTyEqSym.
    eapply appcongTerm'; cycle 2; tea; [shelve|..].
    eapply appcongTerm'; cycle 2; tea.
    cbn; f_equal; now bsimpl.
    Unshelve.
    5:{ cbn. f_equal. bsimpl. now cbn. }
    2:{ now asimpl. }
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

Lemma redSubstTerm' {Γ A t u l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u : A | RA] ->
  [Γ |- t ⇒* u : A ] ->
  [Γ ||-<l> t : A | RA] ×  
  [Γ ||-<l> u : A | RA] ×
  [Γ ||-<l> t ≅ u : A | RA].
Proof.
  intros. assert ([Γ ||-<l> t : A | RA] × [Γ ||-<l> t ≅ u : A | RA]) by now eapply redSubstTerm.
  now repeat split.
Qed.

Section EliminatorReducibility.
Context {Γ l A P hnil hcons}
  (RA : [Γ ||-<l> A])
  (RLiA0 : [Γ ||-List<l> tList A])
  (RLiA := normList0 RLiA0)
  (RLA := LRList' RLiA)
  (PolyP : PolyRed Γ l (tList A) P)
  (RP := polyCodSubstRed RLA PolyP)
  (RPeq := polyCodSubstExtRed RLA PolyP)
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

Lemma elimListRed_mut : 
  (forall t (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt),
    [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × 
    [Γ ||-<l> tListElim A P hnil hcons (ListRedTm.nf Rt) : _ | RPl] × 
    [Γ ||-<l> tListElim A P hnil hcons t ≅ tListElim A P hnil hcons (ListRedTm.nf Rt) : _ | RPl]) ×
  (forall t (Pt : ListProp Γ _ RLiA t) (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt),
    [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × 
    [Γ ||-<l> listElimProp t Pt : _ | RPl] × 
    [Γ ||-<l> tListElim A P hnil hcons t ≅ listElimProp t Pt : _ | RPl]).
Proof.
  pose proof (polyRedId PolyP) as [_ ?].
  assert (hP : [Γ,, tList A |- P]) by now escape.
  assert (hPrefl : [Γ,, tList A |- P ≅ P]) by (eapply escapeEq; now eapply LRTyEqRefl_).
  eapply ListRedInduction.
  + intros.
    eapply redSubstTerm'; cycle 1.
    1: destruct red; escape; now eapply redtm_listelim.
    pose proof (wnf := ListProp_whnf prop).
    set (Rt := Build_ListRedTm _ _ _ _  : [Γ ||-<l> t : _ | RLA]).
    pose proof (redTmFwdConv Rt red wnf) as [Rnf Rtnf].
    eapply LRTmRedConv.
    1: unshelve eapply RPeq; cycle 3; [now eapply LRTmEqSym|..]; tea.
    apply (fst (X _)).
  + intros.
    assert [Γ ||-<l> A ≅ P0 | RA] by irrelevance.
    eapply redSubstTerm'; cycle 1.
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
    eapply redSubstTerm'; cycle 1.
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
    cbn.
    match goal with |- _ × ?G => enough (h : G) by (split; [apply h| tea]) end.
    escape; eapply completeness.
    1,2: now eapply ty_listElim.
    now eapply convneu_listElim.
  Qed.

  Lemma elimListRed t (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt) :
      [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] × 
      [Γ ||-<l> tListElim A P hnil hcons (ListRedTm.nf Rt) : _ | RPl] × 
      [Γ ||-<l> tListElim A P hnil hcons t ≅ tListElim A P hnil hcons (ListRedTm.nf Rt) : _ | RPl].
  Proof. 
    apply elimListRed_mut.
  Qed.

  Lemma elimListProp  t (Pt : ListProp Γ _ RLiA t) (Rt : [Γ ||-<l> t : _ | RLA]) (RPl := RP t Rt) :
      [Γ ||-<l> tListElim A P hnil hcons t : _ | RPl] ×
      [Γ ||-<l> listElimProp t Pt : _ | RPl] ×
      [Γ ||-<l> tListElim A P hnil hcons t ≅ listElimProp t Pt : _ | RPl].
  Proof. apply elimListRed_mut. Qed.

End EliminatorReducibility.

Lemma ListRedTmFwd {Γ l A t} (RA : [Γ ||-<l> A]) (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA)
  (Rt : [Γ ||-<l> t : _ | RLA]) : [Γ ||-<l> ListRedTm.nf Rt : _ | RLA] × [Γ ||-<l> t ≅ ListRedTm.nf Rt : _ | RLA].
Proof. eapply redTmFwdConv; tea; [eapply (ListRedTm.red Rt)| eapply ListProp_whnf; eapply (ListRedTm.prop Rt)]. Qed.

Lemma ListRedTm_det {Γ l A A' t} (RA : [Γ ||-<l> A]) (RA' : [Γ ||-<l> A'])
  (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA)
  (RLiA0' : [Γ ||-List<l> tList A']) (RLiA' := normList0 RLiA0') (RLA' := LRList' RLiA')
  (Rt : [Γ ||-<l> t : _ | RLA]) (Rt' : [Γ ||-<l> t : _ | RLA']) : ListRedTm.nf Rt = ListRedTm.nf Rt'.
Proof.
  eapply redtmwf_det.
  1,2: eapply ListProp_whnf; eapply ListRedTm.prop.
  1,2: eapply ListRedTm.red.
Qed.

Lemma ListRedTm_whnf {Γ l A t} (RA : [Γ ||-<l> A]) (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA)
  (Rt : [Γ ||-<l> t : _ | RLA]) : whnf t -> ListRedTm.nf Rt = t.
Proof.
  intros; symmetry; eapply redtmwf_whnf; tea.
  eapply ListRedTm.red.
Qed.

Lemma ListRedTm_prop_whnf {Γ l A t} (RA : [Γ ||-<l> A]) (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA)
  (Rt : [Γ ||-<l> t : _ | RLA]) : whnf t -> ListProp Γ _ RLiA t.
Proof.
  intros. erewrite <- ListRedTm_whnf.
  1: eapply ListRedTm.prop.
  all: tea.
  Unshelve. tea.
Qed.

Lemma ListProp_nil_inv {Γ l A P} (RA : [Γ ||-<l> A]) (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA) :
  ListProp Γ _ RLiA (tNil P) -> ListProp Γ _ RLiA (tNil P).
Proof.
  intros Rt.  
  econstructor; inversion Rt; tea; try (eapply convneulist_whne_list in refl; do 2 inv_whne); now irrelevanceRefl.
  Unshelve. escape; now gen_typing.
Defined.

Lemma ListProp_cons_inv0 {Γ l A P hd tl} (RA : [Γ ||-<l> A]) (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA) :
  ListProp Γ _ RLiA (tCons P hd tl) -> 
  [× [Γ |- P], 
    [Γ ||-<l> A ≅ P | RA],
    [Γ ||-<l> hd : _ | RA] &
    [Γ ||-<l> tl : _ | RLA]].
Proof.
  intros Rt; inversion Rt; tea; try (eapply convneulist_whne_list in refl; do 2 inv_whne).
  subst; split; tea; irrelevance.
Qed.

Lemma ListProp_cons_inv {Γ l A P hd tl} (RA : [Γ ||-<l> A]) (RLiA0 : [Γ ||-List<l> tList A]) (RLiA := normList0 RLiA0) (RLA := LRList' RLiA) :
  ListProp Γ _ RLiA (tCons P hd tl) -> ListProp Γ _ RLiA (tCons P hd tl).
Proof.
  intros Rt; econstructor; pose proof (ListProp_cons_inv0 RA _ Rt) as []; tea; irrelevance.
  Unshelve. escape; now gen_typing.
Defined.


Context {Γ l A A' P P' hnil hnil' hcons hcons'}
  (RA : [Γ ||-<l> A])
  (RA' : [Γ ||-<l> A'])
  (RAA' : [Γ ||-<l> A ≅ A' | RA])

  (RLiA0 : [Γ ||-List<l> tList A])
  (RLiA := normList0 RLiA0)
  (RLA := LRList' RLiA)
  (RLiA0' : [Γ ||-List<l> tList A'])
  (RLiA' := normList0 RLiA0')
  (RLA' := LRList' RLiA')

  (PolyP : PolyRed Γ l (tList A) P)
  (PolyP' : PolyRed Γ l (tList A') P')
  (PolyPeq : PolyRedEq PolyP (tList A') P')

  (RP := polyCodSubstRed RLA PolyP)
  (RP' := polyCodSubstRed RLA' PolyP')
  (RPeq := polyCodSubstExtRed RLA PolyP)
  (RPeq' := polyCodSubstExtRed RLA' PolyP')


  (Rtynil : [Γ ||-<l> P[(tNil A)..]])
  (Rhnil : [Γ ||-<l> hnil : _ | Rtynil])
  (Rtynil' : [Γ ||-<l> P'[(tNil A')..]])
  (Rhnil' : [Γ ||-<l> hnil' : _ | Rtynil'])
  (Rhnileq : [Γ ||-<l> hnil ≅ hnil' : _ | Rtynil])

  (Rtycons : [Γ ||-<l> elimConsHypTy A P])
  (Rhcons : [Γ ||-<l> hcons : _ | Rtycons])
  (Rtycons' : [Γ ||-<l> elimConsHypTy A' P'])
  (Rhcons' : [Γ ||-<l> hcons' : _ | Rtycons'])
  (Rhconseq : [Γ ||-<l> hcons ≅ hcons' : _ | Rtycons]).


  Let listElimProp' := @listElimProp Γ l A' P' hnil' hcons' RLiA0'.
  Let listElimProp := @listElimProp Γ l A P hnil hcons RLiA0.


  Let QRed t u (Rtu : [Γ ||-<l> t ≅ u: _ | RLA]) :=
      let RPl := RP t (ListRedTmEq.redl Rtu) in [Γ ||-<l> tListElim A P hnil hcons t ≅ tListElim A' P' hnil' hcons' u : _ | RPl].
  Let QProp t u (Ptu : ListPropEq Γ _ RLiA t u) :=
    forall (Rt : [Γ ||-<l> t : _ | RLA]) (Ru : [Γ ||-<l> u : _ | RLA]) (RPl := RP t Rt),
      [Γ ||-<l> tListElim A P hnil hcons t ≅ tListElim A' P' hnil' hcons' u : _ | RPl].

  Lemma elimListRedEq_mut : 
    (forall t u (Rtu : ListRedTmEq Γ _ RLiA t u), QRed t u Rtu) ×
    (forall t u (Ptu : ListPropEq Γ _ RLiA t u), QProp t u Ptu).
  Proof.
    assert [Γ ||-<l> _ ≅ tList A' | RLA].
    1:{ econstructor.
      + eapply redtywf_refl; escape; gen_typing.
      + escape; now eapply convty_list.
      + intros; cbn; irrelevanceRefl; now unshelve eapply wkEq.
    }
    assert (RPP' : forall t u (Rt : [Γ ||-<l> t : _ | RLA]), [Γ ||-<l> u : _ | RLA] -> [Γ ||-<l> t ≅ u : _ | RLA] -> [Γ ||-<l> P[t..] ≅ P'[u..]| RP t Rt]).
    1:{
      intros.
      assert [|- Γ] by (escape ; gen_typing).
      eapply transEq.
      1: now unshelve eapply RPeq.
      irrelevance0; erewrite <- subst_wk_id_tail; [reflexivity|].
      unshelve eapply (PolyRedEq.posRed PolyPeq); tea; irrelevance.
      Unshelve. 3: now eapply RP. 2: eapply RP'; eapply LRTmRedConv; tea.
    }

    assert [Γ |- A] by now escape.
    assert [Γ ||-<l> A ≅ A | RA] by eapply LRTyEqRefl_.


    eapply ListRedEqInductionDep; subst QRed QProp; cbn.

    - intros.
      assert [Γ ||-<l> t ≅ u : _ | RLA] by now econstructor.
      assert (Ru' : [Γ ||-<l> u : _ | RLA']) by now eapply LRTmRedConv.
      pose proof (elimListRed RA RLiA0 PolyP Rtynil Rhnil Rtycons Rhcons t Rt) as [_ [Rtnf Rtnfeq]].
      pose proof (elimListRed RA' RLiA0' PolyP' Rtynil' Rhnil' Rtycons' Rhcons' u Ru') as [_ [Runf Runfeq]].
      assert [Γ ||-<l> P[t..] ≅ P'[u..] | RP _ Rt] by now eapply RPP'.
      eapply LREqTermHelper; tea.
      (* why does rewrite fails here ? *)
      set (v := ListRedTm.nf _); replace (ListRedTm.nf _) with (ListRedTm.nf Ru) by now eapply ListRedTm_det.
      pose proof (ListRedTmFwd RA _ Rt) as [].
      pose proof (ListRedTmFwd RA _ Ru) as [].
      eapply LRTmEqRedConv.  2: eauto.
      eapply LRTyEqSym; unshelve eapply RPeq; tea.
      Unshelve. tea.

    - intros.
      assert [Γ ||-<l> A ≅ P0 | RA] by irrelevance.
      assert [Γ ||-<l> A ≅ P'0 | RA] by irrelevance.
      assert [Γ ||-<l> tNil A ≅ tNil P0 : _ | RLA] by now eapply nilEqRed.
      assert [Γ ||-<l> tNil A ≅ tNil P'0 : _ | RLA] by now eapply nilEqRed.
      assert (Ru' : [Γ ||-<l> tNil P'0 : _ | RLA']) by now eapply LRTmRedConv.

      set (Pt := ListProp_nil_inv RA _ (ListRedTm_prop_whnf RA _ Rt whnf_tNil)).
      set (Pu' := ListProp_nil_inv RA' _ (ListRedTm_prop_whnf RA' _ Ru' whnf_tNil)).
      pose proof (elimListProp RA RLiA0 PolyP Rtynil Rhnil Rtycons Rhcons _ Pt Rt) as [_ []].
      pose proof (elimListProp RA' RLiA0' PolyP' Rtynil' Rhnil' Rtycons' Rhcons' _ Pu' Ru') as [_ []].
      eapply LREqTermHelper; tea.
      + eapply RPP'; tea.
        eapply transEqTerm; tea.
        eapply LRTmEqSym; tea.
      + cbn. eapply LRTmEqRedConv; tea.
        irrelevanceRefl; eapply RPeq; tea.
        Unshelve. now eapply nilRed.
    
    - intros.
      assert [Γ ||-<l> A ≅ P0 | RA] by irrelevance.
      assert [Γ ||-<l> A ≅ P'0 | RA] by irrelevance.
      assert (Ru' : [Γ ||-<l> tCons P'0 hd' tl' : _ | RLA']) by now eapply LRTmRedConv.

      pose proof (Pt0 := ListRedTm_prop_whnf RA _ Rt whnf_tCons).
      pose proof (ListProp_cons_inv0 RA _ Pt0) as [].
      set (Pt := ListProp_cons_inv RA _ Pt0).

      pose proof (Pu0' := ListRedTm_prop_whnf RA' _ Ru' whnf_tCons).
      pose proof (ListProp_cons_inv0 RA' _ Pu0') as [].
      set (Pu' := ListProp_cons_inv RA' _ Pu0').
      pose proof (elimListProp RA RLiA0 PolyP Rtynil Rhnil Rtycons Rhcons _ Pt Rt) as [_ []].
      pose proof (elimListProp RA' RLiA0' PolyP' Rtynil' Rhnil' Rtycons' Rhcons' _ Pu' Ru') as [_ []].
      eapply LREqTermHelper; tea.
      + eapply RPP'; tea.
        eapply consEqRed; cycle 3; tea.
        irrelevance.
      + cbn.
        pose proof (polyRedId PolyP) as [_].
        eapply LRTmEqRedConv.
        2: eapply elimConsHypAppEqRed; tea.
        * eapply RPeq; tea.
          eapply consEqRed; cycle 3; tea; now eapply LREqTermRefl_.
        * irrelevance.
        * now eapply elimListRed.
        * now eapply elimListRed.
        * eapply consRed; tea.
          1: now escape.
          now eapply LRTyEqRefl_.
        * eapply consEqRed; cycle 3; tea.
          2: irrelevance.
          1,2: eapply LRTmRedConv; [|tea]; now eapply LRTyEqSym.
          now escape.
        Unshelve. 
          2: irrelevance.
          2,3: tea.
          now eapply consRed.
    - intros. 
      pose proof (polyRedId PolyP) as [_].
      pose proof (polyRedId PolyP') as [_].
      pose proof (polyRedEqId _ PolyPeq) as [_].
      change [Γ ||-<l> l0 : _ | RLA] in Rt.
      change [Γ ||-<l> l' : _ | RLA] in Ru.
      assert [Γ ||-<l> l0 ≅ l' : _ | RLA] by (escape ; now eapply neuListTermEq).
      assert [Γ ||-<l> P[l0..] ≅ P'[l'..] | RP _ Rt] by now eapply RPP'.
      escape.
      eapply completeness.
      + now eapply ty_listElim.
      + eapply ty_conv; [| now symmetry].
        eapply ty_listElim; tea.
        now eapply ty_conv.
      + now eapply convneu_listElim.
  Qed.

  Lemma elimListRedEq : forall t u (Rtu : ListRedTmEq Γ _ RLiA t u), QRed t u Rtu.
  Proof. apply elimListRedEq_mut. Qed.

End ListElimRed.



Section ListElimValid.
  Context `{GenericTypingProperties}.

  Context {Γ l A P}
    (VΓ : [||-v Γ])
    (VA : [Γ ||-v<l> A | VΓ])
    (VLA := listValid VΓ VA)
    (VΓA := validSnoc VΓ VLA)
    (VP : [Γ ,, tList A ||-v<l> P | VΓA]).


  Lemma Vtynil : [Γ ||-v<l> P[(tNil A)..] | VΓ].
  Proof.
    eapply substS; tea.
    eapply nilValid.
    Unshelve. tea.
  Defined.

  Definition wk2 Γ A B := wk_step B (@wk1 Γ A).

  Lemma wk2_ren_on Δ X Y t : t⟨wk2 Δ X Y⟩ = t⟨↑⟩⟨↑⟩.
  Proof. unfold wk2; now bsimpl. Qed.

  Lemma Vtycons : [Γ ||-v<l> elimConsHypTy A P | VΓ].
  Proof.
    unfold elimConsHypTy.
    unshelve eapply PiValid; tea.
    unshelve eapply PiValid; tea.
    1: eapply listValid; erewrite <- wk1_ren_on; now eapply wk1ValidTy.
    assert (VΓALA : [||-v (Γ ,, A),, (tList A)⟨@wk1 Γ A⟩]).
    1: unshelve eapply validSnoc; [|unshelve eapply validSnoc; tea|now eapply wkValid].
    pose (ρ := wk_up (tList A) (@wk1 Γ A)).
    eapply simpleArrValid.
    + eapply irrelevanceValidity'.
      1: exact (wkValid ρ VΓA VΓALA VP).
      1: unfold ρ; now bsimpl.
      now bsimpl.
    + set (t := tCons _ _ _).
      set (τ := wk2 Γ A (tList A⟨@wk1 Γ A⟩)).
      pose (VULA := wkValid τ VΓ VΓALA VLA).
      assert [_ ||-v<l> t : _ | VΓALA | VULA].
      1:{
        eapply irrelevanceTm'.
        1: now rewrite <- wk_list, wk2_ren_on.
        unfold t. eapply consValid.
        1: eapply var1Valid.
        eapply varnValid; rewrite wk1_ren_on; now constructor.
        Unshelve.
        2: tea.
        2,3: erewrite <- wk2_ren_on, ?wk_list; eapply wkValid; tea.
      }
      enough (h : [_ ||-v<l> P⟨ρ⟩[t]⇑ | VΓALA]).
      1:{
        eapply irrelevanceValidity'; [exact h|..].
        1: now unfold ρ; bsimpl.
        now rewrite <- wk_list, wk1_ren_on.
      } 
      eapply irrelevanceValidity.
      eapply substLiftS.
      2: eapply irrelevanceTm'; tea; unfold τ, wk2; now bsimpl.
      now eapply wkValid.
      Unshelve.
      1: now eapply validSnoc.
      now eapply wkValid.
  Qed.

  Context {hnil hcons}
    (Vhnil : [Γ ||-v<l> hnil : _ | VΓ | Vtynil])
    (Vhcons : [Γ ||-v<l> hcons : _ | VΓ | Vtycons]).


  Lemma elimConsHypTySubst σ : (elimConsHypTy A P)[σ] = elimConsHypTy A[σ] P[up_term_term σ].
  Proof.
    unfold elimConsHypTy. do 2 (rewrite subst_prod; f_equal).
    1: now asimpl.
    rewrite subst_arr; f_equal.
    1: now asimpl.
    do 2 (asimpl; cbn); now rewrite rinstInst'_term_pointwise.
  Qed.

  Lemma elimListValid t (Vt : [Γ ||-v<l> t : _ | VΓ | VLA]) (VPt := substS VP Vt) :
    [Γ ||-v<l> tListElim A P hnil hcons t : _ | VΓ | VPt].
  Proof.
    pose Vtynil.
    pose Vtycons.
    econstructor; intros.
    - instValid Vσ.
      cbn; irrelevance0.
      2: unshelve eapply elimListRed; tea; try irrelevance.
      1: now asimpl.
      1: now eapply invLRList.
      4: apply elimConsHypTySubst.
      3: now rewrite <- elimConsHypTySubst.
      2: intros; change (tNil ?A[?σ]) with (tNil A)[σ]; now rewrite <- singleSubstComm'.
      change (tList ?A[?σ]) with (tList A)[σ]; now eapply substPolyRed.
    - instAllValid Vσ Vσ' Vσσ'.
      cbn; irrelevance0.
      1: now rewrite singleSubstComm'.
      unshelve eapply elimListRedEq; tea; try irrelevance.
      1,8: now eapply invLRList. 
      9,10,11: apply elimConsHypTySubst.
      1,7: change (tList ?A[?σ]) with (tList A)[σ]; now eapply substPolyRed.
      2,3: intros; change (tNil ?A[?σ]) with (tNil A)[σ]; now rewrite <- singleSubstComm'.
      2,3: now rewrite <- elimConsHypTySubst.
      1: change [Δ ||-<l> t[σ] ≅ t[σ'] : _ | LRList' (normList0 (invLRList RVLA))]; irrelevance.
      change (tList ?A[?σ]) with (tList A)[σ]; now eapply substPolyRedEq.
  Qed.

  
End ListElimValid.
