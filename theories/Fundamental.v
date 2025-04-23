(** * LogRel.Fundamental: declarative typing implies the logical relation for any generic instance. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening
  DeclarativeTyping DeclarativeInstance GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Monotonicity Split Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape Monotonicity Split.
From LogRel.Substitution.Introductions Require Import Application Universe Pi Lambda Var Nat Bool Empty SimpleArr Sigma Id.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Primitive Projection Parameters.

(** ** Definitions *)

(** These records bundle together all the validity data: they do not only say that the
relevant relation holds, but also that all its boundaries hold as well. For instance,
FundTm tells that not only the term is valid at a given type, but also that this type is
itself valid, and that the context is as well. This is needed because the definition of
later validity relations depends on earlier ones, and makes using the fundamental lemma
easier, because we can simply invoke it to get all the validity properties we need. *)

Definition FundCon `{GenericTypingProperties}
  (wl : wfLCon) (Γ : context) : Type := [||-v Γ ]< wl >.

Module FundTy.
  Record FundTy `{GenericTypingProperties} {wl : wfLCon} {Γ : context} {A : term}
  : Type := {
    VΓ : [||-v Γ ]< wl >;
    VA : [ Γ ||-v< one > A | VΓ ]< wl >
  }.
  Arguments FundTy {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTy.

Export FundTy(FundTy,Build_FundTy).

Module FundTyEq.
  Record FundTyEq `{GenericTypingProperties}
    {wl : wfLCon} {Γ : context} {A B : term}
  : Type := {
    VΓ : [||-v Γ ]< wl >;
    VA : [ Γ ||-v< one > A | VΓ ]< wl >;
    VB : [ Γ ||-v< one > B | VΓ ]< wl >;
    VAB : [ Γ ||-v< one > A ≅ B | VΓ | VA ]< wl >
  }.
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTyEq.

Export FundTyEq(FundTyEq,Build_FundTyEq).

Module FundTm.
  Record FundTm `{GenericTypingProperties}
    {wl : wfLCon} {Γ : context} {A t : term}
  : Type := {
    VΓ : [||-v Γ ]< wl >;
    VA : [ Γ ||-v< one > A | VΓ ]< wl >;
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ]< wl >;
  }.
  Arguments FundTm {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTm.

Export FundTm(FundTm,Build_FundTm).

Module FundTmEq.
  Record FundTmEq `{GenericTypingProperties}
    {wl : wfLCon} {Γ : context} {A t u : term}
  : Type := {
    VΓ : [||-v Γ ]< wl >;
    VA : [ Γ ||-v< one > A | VΓ ]< wl >;
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ]< wl >;
    Vu : [ Γ ||-v< one > u : A | VΓ | VA ]< wl >;
    Vtu : [ Γ ||-v< one > t ≅ u : A | VΓ | VA ]< wl >;
  }.
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).

Module FundSubst.
  Record FundSubst `{GenericTypingProperties}
    {wl wl' : wfLCon} {Γ Δ : context} {σ : nat -> term} {f: wl' ≤ε wl}  {wfΓ : [|- Γ]< wl' >}
  : Type := {
    VΔ : [||-v Δ ]< wl > ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ | f]< wl > ;
  }.
  Arguments FundSubst {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundSubst.

Export FundSubst(FundSubst,Build_FundSubst).

Module FundSubstConv.
  Record FundSubstConv `{GenericTypingProperties}
    {wl wl' : wfLCon} {Γ Δ : context}  {σ σ' : nat -> term} {f: wl' ≤ε wl} {wfΓ : [|- Γ]< wl' >}
  : Type := {
    VΔ : [||-v Δ ]< wl > ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ | f]< wl > ;
    Vσ' : [VΔ | Γ ||-v σ' : Δ | wfΓ | f]< wl > ;
    Veq : [VΔ | Γ ||-v σ ≅ σ' : Δ | wfΓ | Vσ | f]< wl > ;
  }.
  Arguments FundSubstConv {_ _ _ _ _ _ _ _ _ _ _ _ _ _}.
End FundSubstConv.

Export FundSubstConv(FundSubstConv,Build_FundSubstConv).

(** ** The main proof *)

(** Each cases of the fundamental lemma is proven separately, and the final proof simply
brings them all together. *)

Section Fundamental.
  (** We need to have in scope both the declarative instance and a generic one, which we use
  for the logical relation. *)
  Context `{GenericTypingProperties}.
  Import DeclarativeTypingData.

  Lemma FundConNil {wl} : FundCon wl ε.
  Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + intros; exact unit.
    + intros; exact unit.
  - cbn.
    constructor.
    all: now auto.
  Qed.

  Lemma FundConCons (wl : wfLCon) (Γ : context) (A : term)
  (fΓ : FundCon wl Γ) (fA : FundTy wl Γ A) : FundCon wl (Γ,, A).
  Proof.
    destruct fA as [ VΓ VA ].
    eapply validSnoc'. exact VA.
  Qed.

  Lemma FundTyU (wl : wfLCon) (Γ : context) (fΓ : FundCon wl Γ) : FundTy wl Γ U.
  Proof.
    unshelve econstructor.
    - assumption.
    - unshelve econstructor.
      + intros * _.
        econstructor ; intros wl'' Ho.
        pose (f' := over_tree_le Ho).
        apply LRU_.  
        econstructor; tea  ; [constructor| now eapply wfc_Ltrans | ]. 
        cbn; eapply redtywf_refl.
        eapply wft_Ltrans ; [eassumption | gen_typing].
      + intros * _ _. simpl.
        econstructor ; intros wl'' Ho Ho'.
        pose (f' := over_tree_le Ho).
        constructor.
        cbn; eapply redtywf_refl.
        eapply wft_Ltrans ; [eassumption | gen_typing].
        Unshelve. all: now constructor.
  Qed.

  Lemma FundTyPi (wl : wfLCon) (Γ : context) (F G : term)
    (fF : FundTy wl Γ F)
    (fG : FundTy wl (Γ,, F) G)
    : FundTy wl Γ (tProd F G).
  Proof.
    destruct fF as [ VΓ VF ]. destruct fG as [ VΓF VG ].
    econstructor.
    unshelve eapply (PiValid VΓ).
    - assumption.
    - now eapply irrelevanceTy.
  Qed.

  Lemma FundTyUniv (wl : wfLCon) (Γ : context) (A : term)
    (fA : FundTm wl Γ U A)
    : FundTy wl Γ A.
  Proof.
    destruct fA as [ VΓ VU [ RA RAext ] ]. econstructor.
    unshelve econstructor.
    - intros * vσ.
      eapply WUnivEq. exact (RA _ _ _ _ wfΔ vσ).
    - intros * vσ' vσσ'.
      eapply WUnivEqEq. exact (RAext _ _ _ _ _ wfΔ vσ vσ' vσσ').
  Qed.

  Lemma FundTmVar : forall (wl : wfLCon) (Γ : context) (n : nat) decl,
      FundCon wl Γ ->
      in_ctx Γ n decl -> FundTm wl Γ decl (tRel n).
  Proof.
    intros wl Γ n d FΓ hin.
    induction hin ; destruct (invValidity FΓ) as [l [VΓ [VA [Hsub [Hext ]]]]] ; subst.
    - renToWk; rewrite <- (wk1_ren_on Γ d d).
      eexists _ _; unshelve eapply var0Valid; tea.
      now eapply embValidTyOne.
    - renToWk; rewrite <- (wk1_ren_on Γ d' d).
      destruct (IHhin VΓ); cbn in *.
      econstructor. set (ρ := wk1 _).
      replace (tRel _) with (tRel n)⟨ρ⟩ by (unfold ρ; now bsimpl).
      unshelve eapply wk1ValidTm; cycle 1; tea; now eapply irrelevanceTy.
  Qed.

  Lemma FundTmProd : forall (wl : wfLCon) (Γ : context) (A B : term),
    FundTm wl Γ U A ->
    FundTm wl (Γ,, A) U B -> FundTm wl Γ U (tProd A B).
  Proof.
    intros * [] []; econstructor.
    eapply PiValidU; irrValid.
    Unshelve. 
    3: eapply UValid. 
    2: eapply univValid. 
    all:tea.
  Qed.

  Lemma FundTmLambda : forall (wl : wfLCon) (Γ : context) (A B t : term),
    FundTy wl Γ A ->
    FundTm wl (Γ,, A) B t -> FundTm wl Γ (tProd A B) (tLambda A t).
  Proof.
    intros * [] []; econstructor.
    eapply lamValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmApp : forall (wl : wfLCon) (Γ : context) (f a A B : term),
    FundTm wl Γ (tProd A B) f ->
    FundTm wl Γ A a -> FundTm wl Γ B[a..] (tApp f a).
  Proof.
    intros * [] []; econstructor.
    now eapply appValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmConv : forall (wl : wfLCon) (Γ : context) (t A B : term),
      FundTm wl Γ A t ->
      FundTyEq wl Γ A B -> FundTm wl Γ B t.
  Proof.
    intros * [] []; econstructor. 
    eapply conv; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTyEqPiCong : forall (wl : wfLCon) (Γ : context) (A B C D : term),
    FundTy wl Γ A ->
    FundTyEq wl Γ A B ->
    FundTyEq wl (Γ,, A) C D ->
    FundTyEq wl Γ (tProd A C) (tProd B D).
  Proof.
    intros * [] [] []; econstructor.
    - eapply PiValid. eapply irrelevanceLift; tea; irrValid.
    - eapply PiCong. 1: eapply irrelevanceLift; tea.
      all: irrValid.
    Unshelve. all: tea; irrValid.
  Qed.

  Lemma FundTyEqRefl : forall (wl : wfLCon) (Γ : context) (A : term),
      FundTy wl Γ A -> FundTyEq wl Γ A A.
  Proof.
    intros * []; unshelve econstructor; tea; now eapply reflValidTy.
  Qed.

  Lemma FundTyEqSym : forall (wl : wfLCon) (Γ : context) (A B : term),
      FundTyEq wl Γ A B -> FundTyEq wl Γ B A.
  Proof.
    intros * [];  unshelve econstructor; tea.
    now eapply symValidTyEq.
  Qed.

  Lemma FundTyEqTrans : forall (wl : wfLCon) (Γ : context) (A B C : term),
      FundTyEq wl Γ A B ->
      FundTyEq wl Γ B C ->
      FundTyEq wl Γ A C.
  Proof.
    intros *  [] []; unshelve econstructor; tea. 1:irrValid.
    eapply transValidTyEq; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTyEqUniv : forall (wl : wfLCon) (Γ : context) (A B : term),
      FundTmEq wl Γ U A B -> FundTyEq wl Γ A B.
  Proof.
    intros * []; unshelve econstructor; tea.
    1,2: now eapply univValid.
    now eapply univEqValid.
  Qed.

  Lemma FundTmEqBRed : forall (wl : wfLCon) (Γ : context) (a t A B : term),
    FundTy wl Γ A ->
    FundTm wl (Γ,, A) B t ->
    FundTm wl Γ A a -> FundTmEq wl Γ B[a..] (tApp (tLambda A t) a) t[a..].
  Proof.
    intros *  [] [] []; econstructor.
    - eapply appValid. eapply lamValid. irrValid.
    - unshelve epose (substSTm _ _).
      8-12: irrValid.
      cbn in *.
      irrValid.
    - unshelve epose (betaValid VA _ _ _). 2,5-7:irrValid.
      Unshelve. all: tea; try irrValid.
  Qed.


  Lemma FundTmEqPiCong : forall (wl : wfLCon) (Γ : context) (A B C D : term),
    FundTm wl Γ U A ->
    FundTmEq wl Γ U A B ->
    FundTmEq wl (Γ,, A) U C D ->
    FundTmEq wl Γ U (tProd A C) (tProd B D).
  Proof.
    intros * [] [] [].
    assert (VA' : [Γ ||-v<one> A | VΓ]< wl >) by now eapply univValid.
    assert [Γ ||-v<one> A ≅ B | VΓ | VA']< wl > by (eapply univEqValid; irrValid).
    opector; tea.
    - now eapply UValid.
    - edestruct FundTmProd. 3: irrValid.
      2: eauto.
      all: unshelve econstructor; irrValid.
    - edestruct FundTmProd. 3: irrValid.
      1: unshelve econstructor; irrValid.
      unshelve econstructor.
      + eapply validSnoc'; now eapply univValid.
      + eapply UValid.
      + eapply irrelevanceTmLift; irrValid.
    - unshelve epose (PiCongTm _ _ _ _ _ _ _ _ _ _ _).
      17: irrValid.
      3: tea.
      3,4,9: irrValid.
      all: try irrValid.
      + eapply univValid; irrValid.
      + eapply irrelevanceLift; irrValid.
      + eapply irrelevanceTmLift; irrValid.
      Unshelve.
      all: try irrValid.
  Qed.

  Lemma FundTmEqAppCong : forall (wl : wfLCon) (Γ : context) (a b f g A B : term),
      FundTmEq wl Γ (tProd A B) f g ->
      FundTmEq wl Γ A a b ->
    FundTmEq wl Γ B[a..] (tApp f a) (tApp g b).
  Proof.
    intros *  [] []; econstructor.
    - eapply appValid; irrValid.
    - eapply conv. 2: eapply appValid; irrValid.
      eapply substSΠeq; try irrValid.
      1: eapply reflValidTy.
      now eapply symValidTmEq.
    - eapply appcongValid; irrValid.
    Unshelve. all: irrValid.
  Qed.
  
  Lemma FundTmEqLambdaCong : forall (wl : wfLCon) (Γ : context) (t u A A' A'' B : term),
    FundTy wl Γ A ->
    FundTyEq wl Γ A A' ->
    FundTyEq wl Γ A A'' ->
    FundTmEq wl (Γ,, A) B t u ->
    FundTmEq wl Γ (tProd A B) (tLambda A' t) (tLambda A'' u).
  Proof.
    intros * [VΓ] [? ? VA'] [? ? VA''] [].
    assert (VΠAB : [Γ ||-v< one > tProd A B | VΓ]< wl >).
    { unshelve eapply PiValid; irrValid. }
    assert (VB' : [Γ,, A' ||-v< one > B | validSnoc' _ VA']< wl >).
    { eapply irrelevanceLift; [tea|]; irrValid. }
    assert (VB'' : [Γ,, A'' ||-v< one > B | validSnoc' _ VA'']< wl >).
    { eapply irrelevanceLift; [tea|]; irrValid. }
    assert (Vλt : [Γ ||-v< one > tLambda A' t : tProd A B | VΓ | VΠAB ]< wl >).
    { eapply conv; [|eapply lamValid].
      + eapply symValidTyEq, PiCong; tea; try irrValid.
        eapply reflValidTy.
      + eapply irrelevanceTmLift; irrValid.
    }
    assert (Vλu : [Γ ||-v< one > tLambda A'' u : tProd A B | VΓ | VΠAB ]< wl >).
    { eapply conv; [|eapply lamValid].
      + eapply symValidTyEq, PiCong; tea; try irrValid.
        eapply reflValidTy.
      + eapply irrelevanceTmLift; irrValid.
    }
    Unshelve. all: try irrValid.
    assert [Γ,, A ||-v< one > A⟨@wk1 Γ A⟩ | validSnoc' VΓ VA]< wl >.
    { apply wk1ValidTy; irrValid. }
    assert (VΓAA' : [Γ,, A ||-v< one > A'⟨@wk1 Γ A⟩ | validSnoc' VΓ VA]< wl >).
    { apply wk1ValidTy; irrValid. }
    assert (VΓAA'' : [Γ,, A ||-v< one > A''⟨@wk1 Γ A⟩ | validSnoc' VΓ VA]< wl >).
    { apply wk1ValidTy; irrValid. }
    assert (VAdequate (ta := ta) wl (Γ,, A) VR).
    { now eapply validSnoc'. }
    assert (VAdequate (ta := ta) wl (Γ,, A,, A'⟨@wk1 Γ A⟩) VR).
    { unshelve eapply validSnoc'; tea; try irrValid. }
    assert (VAdequate (ta := ta) wl (Γ,, A,, A''⟨@wk1 Γ A⟩) VR).
    { unshelve eapply validSnoc'; tea; try irrValid. }
    assert (eq0 : forall t, t⟨upRen_term_term ↑⟩[(tRel 0)..] = t).
    { clear; intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
    econstructor; tea.
    eapply irrelevanceTmEq, etaeqValid; try irrValid.
    eapply transValidTmEq; [|eapply transValidTmEq]; [|eapply irrelevanceTmEq; tea|].
    + eapply irrelevanceTmEq'; [eapply eq0|].
      eapply transValidTmEq; [eapply betaValid|]; refold.
      - eapply irrelevanceTm'.
        2: eapply (wkValidTm  (A := B)) with (ρ := wk_up A' (@wk1 Γ A)).
        * now bsimpl.
        * eapply irrelevanceTmLift; irrValid.
      - eapply irrelevanceTmEq'; [symmetry; eapply eq0|].
        match goal with |- [_ ||-v< _ > ?t ≅ ?u : _ | _ | _ ]< wl > => assert (Hrw : t = u) end.
        { bsimpl; apply idSubst_term; intros []; reflexivity. }
        set (t' := t) at 2; rewrite Hrw.
        apply reflValidTm; tea.
    + apply symValidTmEq; eapply irrelevanceTmEq'; [eapply eq0|].
      eapply transValidTmEq; [eapply betaValid|]; refold.
      - eapply irrelevanceTm'.
        2: eapply (wkValidTm  (A := B)) with (ρ := wk_up A'' (@wk1 Γ A)).
        * now bsimpl.
        * eapply irrelevanceTmLift; irrValid.
      - eapply irrelevanceTmEq'; [symmetry; eapply eq0|].
        match goal with |- [_ ||-v< _ > ?t ≅ ?u : _ | _ | _ ]< wl > => assert (Hrw : t = u) end.
        { bsimpl; apply idSubst_term; intros []; reflexivity. }
        set (u' := u) at 2; rewrite Hrw.
        apply reflValidTm; tea.
    Unshelve.
    all: refold; try irrValid.
    * unshelve eapply irrelevanceTy; tea.
      rewrite <- (wk_up_wk1_ren_on Γ A' A).
      eapply wkValidTy, irrelevanceLift; irrValid.
    * eapply conv; [now eapply irrelevanceTyEq, wk1ValidTyEq|].
      eapply irrelevanceTm'; [symmetry; eapply wk1_ren_on|].
      eapply var0Valid'.
    * eapply irrelevanceTy.
      rewrite <- (wk_up_wk1_ren_on Γ A'' A).
      eapply wkValidTy, irrelevanceLift; irrValid.
    * eapply conv; [now eapply irrelevanceTyEq, wk1ValidTyEq|].
      eapply irrelevanceTm'; [symmetry; eapply wk1_ren_on|].
      eapply var0Valid'.
  Unshelve.
  all: try irrValid.
  2,4: rewrite <- (wk1_ren_on Γ A); irrValid.
  Qed.


  Lemma FundTmEqFunEta : forall (wl : wfLCon) (Γ : context) (f A B : term),
    FundTm wl Γ (tProd A B) f -> FundTmEq wl Γ (tProd A B) (tLambda A (tApp f⟨↑⟩ (tRel 0))) f.
  Proof.
  intros * [VΓ VΠ Vf].
  assert (eq0 : forall t, t⟨upRen_term_term ↑⟩[(tRel 0)..] = t).
  { clear; intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert (VA : [Γ ||-v< one > A | VΓ]< wl >).
  { now eapply PiValidDom. }
  assert (VΓA := validSnoc' VΓ VA).
  assert (VΓAA : [Γ,, A ||-v< one > A⟨@wk1 Γ A⟩ | VΓA]< wl >).
  { now eapply irrelevanceTy, wk1ValidTy. }
  assert (VΓAA0 : VAdequate (ta := ta) wl (Γ,, A,, A⟨@wk1 Γ A⟩) VR).
  { now eapply validSnoc'. }
  assert (VΓAA' : [Γ,, A ||-v< one > A⟨↑⟩ | VΓA]< wl >).
  { now rewrite wk1_ren_on in VΓAA. }
  assert [Γ,, A ||-v< one > B | VΓA]< wl >.
  { eapply irrelevanceTy, PiValidCod. }
  assert ([Γ,, A ||-v< one > tProd A⟨@wk1 Γ A⟩ B⟨upRen_term_term ↑⟩ | VΓA]< wl >).
  { rewrite <- (wk_up_wk1_ren_on Γ A A).
    now eapply irrelevanceTy, (wk1ValidTy (A := tProd A B)). }
  assert ([Γ,, A ||-v< one > tRel 0 : A⟨wk1 A⟩ | VΓA | VΓAA]< wl >).
  { eapply irrelevanceTm'; [rewrite wk1_ren_on; reflexivity|].
    unshelve apply var0Valid'. }
  assert ([(Γ,, A),, A⟨wk1 A⟩ ||-v< one > tProd A⟨↑⟩⟨↑⟩ B⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩ | VΓAA0]< wl >).
  { assert (eq1 : (tProd A B)⟨@wk1 Γ A⟩⟨@wk1 (Γ,, A) A⟨@wk1 Γ A⟩⟩ = tProd (A⟨↑⟩⟨↑⟩) (B⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩)).
    { rewrite wk1_ren_on, wk1_ren_on; reflexivity. }
    eapply irrelevanceTy'; [|eapply eq1|reflexivity].
    now eapply wkValidTy, wkValidTy. }
  assert ([Γ ||-v< one > tLambda A (tApp f⟨↑⟩ (tRel 0)) : tProd A B | VΓ | VΠ]< wl >).
  { eapply irrelevanceTm, lamValid.
    eapply irrelevanceTm'; [apply eq0|eapply (appValid (F := A⟨@wk1 Γ A⟩))].
    rewrite <- (wk1_ren_on Γ A).
    eapply irrelevanceTm'; [|now eapply wkValidTm].
    rewrite <- (wk_up_wk1_ren_on Γ A A).
    reflexivity. }
  Unshelve. all: try irrValid.
  econstructor; tea.
  eapply irrelevanceTmEq, etaeqValid; try irrValid.
  eapply transValidTmEq; refold.
  + eapply irrelevanceTmEq'; [eapply eq0|].
    eapply betaValid; refold.
    eapply irrelevanceTm'; [apply eq0|].
    eapply appValid.
    rewrite <- shift_upRen.
    assert (eq1 : (tProd A B)⟨@wk1 Γ A⟩⟨@wk1 (Γ,, A) A⟨@wk1 Γ A⟩⟩ = tProd (A⟨↑⟩⟨↑⟩) (B⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩)).
    { rewrite wk1_ren_on, wk1_ren_on; reflexivity. }
    eapply irrelevanceTm'; [eapply eq1|].
    rewrite <- (wk1_ren_on (Γ,, A)  A⟨@wk1 Γ A⟩).
    now eapply wkValidTm, wkValidTm.
  + refold.
    match goal with |- [_ ||-v< _ > ?t ≅ ?u : _ | _ | _ ]< wl > => assert (Hrw : t = u) end.
    { rewrite <- eq0; now bsimpl. }
    rewrite Hrw.
    apply reflValidTm; tea.
    eapply irrelevanceTm'; [apply eq0|].
    eapply (appValid (F := A⟨@wk1 Γ A⟩)).
    eapply irrelevanceTm'; [|now eapply wk1ValidTm].
    now rewrite <- (wk_up_wk1_ren_on Γ A A).
  Unshelve.
  all: refold; try irrValid.
  { unshelve eapply irrelevanceTy; [tea|].
    rewrite <- (wk_up_wk1_ren_on Γ A A).
    now eapply wkValidTy. }
  { eapply (irrelevanceTy' (A := A⟨↑⟩⟨@wk1 (Γ,, A) A⟨@wk1 Γ A⟩⟩)); [|now rewrite wk1_ren_on|reflexivity].
    now eapply wkValidTy. }
  { eapply (irrelevanceTm' (A := A⟨@wk1 Γ A⟩⟨↑⟩)); [now rewrite wk1_ren_on|].
    apply var0Valid'. }
  Unshelve.
  all: try irrValid.
  { shelve. }
  { rewrite <- (wk1_ren_on (Γ,, A)  A⟨@wk1 Γ A⟩).
    now eapply wkValidTy. }
  Qed.


  Lemma FundTmEqFunExt : forall (wl : wfLCon) (Γ : context) (f g A B : term),
      FundTy wl Γ A ->
      FundTm wl Γ (tProd A B) f ->
      FundTm wl Γ (tProd A B) g ->
     FundTmEq wl (Γ,, A) B (tApp (f⟨↑⟩) (tRel 0)) (tApp (g⟨↑⟩) (tRel 0)) ->
     FundTmEq wl Γ (tProd A B) f g.
  Proof.
    intros *  [] [VΓ0 VA0] [] [].
    assert [Γ ||-v< one > g : tProd A B | VΓ0 | VA0]< wl >.
    1:{
      eapply conv. 
      2: irrValid.
      eapply symValidTyEq. eapply PiCong.
      eapply irrelevanceLift. 
      1,3,4: eapply reflValidTy.
      irrValid.
    }
    econstructor. 
    3: eapply etaeqValid. 
    5: do 2 rewrite wk1_ren_on.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqRefl : forall (wl : wfLCon) (Γ : context) (t A : term),
      FundTm wl Γ A t ->
      FundTmEq wl Γ A t t.
  Proof.
    intros * []; econstructor; tea; now eapply reflValidTm.
  Qed.

  Lemma FundTmEqSym : forall (wl : wfLCon) (Γ : context) (t t' A : term),
      FundTmEq wl Γ A t t' ->
      FundTmEq wl Γ A t' t.
  Proof.
    intros * []; econstructor; tea; now eapply symValidTmEq.
  Qed.

  Lemma FundTmEqTrans : forall (wl : wfLCon) (Γ : context) (t t' t'' A : term),
      FundTmEq wl Γ A t t' ->
      FundTmEq wl Γ A t' t'' ->
    FundTmEq wl Γ A t t''.
  Proof.
    intros *  [] []; econstructor; tea.
    1: irrValid.
    eapply transValidTmEq; irrValid.
  Qed.

  Lemma FundTmEqConv : forall (wl : wfLCon) (Γ : context) (t t' A B : term),
      FundTmEq wl Γ A t t' ->
      FundTyEq wl Γ A B ->
    FundTmEq wl Γ B t t'.
  Proof.
    intros *  [] []; econstructor.
    1,2: eapply conv; irrValid.
    eapply convEq; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyNat : forall (wl : wfLCon) (Γ : context),
      FundCon wl Γ -> FundTy wl Γ tNat.
  Proof.
    intros ???; unshelve econstructor; tea;  eapply natValid.
  Qed.

  Lemma FundTmNat : forall (wl : wfLCon) (Γ : context),
      FundCon wl Γ -> FundTm wl Γ U tNat.
  Proof.
    intros ???; unshelve econstructor; tea.
    2: eapply natTermValid.
  Qed.

  Lemma FundTmZero : forall (wl : wfLCon) (Γ : context), FundCon wl Γ -> FundTm wl Γ tNat tZero.
  Proof.
    intros; unshelve econstructor; tea. 
    2:eapply zeroValid.
  Qed.

  Lemma FundTmSucc : forall (wl : wfLCon) (Γ : context) (n : term),
      FundTm wl Γ tNat n -> FundTm wl Γ tNat (tSucc n).
  Proof.
    intros * []; unshelve econstructor; tea.
    eapply irrelevanceTm; eapply succValid; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTmNatElim : forall (wl : wfLCon) (Γ : context) (P hz hs n : term),
    FundTy wl (Γ,, tNat) P ->
    FundTm wl Γ P[tZero..] hz ->
    FundTm wl Γ (elimSuccHypTy P) hs ->
    FundTm wl Γ tNat n -> FundTm wl Γ P[n..] (tNatElim P hz hs n).
  Proof.
    intros *  [] [] [] []; unshelve econstructor; tea.
    2: eapply natElimValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyBool : forall (wl : wfLCon) (Γ : context),
      FundCon wl Γ -> FundTy wl Γ tBool.
  Proof.
    intros ???; unshelve econstructor; tea;  eapply boolValid.
  Qed.

  Lemma FundTmBool : forall (wl : wfLCon) (Γ : context),
      FundCon wl Γ -> FundTm wl Γ U tBool.
  Proof.
    intros ???; unshelve econstructor; tea.
    2: eapply boolTermValid.
  Qed.

  Lemma FundTmTrue : forall (wl : wfLCon) (Γ : context), FundCon wl Γ -> FundTm wl Γ tBool tTrue.
  Proof.
    intros; unshelve econstructor; tea. 
    2:eapply trueValid.
  Qed.

  Lemma FundTmFalse : forall (wl : wfLCon) (Γ : context), FundCon wl Γ -> FundTm wl Γ tBool tFalse.
  Proof.
    intros; unshelve econstructor; tea. 
    2:eapply falseValid.
  Qed.

  Lemma FundTmAlpha : forall (wl : wfLCon) (Γ : context) (n : term),
      FundTm wl Γ tNat n -> FundTm wl Γ tNat (tAlpha n).
  Proof.
    intros * []; unshelve econstructor; tea.
    eapply irrelevanceTm; eapply alphaValid; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTmBoolElim : forall (wl : wfLCon) (Γ : context) (P ht hf n : term),
    FundTy wl (Γ,, tBool) P ->
    FundTm wl Γ P[tTrue..] ht ->
    FundTm wl Γ P[tFalse..] hf ->
    FundTm wl Γ tBool n ->
    FundTm wl Γ P[n..] (tBoolElim P ht hf n).
  Proof.
    intros *  [] [] [] []; unshelve econstructor; tea.
    2: eapply boolElimValid; irrValid.
    Unshelve. all: irrValid.
  Qed.
  
  Lemma FundTyEmpty : forall (wl : wfLCon) (Γ : context), FundCon wl Γ -> FundTy wl Γ tEmpty.
  Proof.
    intros ???; unshelve econstructor; tea;  eapply emptyValid.
  Qed.

  Lemma FundTmEmpty : forall (wl : wfLCon) (Γ : context), [ |-[ de ] Γ]< wl > -> FundCon wl Γ -> FundTm wl Γ U tEmpty.
  Proof.
    intros ???; unshelve econstructor; tea.
    2: eapply emptyTermValid.
  Qed.

  Lemma FundTmEmptyElim : forall (wl : wfLCon) (Γ : context) (P n : term),
    FundTy wl (Γ,, tEmpty) P ->
    FundTm wl Γ tEmpty n -> FundTm wl Γ P[n..] (tEmptyElim P n).
  Proof.
    intros *  [] []; unshelve econstructor; tea.
    2: eapply emptyElimValid; irrValid.
    Unshelve. 1,2: irrValid. 
  Qed.

  Lemma FundTmEqSuccCong : forall (wl : wfLCon) (Γ : context) (n n' : term),
      FundTmEq wl Γ tNat n n' -> FundTmEq wl Γ tNat (tSucc n) (tSucc n').
  Proof.
    intros * []; unshelve econstructor; tea.
    1,2: eapply irrelevanceTm; eapply succValid; irrValid.
    eapply irrelevanceTmEq; eapply succcongValid; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTmEqNatElimCong : forall (wl : wfLCon) (Γ : context)
      (P P' hz hz' hs hs' n n' : term),
    FundTyEq wl (Γ,, tNat) P P' ->
    FundTmEq wl Γ P[tZero..] hz hz' ->
    FundTmEq wl Γ (elimSuccHypTy P) hs hs' ->
    FundTmEq wl Γ tNat n n' ->
    FundTmEq wl Γ P[n..] (tNatElim P hz hs n) (tNatElim P' hz' hs' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0] [] [].
    pose (VN := natValid (l:=one) VΓ0).
    assert (VP' : [ _ ||-v<one> P' | validSnoc' VΓ0 VN]< wl >) by irrValid. 
    assert [Γ ||-v< one > hz' : P'[tZero..] | VΓ0 | substS VP' (zeroValid VΓ0)]< wl >. 1:{
      eapply conv. 2: irrValid.
      eapply substSEq. 2,3: irrValid.
      1: eapply reflValidTy.
      2: eapply reflValidTm.
      all: eapply zeroValid.
    }
    assert [Γ ||-v< one > hs' : elimSuccHypTy P' | VΓ0 | elimSuccHypTyValid VΓ0 VP']< wl >. 1:{
      eapply conv. 2: irrValid.
      eapply elimSuccHypTyCongValid; irrValid.
    } 
    unshelve econstructor; tea.
    2: eapply natElimValid; irrValid.
    + eapply conv.
      2: eapply irrelevanceTm; now eapply natElimValid.
      eapply symValidTyEq. 
      eapply substSEq; tea. 
      2,3: irrValid.
      eapply reflValidTy.
    + eapply natElimCongValid; tea; try irrValid.
    Unshelve. all: try irrValid.
    1: eapply zeroValid.
    1: unshelve eapply substS; try irrValid.
  Qed.

  Lemma FundTmEqNatElimZero : forall (wl : wfLCon) (Γ : context) (P hz hs : term),
    FundTy wl (Γ,, tNat) P ->
    FundTm wl Γ P[tZero..] hz ->
    FundTm wl Γ (elimSuccHypTy P) hs ->
    FundTmEq wl Γ P[tZero..] (tNatElim P hz hs tZero) hz.
  Proof.
    intros * [] [] []; unshelve econstructor; tea.
    3: irrValid.
    3: eapply natElimZeroValid; irrValid.
    eapply natElimValid; irrValid.
    Unshelve. irrValid.
  Qed.

  Lemma FundTmEqNatElimSucc : forall (wl : wfLCon) (Γ : context) (P hz hs n : term),
    FundTy wl (Γ,, tNat) P ->
    FundTm wl Γ P[tZero..] hz ->
    FundTm wl Γ (elimSuccHypTy P) hs ->
    FundTm wl Γ tNat n ->
    FundTmEq wl Γ P[(tSucc n)..] (tNatElim P hz hs (tSucc n))
      (tApp (tApp hs n) (tNatElim P hz hs n)).
  Proof.
    intros *  [] [] [] []; unshelve econstructor; tea.
    4: eapply natElimSuccValid; irrValid.
    1: eapply natElimValid; irrValid.
    eapply simple_appValid.
    2: eapply natElimValid; irrValid.
    eapply irrelevanceTm'.
    2: now eapply appValid.
    now bsimpl.
    Unshelve. all: try irrValid.
    eapply simpleArrValid; eapply substS; tea.
    1,2: irrValid.
    eapply succValid; irrValid.
  Qed.

  Lemma FundTmEqBoolElimCong : forall (wl : wfLCon) (Γ : context)
      (P P' ht ht' hf hf' n n' : term),
    FundTyEq wl (Γ,, tBool) P P' ->
    FundTmEq wl Γ P[tTrue..] ht ht' ->
    FundTmEq wl Γ P[tFalse..] hf hf' ->
    FundTmEq wl Γ tBool n n' ->
    FundTmEq wl Γ P[n..] (tBoolElim P ht hf n) (tBoolElim P' ht' hf' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0] [] [].
    pose (VN := boolValid (l:=one) VΓ0).
    assert (VP' : [ _ ||-v<one> P' | validSnoc' VΓ0 VN]< wl >) by irrValid. 
    assert [Γ ||-v< one > ht' : P'[tTrue..] | VΓ0 | substS VP' (trueValid VΓ0)]< wl >. 1:{
      eapply conv. 2: irrValid.
      eapply substSEq. 2,3: irrValid.
      1: eapply reflValidTy.
      2: eapply reflValidTm.
      all: eapply trueValid.
    }
    assert [Γ ||-v< one > hf' : P'[tFalse..] | VΓ0 | substS VP' (falseValid VΓ0)]< wl >. 1:{
      eapply conv. 2: irrValid.
      eapply substSEq. 2,3: irrValid.
      1: eapply reflValidTy.
      2: eapply reflValidTm.
      all: eapply falseValid.
    }
    unshelve econstructor; tea.
    2: eapply boolElimValid; irrValid.
    + eapply conv.
      2: eapply irrelevanceTm; now eapply boolElimValid.
      eapply symValidTyEq. 
      eapply substSEq; tea. 
      2,3: irrValid.
      eapply reflValidTy.
    + eapply boolElimCongValid; tea; try irrValid.
    Unshelve. all: try irrValid.
    1: eapply trueValid.
    1: eapply falseValid.
    1: unshelve eapply substS; try irrValid.
  Qed.

  Lemma FundTmEqBoolElimTrue : forall (wl : wfLCon) (Γ : context) (P ht hf : term),
    FundTy wl (Γ,, tBool) P ->
    FundTm wl Γ P[tTrue..] ht ->
    FundTm wl Γ P[tFalse..] hf ->
    FundTmEq wl Γ P[tTrue..] (tBoolElim P ht hf tTrue) ht.
  Proof.
    intros * [] [] []; unshelve econstructor; tea.
    3: irrValid.
    3: eapply boolElimTrueValid; irrValid.
    eapply boolElimValid; irrValid.
    Unshelve. irrValid.
  Qed.

  Lemma FundTmEqBoolElimFalse : forall (wl : wfLCon) (Γ : context) (P ht hf : term),
    FundTy wl (Γ,, tBool) P ->
    FundTm wl Γ P[tTrue..] ht ->
    FundTm wl Γ P[tFalse..] hf ->
    FundTmEq wl Γ P[tFalse..] (tBoolElim P ht hf tFalse) hf.
  Proof.
    intros * [] [] []; unshelve econstructor.
    1: tea.
    3: irrValid.
    3: eapply boolElimFalseValid; irrValid.
    eapply boolElimValid; irrValid.
    Unshelve. irrValid.
  Qed.

  Lemma FundTmEqAlphaCong : forall (wl : wfLCon) (Γ : context) (n n' : term),
      FundTmEq wl Γ tNat n n' -> FundTmEq wl Γ tNat (tAlpha n) (tAlpha n').
  Proof.
    intros * []; unshelve econstructor; tea.
    1,2: eapply irrelevanceTm; eapply alphaValid; irrValid.
    eapply irrelevanceTmEq; eapply alphacongValid; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTmEqAlpha : forall (wl : wfLCon) (Γ : context) (n b : nat),
      FundCon wl Γ -> in_LCon wl n b ->
      FundTmEq wl Γ tNat (tAlpha (nat_to_term n)) (nat_to_term b).
  Proof.
    intros * wfG Hin.
    unshelve econstructor.
    - eassumption.
    - now eapply natValid.
    - eapply alphaValid.
      clear Hin ; induction n.
      + now eapply zeroValid.
      + cbn ; now eapply succValid.
    - unfold nat_to_term ; unshelve econstructor.
      + intros ; rewrite nSucc_subst ; cbn.
        unshelve eapply WnSucc_Red, zeroValid ; cycle 2 ; eassumption.
      + intros ; do 2 rewrite nSucc_subst ; cbn.
        clear Hin ; induction b ; cbn ; [unshelve eapply zeroValid ; cycle 8; eassumption| ].
        eapply WsuccRedEq ; cbn ; try eassumption.
        1,2: unshelve eapply WnSucc_Red, zeroValid ; [ .. | eassumption].
    - now eapply alphacongValidSubst.
  Qed.
  
  Lemma FundTmEqEmptyElimCong : forall (wl : wfLCon) (Γ : context)
      (P P' n n' : term),
    FundTyEq wl (Γ,, tEmpty) P P' ->
    FundTmEq wl Γ tEmpty n n' ->
    FundTmEq wl Γ P[n..] (tEmptyElim P n) (tEmptyElim P' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0].
    pose (VN := emptyValid (l:=one) VΓ0).
    assert (VP' : [ _ ||-v<one> P' | validSnoc' VΓ0 VN]< wl >) by irrValid.
    unshelve econstructor; tea.
    2: eapply emptyElimValid; irrValid.
    + eapply conv.
      2: eapply irrelevanceTm; now eapply emptyElimValid.
      eapply symValidTyEq.
      eapply substSEq; tea.
      2,3: irrValid.
      eapply reflValidTy.
    + eapply emptyElimCongValid; tea; try irrValid.
    Unshelve. all: try irrValid.
    1: unshelve eapply substS; try irrValid.
  Qed.


  Lemma FundTySig : forall wl (Γ : context) (A B : term),
  FundTy wl Γ A -> FundTy wl (Γ,, A) B -> FundTy wl Γ (tSig A B).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    unshelve eapply SigValid; tea; irrValid.
  Qed.

  Lemma FundTmSig : forall wl (Γ : context) (A B : term),
    FundTm wl Γ U A ->
    FundTm wl (Γ,, A) U B -> FundTm wl Γ U (tSig A B).
  Proof.
    intros * [] []; unshelve econstructor.
    3: unshelve eapply SigValidU.
    3-5: irrValid.
    1: tea.
    unshelve eapply univValid; tea.
  Qed.

  Lemma FundTmPair : forall wl (Γ : context) (A B a b : term),
    FundTy wl Γ A ->
    FundTy wl (Γ,, A) B ->
    FundTm wl Γ A a ->
    FundTm wl Γ B[a..] b -> FundTm wl Γ (tSig A B) (tPair A B a b).
  Proof.
    intros * [] [] [] []; unshelve econstructor.
    3: unshelve eapply pairValid; irrValid.
    tea.
  Qed.

  Lemma FundTmFst : forall wl (Γ : context) (A B p : term),
    FundTm wl Γ (tSig A B) p -> FundTm wl Γ A (tFst p).
  Proof.
    intros * []; unshelve econstructor.
    3: unshelve eapply fstValid.
    5: irrValid.
    2: now eapply domSigValid.
    now eapply codSigValid.
  Qed.

  Lemma FundTmSnd : forall wl (Γ : context) (A B p : term),
    FundTm wl Γ (tSig A B) p -> FundTm wl Γ B[(tFst p)..] (tSnd p).
  Proof.
    intros * []; unshelve econstructor.
    3: unshelve eapply sndValid.
    5: irrValid.
    2: now eapply domSigValid.
    now eapply codSigValid.
  Qed.

  Lemma FundTyEqSigCong : forall wl (Γ : context) (A B C D : term),
    FundTy wl Γ A ->
    FundTyEq wl Γ A B ->
    FundTyEq wl (Γ,, A) C D -> FundTyEq wl Γ (tSig A C) (tSig B D).
  Proof.
    intros * [] [] [].
    unshelve econstructor.
    4: eapply SigCong; tea; try irrValid.
    2: eapply irrelevanceLift; irrValid.
    eapply SigValid; eapply irrelevanceLift; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSigCong :forall wl (Γ : context) (A A' B B' : term),
    FundTm wl Γ U A ->
    FundTmEq wl Γ U A A' ->
    FundTmEq wl (Γ,, A) U B B' -> FundTmEq wl Γ U (tSig A B) (tSig A' B').
  Proof.
    intros * [] [] []; unshelve econstructor.
    5: eapply SigCongTm; tea; try irrValid.
    4: eapply irrelevanceTmLift ; try irrValid; now eapply univEqValid.
    1,2: unshelve eapply SigValidU; try irrValid.
    1,2: now eapply univValid.
    1: eapply UValid.
    eapply irrelevanceTmLift ; try irrValid; now eapply univEqValid.
    Unshelve. all: solve [ eapply UValid | now eapply univValid | irrValid].
  Qed.

  Lemma FundTmEqPairCong : forall wl (Γ : context) (A A' A'' B B' B'' a a' b b' : term),
    FundTy wl Γ A ->
    FundTyEq wl Γ A A' ->
    FundTyEq wl Γ A A'' ->
    FundTyEq wl (Γ,, A) B B' ->
    FundTyEq wl (Γ,, A) B B'' ->
    FundTmEq wl Γ A a a' ->
    FundTmEq wl Γ B[a..] b b' -> FundTmEq wl Γ (tSig A B) (tPair A' B' a b) (tPair A'' B'' a' b').
  Proof.
    intros * [VΓ VA] [] [] [] [] [] [].
    assert (VΣ : [Γ ||-v< one > tSig A B | VΓ]< wl >).
    { unshelve eapply SigValid; irrValid. }
    assert (VA' : [Γ ||-v< one > A' | VΓ]< wl >) by irrValid.
    assert (VA'' : [Γ ||-v< one > A'' | VΓ]< wl >) by irrValid.
    assert ([Γ ||-v< one > a : A' | VΓ | VA']< wl >).
    { eapply conv; [|irrValid]; irrValid. Unshelve. tea. }
    assert ([Γ ||-v< one > a : A'' | VΓ | VA'']< wl >).
    { eapply conv; [irrValid|]; irrValid. Unshelve. tea. }
    assert ([Γ ||-v< one > a' : A'' | VΓ | VA'']< wl >).
    { eapply conv; [irrValid|]; irrValid. Unshelve. tea. }
    assert (VΓA' : VAdequate (ta := ta) wl (Γ,, A') VR) by now eapply validSnoc'.
    assert (VΓA'' : VAdequate (ta := ta) wl (Γ,, A'') VR) by now eapply validSnoc'.
    assert (VA'B : [Γ,, A' ||-v< one > B | VΓA']< wl >).
    { eapply irrelevanceTy, irrelevanceLift; irrValid.
      Unshelve. all: irrValid. }
    assert (VA''B : [Γ,, A'' ||-v< one > B | VΓA'']< wl >).
    { eapply irrelevanceTy, irrelevanceLift; irrValid.
      Unshelve. all: irrValid. }
    assert (VA'B' : [Γ,, A' ||-v< one > B' | VΓA']< wl >).
    { eapply irrelevanceTy, irrelevanceLift; try irrValid.
      Unshelve. all: irrValid. }
    assert (VA''B' : [Γ,, A'' ||-v< one > B' | VΓA'']< wl >).
    { eapply irrelevanceTy, irrelevanceLift; try irrValid.
      Unshelve. all: irrValid. }
    assert (VA''B'' : [Γ,, A'' ||-v< one > B'' | VΓA'']< wl >).
    { eapply irrelevanceTy, irrelevanceLift; try irrValid.
      Unshelve. all: irrValid. }
    assert (VBa : [Γ ||-v< one > B[a..] | VΓ]< wl >).
    { irrValid. }
    assert (VB'a : [Γ ||-v< one > B'[a..] | VΓ]< wl >).
    { eapply substS; irrValid. Unshelve. all: irrValid. }
    assert (VB''a : [Γ ||-v< one > B''[a..] | VΓ]< wl >).
    { eapply substS; irrValid. Unshelve. all: irrValid. }
    assert (VB''a' : [Γ ||-v< one > B''[a'..] | VΓ]< wl >).
    { eapply substS; irrValid. Unshelve. all: irrValid. }
    assert [Γ ||-v< one > B[a..] ≅ B'[a..] | VΓ | VBa]< wl >.
    { eapply irrelevanceTyEq, substSEq; try irrValid.
      apply reflValidTm. irrValid. Unshelve. all: irrValid. }
    assert [Γ ||-v< one > B[a..] ≅ B''[a'..] | VΓ | VBa]< wl >.
    { eapply irrelevanceTyEq, substSEq; [..|irrValid|irrValid].
      all: irrValid. Unshelve. all: irrValid. }
    assert (VΣA'B' : [Γ ||-v< one > tSig A' B' | VΓ]< wl >).
    { unshelve eapply SigValid; try irrValid. }
    assert (VΣA''B'' : [Γ ||-v< one > tSig A'' B'' | VΓ]< wl >).
    { unshelve eapply SigValid; try irrValid. }
    assert ([Γ ||-v< one > tSig A B ≅ tSig A' B' | VΓ | VΣ]< wl >).
    { unshelve eapply irrelevanceTyEq, SigCong; try irrValid. }
    assert ([Γ ||-v< one > tSig A B ≅ tSig A'' B'' | VΓ | VΣ]< wl >).
    { unshelve eapply irrelevanceTyEq, SigCong; try irrValid. }
    assert [Γ ||-v< one > tPair A' B' a b : tSig A B | _ | VΣ ]< wl >.
    { eapply conv; [|unshelve eapply pairValid]; try irrValid.
      - unshelve eapply symValidTyEq; irrValid.
      - eapply conv; irrValid. Unshelve. all: irrValid. }
    assert [Γ ||-v< one > tPair A'' B'' a' b' : tSig A B | _ | VΣ ]< wl >.
    { eapply conv; [|unshelve eapply pairValid]; try irrValid.
      - unshelve eapply symValidTyEq; irrValid.
      - eapply conv; irrValid.
        Unshelve. all: irrValid. }
    assert [Γ ||-v< one > b : B'[a..] | VΓ | VB'a]< wl >.
    { eapply conv; irrValid. Unshelve. all: irrValid. }
    assert [Γ ||-v< one > b' : B''[a'..] | VΓ | VB''a']< wl >.
    { eapply conv; irrValid. Unshelve. all: irrValid. }
    assert ([Γ ||-v< one > tFst (tPair A' B' a b) ≅ a : A | VΓ | VA]< wl >).
    { eapply (convEq (A := A')); [eapply symValidTyEq; irrValid|].
      eapply pairFstValid. Unshelve. all: try irrValid. }
    assert ([Γ ||-v< one > tFst (tPair A'' B'' a' b') ≅ a' : A | VΓ | VA]< wl >).
    { eapply (convEq (A := A'')); [eapply symValidTyEq; irrValid|].
      eapply pairFstValid. Unshelve. all: irrValid. }
    assert ([Γ ||-v< one > tFst (tPair A' B' a b) ≅ tFst (tPair A'' B'' a' b') : A | VΓ | VA]< wl >).
    { eapply transValidTmEq; [irrValid|].
      eapply transValidTmEq; [irrValid|].
      eapply symValidTmEq; irrValid. }
    assert ([Γ ||-v< one > tFst (tPair A' B' a b) : A | VΓ | VA]< wl >).
    { eapply fstValid. Unshelve. all: try irrValid. }
    assert ([Γ ||-v< one > tFst (tPair A'' B'' a' b') : A | VΓ | VA]< wl >).
    { eapply fstValid. Unshelve. all: try irrValid. }
    assert (VBfst : [Γ ||-v< one > B[(tFst (tPair A' B' a b))..] | VΓ]< wl >).
    { eapply (substS (F := A)). Unshelve. all: try  irrValid. }
    assert (VB'fst : [Γ ||-v< one > B'[(tFst (tPair A' B' a b))..] | VΓ]< wl >).
    { eapply (substS (F := A)). Unshelve. all: try  irrValid. }
    assert (VB''fst' : [Γ ||-v< one > B''[(tFst (tPair A'' B'' a' b'))..] | VΓ]< wl >).
    { eapply (substS (F := A)). Unshelve. all: try irrValid. }
    assert ([Γ ||-v< one > B[(tFst (tPair A' B' a b))..] ≅ B[a..] | VΓ | VBfst]< wl >).
    { eapply irrelevanceTyEq, substSEq; [..|irrValid|irrValid].
      Unshelve. all: try irrValid. eapply reflValidTy. }
    assert ([Γ ||-v< one > B'[(tFst (tPair A' B' a b))..] ≅ B[a..] | VΓ | VB'fst]< wl >).
    { eapply irrelevanceTyEq, substSEq; [..|irrValid|irrValid].
      Unshelve. all: try irrValid.
      eapply symValidTyEq; irrValid. Unshelve. all: try irrValid. }
    assert ([Γ ||-v< one > B''[(tFst (tPair A'' B'' a' b'))..] ≅ B[a'..] | VΓ | VB''fst']< wl >).
    { eapply irrelevanceTyEq, substSEq; [..|irrValid|].
      Unshelve. all: try irrValid.
      eapply symValidTyEq; irrValid. Unshelve. all: try irrValid. }
    assert ([Γ ||-v< one > B''[(tFst (tPair A'' B'' a' b'))..] ≅ B[a..] | VΓ | VB''fst']< wl >).
    { eapply irrelevanceTyEq, substSEq; [..|irrValid|].
      Unshelve. all: try irrValid.
      eapply symValidTyEq; irrValid. Unshelve. all: try irrValid.
      eapply transValidTmEq; [irrValid|].
      eapply symValidTmEq; irrValid.
    }
    assert ([Γ ||-v< one > tSnd (tPair A' B' a b) ≅ b : B[(tFst (tPair A' B' a b))..] | VΓ | VBfst]< wl >).
    { eapply (convEq (A := B'[(tFst (tPair A' B' a b))..])).
      shelve. eapply pairSndValid.
      Unshelve. all: try irrValid.
      eapply irrelevanceTyEq, substSEq; [..|irrValid|apply reflValidTm; irrValid].
      all: try irrValid.
      - unshelve apply reflValidTy.
      - unshelve eapply symValidTyEq; irrValid. }
    assert ([Γ ||-v< one > tSnd (tPair A'' B'' a' b') ≅ b' : B[a..] | VΓ | VBa]< wl >).
    { eapply (convEq (A := B''[(tFst (tPair A'' B'' a' b'))..])).
      shelve. eapply pairSndValid.
      Unshelve. all: try irrValid. }
    unshelve econstructor. 1-4: irrValid.
    eapply irrelevanceTmEq, sigEtaValid; try irrValid.
    eapply transValidTmEq; [irrValid|].
    eapply transValidTmEq.
    - eapply convEq; [|irrValid].
      eapply symValidTyEq; try irrValid.
    - eapply symValidTmEq; try irrValid.
      eapply convEq; [|irrValid].
      eapply symValidTyEq; try irrValid.
  Unshelve. all: try irrValid.
  Qed.

  Lemma FundTmEqSigEta : forall wl (Γ : context) (A B p : term),
    FundTm wl Γ (tSig A B) p -> FundTmEq wl Γ (tSig A B) (tPair A B (tFst p) (tSnd p)) p.
  Proof.
  intros * [VΓ VΣ Vp].
  assert (VA := domSigValid _ VΣ).
  assert (VB := codSigValid _ VΣ).
  assert (Vfst : [Γ ||-v< one > tFst p : A | _ | VA]< wl >).
  { unshelve eapply irrelevanceTm, fstValid; try irrValid. }
  assert (VBfst : [Γ ||-v< one > B[(tFst p)..] | VΓ]< wl >).
  { unshelve eapply substS; try irrValid. }
  assert (Vsnd : [Γ ||-v< one > tSnd p : B[(tFst p)..] | _ | VBfst]< wl >).
  { unshelve eapply irrelevanceTm, sndValid.
    5: irrValid. all: irrValid. }
  assert (Vηp : [Γ ||-v< one > tPair A B (tFst p) (tSnd p) : tSig A B | VΓ | VΣ]< wl >).
  { unshelve eapply irrelevanceTm, pairValid; try irrValid. }
  unshelve econstructor; try irrValid.
  eapply irrelevanceTmEq, sigEtaValid; try irrValid.
  - eapply transValidTmEq; [eapply pairFstValid|eapply reflValidTm].
    Unshelve. all: try irrValid.
  - eapply transValidTmEq; [unshelve eapply irrelevanceTmEq, pairSndValid|unshelve eapply reflValidTm]; try irrValid.
    unshelve eapply conv; try irrValid.
    eapply irrelevanceTyEq, substSEq; try irrValid.
    1,2: unshelve apply reflValidTy.
    { unshelve eapply fstValid; try irrValid. }
    { unshelve eapply symValidTmEq, pairFstValid; try irrValid. }
    Unshelve. all: try irrValid.
  Qed.

  Lemma FundTmEqFstCong : forall wl (Γ : context) (A B p p' : term),
    FundTmEq wl Γ (tSig A B) p p' -> FundTmEq wl Γ A (tFst p) (tFst p').
  Proof.
    intros * []; unshelve econstructor.
    5: eapply fstCongValid; irrValid.
    2: now eapply domSigValid.
    1,2: eapply fstValid; irrValid.
    Unshelve. all: now eapply codSigValid.
  Qed.

  Lemma FundTmEqFstBeta : forall wl (Γ : context) (A B a b : term),
    FundTy wl Γ A ->
    FundTy wl (Γ,, A) B ->
    FundTm wl Γ A a ->
    FundTm wl Γ B[a..] b -> FundTmEq wl Γ A (tFst (tPair A B a b)) a.
  Proof.
    intros * [] [] [] [].
    unshelve econstructor.
    3,5: eapply pairFstValid; irrValid.
    2,3: irrValid. 
    tea.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSndCong : forall wl (Γ : context) (A B p p' : term),
    FundTmEq wl Γ (tSig A B) p p' -> FundTmEq wl Γ B[(tFst p)..] (tSnd p) (tSnd p').
  Proof.
    intros * []; unshelve econstructor.
    5: eapply sndCongValid; irrValid.
    1: tea.
    1: eapply sndValid.
    eapply conv; [| eapply sndValid].
    eapply substSEq.
    5: eapply fstCongValid.
    4: eapply fstValid.
    4-6: irrValid.
    + eapply reflValidTy.
    + eapply codSigValid.
    + eapply reflValidTy.
    + eapply symValidTmEq; irrValid.
    Unshelve. all: try solve [now eapply domSigValid| now eapply codSigValid| irrValid].
  Qed.

  Lemma FundTmEqSndBeta : forall wl (Γ : context) (A B a b : term),
    FundTy wl Γ A ->
    FundTy wl (Γ,, A) B ->
    FundTm wl Γ A a ->
    FundTm wl Γ B[a..] b ->
    FundTmEq wl Γ B[(tFst (tPair A B a b))..] (tSnd (tPair A B a b)) b.
  Proof.
    intros * [] [] [] []; unshelve econstructor.
    3,5: unshelve eapply pairSndValid; irrValid.
    + tea.
    + eapply conv; tea.
      eapply irrelevanceTyEq.
      eapply substSEq.
      1,3: eapply reflValidTy.
      1: irrValid.
      2: eapply symValidTmEq.
      1,2: eapply pairFstValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyId : forall wl (Γ : context) (A x y : term),
    FundTy wl Γ A -> FundTm wl Γ A x -> FundTm wl Γ A y -> FundTy wl Γ (tId A x y).
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    unshelve eapply IdValid; irrValid.
  Qed.


  Lemma FundTmId : forall wl (Γ : context) (A x y : term),
    FundTm wl Γ U A -> FundTm wl Γ A x -> FundTm wl Γ A y -> FundTm wl Γ U (tId A x y).
  Proof.
      intros * [] [] [].
      unshelve econstructor; tea.
      1: eapply UValid.
      unshelve eapply IdTmValid; cycle 1; try irrValid; tea.
  Qed.

  Lemma FundTmRefl : forall wl (Γ : context) (A x : term),
    FundTy wl Γ A -> FundTm wl Γ A x -> FundTm wl Γ (tId A x x) (tRefl A x).
  Proof.
    intros * [] []; unshelve econstructor.
    3: now eapply reflValid.
    now eapply IdValid.
  Qed.

  Lemma FundTmIdElim : forall wl (Γ : context) (A x P hr y e : term),
    FundTy wl Γ A ->
    FundTm wl Γ A x ->
    FundTy wl ((Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P ->
    FundTm wl Γ P[tRefl A x .: x..] hr ->
    FundTm wl Γ A y -> FundTm wl Γ (tId A x y) e -> FundTm wl Γ P[e .: y..] (tIdElim A x P hr y e).
  Proof.
    intros * [] [] [] [] [] []; unshelve econstructor.
    3: unshelve eapply IdElimValid; try irrValid.
    tea.
  Qed.

  Lemma FundTyEqId : forall wl (Γ : context) (A A' x x' y y' : term),
    FundTyEq wl Γ A A' ->
    FundTmEq wl Γ A x x' -> FundTmEq wl Γ A y y' -> FundTyEq wl Γ (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    3: eapply IdCongValid; irrValid.
    1,2: eapply IdValid; try irrValid.
    1,2: eapply conv; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqIdCong : forall wl (Γ : context) (A A' x x' y y' : term),
    FundTmEq wl Γ U A A' ->
    FundTmEq wl Γ A x x' -> FundTmEq wl Γ A y y' -> FundTmEq wl Γ U (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] []; unshelve econstructor.
    5: eapply IdTmCongValid; try irrValid; tea.
    2,3: eapply IdTmValid; try irrValid; tea.
    1: tea.
    1,2: eapply conv; try irrValid; eapply univEqValid; irrValid.
    Unshelve. all: first [eapply UValid| irrValid | tea].
  Qed.

  Lemma FundTmEqReflCong : forall wl (Γ : context) (A A' x x' : term),
    FundTyEq wl Γ A A' -> FundTmEq wl Γ A x x' -> FundTmEq wl Γ (tId A x x) (tRefl A x) (tRefl A' x').
  Proof.
    intros * [] []; unshelve econstructor.
    5: eapply reflCongValid; tea; irrValid.
    3: eapply conv.
    2,4: eapply reflValid; try irrValid.
    2: eapply conv; irrValid.
    2: eapply symValidTyEq; eapply IdCongValid; tea; try irrValid.
    eapply IdValid; irrValid.
    Unshelve. all: try eapply IdValid; try irrValid; eapply conv; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqIdElimCong : forall wl (Γ : context) (A A' x x' P P' hr hr' y y' e e' : term),
    FundTy wl Γ A ->
    FundTm wl Γ A x ->
    FundTyEq wl Γ A A' ->
    FundTmEq wl Γ A x x' ->
    FundTyEq wl ((Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P P' ->
    FundTmEq wl Γ P[tRefl A x .: x..] hr hr' ->
    FundTmEq wl Γ A y y' ->
    FundTmEq wl Γ (tId A x y) e e' -> FundTmEq wl Γ P[e .: y..] (tIdElim A x P hr y e) (tIdElim A' x' P' hr' y' e').
  Proof.
    intros * [] [] [] [] [] [] [] [].
    assert [_ ||-v<one> x' : _ | _ | VB]< wl > by (eapply conv; irrValid).
    assert [_ ||-v<one> y' : _ | _ | VB]< wl > by (eapply conv; irrValid).
    assert (VId' : [_ ||-v<one> tId A' x' y' | VΓ]< wl >) by (eapply IdValid; irrValid).
    assert [_ ||-v<one> _ ≅ tId A' x' y' | _ | VA6]< wl > by (eapply IdCongValid; irrValid).
    assert [_ ||-v<one> e' : _ | _ | VId']< wl > by (eapply conv; irrValid).
    unshelve econstructor.
    5: eapply IdElimCongValid; tea; irrValid.
    1: eapply IdElimValid; irrValid.
    eapply convsym.
    2: eapply IdElimValid; eapply conv; [|irrValid].
    1:{
      eapply substEqIdElimMotive. 7: tea. 2,3,5-12: tea; try irrValid. 1,2: irrValid.
    } 
   eapply substEqIdElimMotive. 7: tea. 2,3,5-9: tea; try irrValid.
    1,2: irrValid.
    2: eapply convsym. 
    1,3: eapply reflValid; first [irrValid| eapply conv; irrValid].
    1:eapply IdCongValid; irrValid.
    eapply reflCongValid; irrValid.
    Unshelve. all: tea; try irrValid.
    3,4: eapply IdValid; irrValid.
    1: eapply validSnoc'; now eapply idElimMotiveCtxIdValid.
    eapply convCtx2'; tea.
    1: eapply convCtx1; tea; [eapply symValidTyEq; irrValid| ].
    1,3: now eapply idElimMotiveCtxIdValid.
    eapply idElimMotiveCtxIdCongValid; tea; irrValid.
    Unshelve.
    3: eapply idElimMotiveCtxIdValid. all: irrValid.
  Qed.

  Lemma FundTmEqIdElimRefl : forall wl (Γ : context) (A x P hr y A' z : term),
    FundTy wl Γ A ->
    FundTm wl Γ A x ->
    FundTy wl ((Γ,, A),, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A ⟩ (tRel 0)) P ->
    FundTm wl Γ P[tRefl A x .: x..] hr ->
    FundTm wl Γ A y ->
    FundTy wl Γ A' ->
    FundTm wl Γ A z ->
    FundTyEq wl Γ A A' ->
    FundTmEq wl Γ A x y ->
    FundTmEq wl Γ A x z -> FundTmEq wl Γ P[tRefl A' z .: y..] (tIdElim A x P hr y (tRefl A' z)) hr.
  Proof.
    intros * [] [] [] [] [] [] [] [] [] [].
    assert (VId : [_ ||-v<one> tId A x y | VΓ]< wl >) by (unshelve eapply IdValid; irrValid).
    assert [Γ ||-v< one > tRefl A' z : tId A x y | _ | VId]< wl >.
    1:{
      eapply convsym ; [| eapply reflValid; try irrValid].
      2: eapply conv; irrValid.
      eapply IdCongValid; try irrValid.
      eapply transValidTmEq; [eapply symValidTmEq|]; irrValid.
      Unshelve.
       1: unshelve eapply IdValid; try eapply conv. 
       all: try irrValid.
       Unshelve. all: irrValid.
    } 
    unshelve econstructor.
    5: eapply IdElimReflValid; tea; try irrValid.
    3: eapply conv; irrValid.
    2:{
      eapply conv; [|irrValid].
      eapply substExtIdElimMotive; cycle 1; tea.
      + eapply reflValid; irrValid.
      + irrValid.
      + eapply reflCongValid; tea; irrValid.
    }
    eapply IdElimValid; irrValid.
    Unshelve. all: tea; try irrValid.
      unshelve eapply IdValid; irrValid.
  Qed.

Lemma FundTySplit : forall (wl : wfLCon)
  (Γ : context)
  (A : term)
  (n : nat)
  (ne : not_in_LCon wl n),
  (forall m, FundTy (wl,,l (ne, m)) Γ A) ->
  FundTy wl Γ A.
Proof.
  intros ????? Hyp.
  unshelve econstructor.
  2: unshelve eapply validTySplit ; try eassumption.
  2: intros m ; destruct (Hyp m) ; now eauto.
  2: cbn ; intros m ; now destruct (Hyp m).
  eapply WfCSplit ;intros m ; now destruct (Hyp m).
Qed.

Lemma FundTmSplit : forall (wl : wfLCon)
  (Γ : context)
  (A t : term)
  (n : nat)
  (ne : not_in_LCon wl n),
  (forall m, FundTm (wl,,l (ne, m)) Γ A t) ->
  FundTm wl Γ A t.
Proof.
  intros ?????? Hyp.
  unshelve econstructor.
  - eapply WfCSplit ; intros m ; now destruct (Hyp m).
  - eapply validTySplit ; intros m ; destruct (Hyp m).
    irrValid.
  - unshelve eapply validTmSplit' ; [ | eassumption | ..].
    all: intros m ;destruct (Hyp m) ; eauto.
    all: irrValid.
    Unshelve.
    intros m ; now destruct (Hyp m).
Qed.

Lemma FundTyEqSplit : forall (wl : wfLCon)
  (Γ : context)
  (A B : term)
  (n : nat)
  (ne : not_in_LCon wl n),
  (forall m, FundTyEq (wl,,l (ne, m)) Γ A B) ->
  FundTyEq wl Γ A B.
Proof.
  intros ?????? Hyp.
  unshelve econstructor.
  - now eapply WfCSplit ; intros m ; now destruct (Hyp m).
  - eapply validTySplit ; intros m ; destruct (Hyp m).
    irrValid.
  - eapply validTySplit ; intros m ; destruct (Hyp m).
    irrValid.
  - unshelve eapply validEqTySplit' ; try eassumption.
    all: intros m ;destruct (Hyp m) ; eauto.
    all: irrValid.
    Unshelve.
    all: intros m ; now destruct (Hyp m).
Qed.

Lemma FundTmEqSplit : forall (wl : wfLCon)
  (Γ : context)
  (t u A : term)
  (n : nat)
  (ne : not_in_LCon wl n),
  (forall m, FundTmEq (wl,,l (ne, m)) Γ A t u) ->
  FundTmEq wl Γ A t u.
Proof.
  intros ??????? Hyp.
  unshelve econstructor.
  - now eapply WfCSplit ; intros m ; now destruct (Hyp m).
  - eapply validTySplit ; intros m ; destruct (Hyp m) ; now irrValid.
  - eapply validTmSplit' ; intros m ; destruct (Hyp m) ; now irrValid.
  - eapply validTmSplit' ; intros m ; destruct (Hyp m) ; now irrValid.
  - eapply validEqTmSplit' ; intros m ; destruct (Hyp m) ; now irrValid.
    Unshelve.
    all: intros m ; try now destruct (Hyp m).
    all: destruct (Hyp m) ; now irrValid.
Qed.  
  
  Lemma Fundamental (wl : wfLCon) :
    (forall (Γ : context), [ |-[ de ] Γ ]< wl > -> FundCon wl (ta := ta) Γ)
    × (forall (Γ : context) (A : term), [Γ |-[ de ] A]< wl > -> FundTy wl (ta := ta) Γ A)
    × (forall (Γ : context) (A t : term), [Γ |-[ de ] t : A]< wl > -> FundTm wl (ta := ta) Γ A t)
    × (forall (Γ : context) (A B : term), [Γ |-[ de ] A ≅ B]< wl > -> FundTyEq wl (ta := ta) Γ A B)
    × (forall (Γ : context) (A t u : term), [Γ |-[ de ] t ≅ u : A]< wl > -> FundTmEq wl (ta := ta) Γ A t u).
  Proof.
  apply WfDeclInduction ; intros.
  + intros; now apply FundConNil.
  + intros; now apply FundConCons.
  + intros; now apply FundTyU.
  + intros; now apply FundTyPi.
  + intros; now apply FundTyNat.
  + intros; now apply FundTyEmpty.
  + intros; now apply FundTyBool.
  + intros; now apply FundTySig.
  + intros; now apply FundTyId.
  + intros; now apply FundTyUniv.
  + intros; now eapply FundTySplit. 
  + intros; now apply FundTmVar.
  + intros; now apply FundTmProd.
  + intros; now apply FundTmLambda.
  + intros; now eapply FundTmApp.
  + intros; now apply FundTmNat.
  + intros; now apply FundTmBool.
  + intros; now apply FundTmZero.
  + intros; now apply FundTmSucc.
  + intros; now apply FundTmNatElim.
  + intros; now apply FundTmEmpty.
  + intros; now apply FundTmEmptyElim.
  + intros; now apply FundTmTrue.
  + intros; now apply FundTmFalse.
  + intros ; now apply FundTmAlpha. 
  + intros; now apply FundTmBoolElim.
  + intros; now apply FundTmSig.
  + intros; now apply FundTmPair.
  + intros; now eapply FundTmFst.
  + intros; now eapply FundTmSnd.
  + intros; now eapply FundTmId.
  + intros; now eapply FundTmRefl.
  + intros; now eapply FundTmIdElim.
  + intros; now eapply FundTmConv.
  + intros; now eapply FundTmSplit.
  + intros; now apply FundTyEqPiCong.
  + intros; now apply FundTyEqSigCong.
  + intros; now eapply FundTyEqId.
  + intros; now apply FundTyEqRefl.
  + intros; now apply FundTyEqUniv.
  + intros; now apply FundTyEqSym.
  + intros; now eapply FundTyEqTrans.
  + intros; now eapply FundTyEqSplit. 
  + intros; now apply FundTmEqBRed.
  + intros; now apply FundTmEqPiCong.
  + intros; now eapply FundTmEqAppCong.
  + intros; now apply FundTmEqLambdaCong.
  + intros; now apply FundTmEqFunEta.
  + intros; now apply FundTmEqSuccCong.
  + intros; now apply FundTmEqNatElimCong.
  + intros; now apply FundTmEqNatElimZero.
  + intros; now apply FundTmEqNatElimSucc.
  + intros; now apply FundTmEqEmptyElimCong.
  + intros; now apply FundTmEqBoolElimCong.
  + intros; now apply FundTmEqBoolElimTrue. 
  + intros; now apply FundTmEqBoolElimFalse. 
  + intros; now apply FundTmEqAlphaCong. 
  + intros; now apply FundTmEqAlpha.
  + intros; now apply FundTmEqSigCong.
  + intros; now apply FundTmEqPairCong.
  + intros; now apply FundTmEqSigEta.
  + intros; now eapply FundTmEqFstCong.
  + intros; now apply FundTmEqFstBeta.
  + intros; now eapply FundTmEqSndCong.
  + intros; now apply FundTmEqSndBeta.
  + intros; now apply FundTmEqIdCong.
  + intros; now apply FundTmEqReflCong.
  + intros; now apply FundTmEqIdElimCong.
  + intros; now apply FundTmEqIdElimRefl.
  + intros; now apply FundTmEqRefl.
  + intros; now eapply FundTmEqConv.
  + intros; now apply FundTmEqSym.
  + intros; now eapply FundTmEqTrans.
  + intros; now eapply FundTmEqSplit. 
  Qed.

(** ** Well-typed substitutions are also valid *)

  Corollary Fundamental_subst wl wl' Γ Δ σ f (wfΓ : [|-[ta] Γ ]< wl' >) :
    [|-[de] Δ]< wl > ->
    [Γ |-[de]s σ : Δ]< wl' > ->
    FundSubst wl wl' Γ Δ σ f wfΓ .
  Proof.
    intros HΔ.
    induction 1 as [|σ Δ A Hσ IH Hσ0].
    - exists validEmpty'.
      now constructor.
    - inversion HΔ as [|?? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [?? Hσ0].
      cbn in *.
      eapply reducibleTm in Hσ0.
      eapply Fundamental in HA as [].
      unshelve econstructor.
      1: now eapply validSnoc'.
      unshelve econstructor.
      + now eapply irrelevanceSubst.
      + cbn; Wirrelevance0.
        2: eassumption.
        reflexivity.
  Qed.

  Corollary Fundamental_subst_conv wl wl' Γ Δ σ σ' (f : wl' ≤ε wl) (wfΓ : [|-[ta] Γ ]< wl' >) :
    [|-[de] Δ]< wl > ->
    [Γ |-[de]s σ ≅ σ' : Δ]< wl' > ->
    FundSubstConv Γ Δ σ σ' f wfΓ .
  Proof.
    intros HΔ.
    induction 1 as [|σ τ Δ A Hσ IH Hσ0].
    - unshelve econstructor.
      1: eapply validEmpty'.
      all: now econstructor.
    - inversion HΔ as [|?? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [?? Hσ0 Hτ0 Ηστ] ; cbn in *.
      eapply Fundamental in HA as [? HA].
      unshelve econstructor.
      + now eapply validSnoc'.
      + unshelve econstructor.
        1: now irrValid.
        cbn ; Wirrelevance0 ; [reflexivity | ].
        now eapply reducibleTm.
      + unshelve econstructor.
        1: now eapply irrelevanceSubst.
        cbn.
        unshelve (Wirrelevance0 ; [reflexivity | ]).
        2: now unshelve eapply HA ; tea ; irrValid.
        cbn.
        unshelve eapply WLRTmRedConv.
        3: now eapply reducibleTy.
        * cbn ; Wirrelevance0 ; [reflexivity | ].
          unshelve eapply HA ; tea.
          all: now irrValid.
        * cbn ; Wirrelevance0 ; [reflexivity | ].
          now eapply reducibleTm.
      + unshelve econstructor ; cbn in *.
        * now irrValid.
        * cbn ; Wirrelevance0 ; [reflexivity | ].
          now eapply reducibleTmEq.
  Qed.

End Fundamental.
