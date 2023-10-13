(** * LogRel.Fundamental: declarative typing implies the logical relation for any generic instance. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape.
From LogRel.Substitution.Introductions Require Import Application Universe Pi Lambda Var Nat Empty SimpleArr Sigma Id.

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
  (Γ : context) : Type := [||-v Γ ].

Module FundTy.
  Record FundTy `{GenericTypingProperties} {Γ : context} {A : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ]
  }.

  Arguments FundTy {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTy.

Export FundTy(FundTy,Build_FundTy).

Module FundTyEq.
  Record FundTyEq `{GenericTypingProperties}
    {Γ : context} {A B : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    VB : [ Γ ||-v< one > B | VΓ ];
    VAB : [ Γ ||-v< one > A ≅ B | VΓ | VA ]
  }.
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTyEq.

Export FundTyEq(FundTyEq,Build_FundTyEq).

Module FundTm.
  Record FundTm `{GenericTypingProperties}
    {Γ : context} {A t : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ];
  }.
  Arguments FundTm {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTm.

Export FundTm(FundTm,Build_FundTm).

Module FundTmEq.
  Record FundTmEq `{GenericTypingProperties}
    {Γ : context} {A t u : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ];
    Vu : [ Γ ||-v< one > u : A | VΓ | VA ];
    Vtu : [ Γ ||-v< one > t ≅ u : A | VΓ | VA ];
  }.
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).

Module FundSubst.
  Record FundSubst `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
  }.
  Arguments FundSubst {_ _ _ _ _ _ _ _ _ _ _ _}.
End FundSubst.

Export FundSubst(FundSubst,Build_FundSubst).

Module FundSubstConv.
  Record FundSubstConv `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ σ' : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
    Vσ' : [VΔ | Γ ||-v σ' : Δ | wfΓ ] ;
    Veq : [VΔ | Γ ||-v σ ≅ σ' : Δ | wfΓ | Vσ] ;
  }.
  Arguments FundSubstConv {_ _ _ _ _ _ _ _ _ _ _ _}.
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

  Lemma FundConNil : FundCon ε.
  Proof.
  unshelve econstructor.
  + unshelve econstructor.
    - intros; exact unit.
    - intros; exact unit.
  + constructor.
  Qed.

  Lemma FundConCons (Γ : context) (A : term)
  (fΓ : FundCon Γ) (fA : FundTy Γ A) : FundCon (Γ,, A).
  Proof.
    destruct fA as [ VΓ VA ].
    eapply validSnoc. exact VA.
  Qed.

  Lemma FundTyU (Γ : context) (fΓ : FundCon Γ) : FundTy Γ U.
  Proof.
    unshelve econstructor.
    - assumption.
    - unshelve econstructor.
      + intros * _. apply LRU_.  
        econstructor; tea; [constructor|]. 
        cbn; eapply redtywf_refl; gen_typing.
      + intros * _ _. simpl. constructor.
        cbn; eapply redtywf_refl; gen_typing.
  Qed.

  Lemma FundTyPi (Γ : context) (F G : term)
    (fF : FundTy Γ F) (fG : FundTy (Γ,, F) G)
    : FundTy Γ (tProd F G).
  Proof.
    destruct fF as [ VΓ VF ]. destruct fG as [ VΓF VG ].
    econstructor.
    unshelve eapply (PiValid VΓ).
    - assumption.
    - now eapply irrelevanceTy.
  Qed.

  Lemma FundTyUniv (Γ : context) (A : term)
    (fA : FundTm Γ U A)
    : FundTy Γ A.
  Proof.
    destruct fA as [ VΓ VU [ RA RAext ] ]. econstructor.
    unshelve econstructor.
    - intros * vσ.
      eapply UnivEq. exact (RA _ _ wfΔ vσ).
    - intros * vσ' vσσ'.
      eapply UnivEqEq. exact (RAext _ _ _ wfΔ vσ vσ' vσσ').
  Qed.

  Lemma FundTmVar : forall (Γ : context) (n : nat) decl,
    FundCon Γ ->
    in_ctx Γ n decl -> FundTm Γ decl (tRel n).
  Proof.
    intros Γ n d FΓ hin. 
    unshelve econstructor; tea.
    + eapply in_ctx_valid in hin as []; now eapply embValidTyOne. 
    + now eapply varnValid.
  Qed.

  Lemma FundTmProd : forall (Γ : context) (A B : term),
    FundTm Γ U A ->
    FundTm (Γ,, A) U B -> FundTm Γ U (tProd A B).
  Proof.
    intros * [] []; econstructor.
    eapply PiValidU; irrValid.
    Unshelve. 
    3: eapply UValid. 
    2: eapply univValid. 
    all:tea.
  Qed.

  Lemma FundTmLambda : forall (Γ : context) (A B t : term),
    FundTy Γ A ->
    FundTm (Γ,, A) B t -> FundTm Γ (tProd A B) (tLambda A t).
  Proof.
    intros * [] []; econstructor.
    eapply lamValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmApp : forall (Γ : context) (f a A B : term),
    FundTm Γ (tProd A B) f ->
    FundTm Γ A a -> FundTm Γ B[a..] (tApp f a).
  Proof.
    intros * [] []; econstructor.
    now eapply appValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmConv : forall (Γ : context) (t A B : term),
    FundTm Γ A t ->
    FundTyEq Γ A B -> FundTm Γ B t.
  Proof.
    intros * [] []; econstructor. 
    eapply conv; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTyEqPiCong : forall (Γ : context) (A B C D : term),
    FundTy Γ A ->
    FundTyEq Γ A B ->
    FundTyEq (Γ,, A) C D -> FundTyEq Γ (tProd A C) (tProd B D).
  Proof.
    intros * [] [] []; econstructor.
    - eapply PiValid. eapply irrelevanceLift; tea; irrValid.
    - eapply PiCong. 1: eapply irrelevanceLift; tea.
      all: irrValid.
    Unshelve. all: tea; irrValid.
  Qed.

  Lemma FundTyEqRefl : forall (Γ : context) (A : term),
    FundTy Γ A -> FundTyEq Γ A A.
  Proof.
    intros * []; unshelve econstructor; tea; now eapply reflValidTy.
  Qed.

  Lemma FundTyEqSym : forall (Γ : context) (A B : term),
    FundTyEq Γ A B -> FundTyEq Γ B A.
  Proof.
    intros * [];  unshelve econstructor; tea.
    now eapply symValidTyEq.
  Qed.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    FundTyEq Γ A B ->
    FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
    intros * [] []; unshelve econstructor; tea. 1:irrValid.
    eapply transValidTyEq; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTyEqUniv : forall (Γ : context) (A B : term),
    FundTmEq Γ U A B -> FundTyEq Γ A B.
  Proof.
    intros * []; unshelve econstructor; tea.
    1,2: now eapply univValid.
    now eapply univEqValid.
  Qed.

  Lemma FundTmEqBRed : forall (Γ : context) (a t A B : term),
    FundTy Γ A ->
    FundTm (Γ,, A) B t ->
    FundTm Γ A a -> FundTmEq Γ B[a..] (tApp (tLambda A t) a) t[a..].
  Proof.
    intros * [] [] []; econstructor.
    - eapply appValid. eapply lamValid. irrValid.
    - unshelve epose (substSTm _ _).
      8-12: irrValid.
      tea.
    - unshelve epose (betaValid VA _ _ _). 2,5-7:irrValid.
      Unshelve. all: tea; try irrValid.
  Qed.

  Lemma FundTmEqPiCong : forall (Γ : context) (A B C D : term),
    FundTm Γ U A ->
    FundTmEq Γ U A B ->
    FundTmEq (Γ,, A) U C D ->
    FundTmEq Γ U (tProd A C) (tProd B D).
  Proof.
    intros * [] [] [].
    assert (VA' : [Γ ||-v<one> A | VΓ]) by now eapply univValid.
    assert [Γ ||-v<one> A ≅ B | VΓ | VA'] by (eapply univEqValid; irrValid).
    opector; tea.
    - eapply UValid.
    - edestruct FundTmProd. 3: irrValid.
      all: unshelve econstructor; irrValid.
    - edestruct FundTmProd. 3: irrValid.
      1: unshelve econstructor; irrValid.
      unshelve econstructor.
      + eapply validSnoc; now eapply univValid.
      + eapply UValid.
      + eapply irrelevanceTmLift; irrValid.
    - unshelve epose (PiCongTm _ _ _ _ _ _ _ _ _ _ _).
      16: irrValid.
      2: tea.
      2,3,8: irrValid.
      all: try irrValid.
      + eapply univValid; irrValid.
      + eapply irrelevanceLift; irrValid.
      + eapply irrelevanceTmLift; irrValid.
      Unshelve.
      all: try irrValid.
  Qed.

  Lemma FundTmEqAppCong : forall (Γ : context) (a b f g A B : term),
    FundTmEq Γ (tProd A B) f g ->
    FundTmEq Γ A a b ->
    FundTmEq Γ B[a..] (tApp f a) (tApp g b).
  Proof.
    intros * [] []; econstructor.
    - eapply appValid; irrValid.
    - eapply conv. 2: eapply appValid; irrValid.
      eapply substSΠeq; try irrValid.
      1: eapply reflValidTy.
      now eapply symValidTmEq.
    - eapply appcongValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqLambdaCong : forall (Γ : context) (t u A A' A'' B : term),
    FundTy Γ A ->
    FundTyEq Γ A A' ->
    FundTyEq Γ A A'' ->
    FundTmEq (Γ,, A) B t u -> FundTmEq Γ (tProd A B) (tLambda A' t) (tLambda A'' u).
  Proof.
    intros * [VΓ] [? ? VA'] [? ? VA''] [].
    assert (VΠAB : [Γ ||-v< one > tProd A B | VΓ]).
    { unshelve eapply PiValid; irrValid. }
    assert (VB' : [Γ,, A' ||-v< one > B | validSnoc _ VA']).
    { eapply irrelevanceLift; [tea|]; irrValid. }
    assert (VB'' : [Γ,, A'' ||-v< one > B | validSnoc _ VA'']).
    { eapply irrelevanceLift; [tea|]; irrValid. }
    assert (Vλt : [Γ ||-v< one > tLambda A' t : tProd A B | VΓ | VΠAB ]).
    { eapply conv; [|eapply lamValid].
      + eapply symValidTyEq, PiCong; tea; try irrValid.
        eapply reflValidTy.
      + eapply irrelevanceTmLift; irrValid.
    }
    assert (Vλu : [Γ ||-v< one > tLambda A'' u : tProd A B | VΓ | VΠAB ]).
    { eapply conv; [|eapply lamValid].
      + eapply symValidTyEq, PiCong; tea; try irrValid.
        eapply reflValidTy.
      + eapply irrelevanceTmLift; irrValid.
    }
    Unshelve. all: try irrValid.
    assert [Γ,, A ||-v< one > A⟨@wk1 Γ A⟩ | validSnoc VΓ VA].
    { apply wk1ValidTy; irrValid. }
    assert (VΓAA' : [Γ,, A ||-v< one > A'⟨@wk1 Γ A⟩ | validSnoc VΓ VA]).
    { apply wk1ValidTy; irrValid. }
    assert (VΓAA'' : [Γ,, A ||-v< one > A''⟨@wk1 Γ A⟩ | validSnoc VΓ VA]).
    { apply wk1ValidTy; irrValid. }
    assert (VAdequate (ta := ta) (Γ,, A) VR).
    { now eapply validSnoc. }
    assert (VAdequate (ta := ta) (Γ,, A,, A'⟨@wk1 Γ A⟩) VR).
    { unshelve eapply validSnoc; tea; try irrValid. }
    assert (VAdequate (ta := ta) (Γ,, A,, A''⟨@wk1 Γ A⟩) VR).
    { unshelve eapply validSnoc; tea; try irrValid. }
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
        match goal with |- [_ ||-v< _ > ?t ≅ ?u : _ | _ | _ ] => assert (Hrw : t = u) end.
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
        match goal with |- [_ ||-v< _ > ?t ≅ ?u : _ | _ | _ ] => assert (Hrw : t = u) end.
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

  Lemma FundTmEqFunEta : forall (Γ : context) (f A B : term),
    FundTm Γ (tProd A B) f -> FundTmEq Γ (tProd A B) (tLambda A (tApp f⟨↑⟩ (tRel 0))) f.
  Proof.
  intros * [VΓ VΠ Vf].
  assert (eq0 : forall t, t⟨upRen_term_term ↑⟩[(tRel 0)..] = t).
  { clear; intros; bsimpl; apply idSubst_term; intros []; reflexivity. }
  assert (VA : [Γ ||-v< one > A | VΓ]).
  { now eapply PiValidDom. }
  assert (VΓA := validSnoc VΓ VA).
  assert (VΓAA : [Γ,, A ||-v< one > A⟨@wk1 Γ A⟩ | VΓA]).
  { now eapply irrelevanceTy, wk1ValidTy. }
  assert (VΓAA0 : VAdequate (ta := ta) (Γ,, A,, A⟨@wk1 Γ A⟩) VR).
  { now eapply validSnoc. }
  assert (VΓAA' : [Γ,, A ||-v< one > A⟨↑⟩ | VΓA]).
  { now rewrite wk1_ren_on in VΓAA. }
  assert [Γ,, A ||-v< one > B | VΓA].
  { eapply irrelevanceTy, PiValidCod. }
  assert ([Γ,, A ||-v< one > tProd A⟨@wk1 Γ A⟩ B⟨upRen_term_term ↑⟩ | VΓA]).
  { rewrite <- (wk_up_wk1_ren_on Γ A A).
    now eapply irrelevanceTy, (wk1ValidTy (A := tProd A B)). }
  assert ([Γ,, A ||-v< one > tRel 0 : A⟨wk1 A⟩ | VΓA | VΓAA]).
  { eapply irrelevanceTm'; [rewrite wk1_ren_on; reflexivity|].
    unshelve apply var0Valid'. }
  assert ([(Γ,, A),, A⟨wk1 A⟩ ||-v< one > tProd A⟨↑⟩⟨↑⟩ B⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩ | VΓAA0]).
  { assert (eq1 : (tProd A B)⟨@wk1 Γ A⟩⟨@wk1 (Γ,, A) A⟨@wk1 Γ A⟩⟩ = tProd (A⟨↑⟩⟨↑⟩) (B⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩)).
    { rewrite wk1_ren_on, wk1_ren_on; reflexivity. }
    eapply irrelevanceTy'; [|eapply eq1|reflexivity].
    now eapply wkValidTy, wkValidTy. }
  assert ([Γ ||-v< one > tLambda A (tApp f⟨↑⟩ (tRel 0)) : tProd A B | VΓ | VΠ]).
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
    match goal with |- [_ ||-v< _ > ?t ≅ ?u : _ | _ | _ ] => assert (Hrw : t = u) end.
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

  Lemma FundTmEqFunExt : forall (Γ : context) (f g A B : term),
    FundTy Γ A ->
    FundTm Γ (tProd A B) f ->
    FundTm Γ (tProd A B) g ->
    FundTmEq (Γ,, A) B (tApp (f⟨↑⟩) (tRel 0)) (tApp (g⟨↑⟩) (tRel 0)) ->
    FundTmEq Γ (tProd A B) f g.
  Proof.
    intros * [] [VΓ0 VA0] [] [].
    assert [Γ ||-v< one > g : tProd A B | VΓ0 | VA0].
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

  Lemma FundTmEqRefl : forall (Γ : context) (t A : term),
    FundTm Γ A t ->
    FundTmEq Γ A t t.
  Proof.
    intros * []; econstructor; tea; now eapply reflValidTm.
  Qed.

  Lemma FundTmEqSym : forall (Γ : context) (t t' A : term),
    FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t.
  Proof.
    intros * []; econstructor; tea; now eapply symValidTmEq.
  Qed.

  Lemma FundTmEqTrans : forall (Γ : context) (t t' t'' A : term),
    FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t'' ->
    FundTmEq Γ A t t''.
  Proof.
    intros * [] []; econstructor; tea.
    1: irrValid.
    eapply transValidTmEq; irrValid.
  Qed.

  Lemma FundTmEqConv : forall (Γ : context) (t t' A B : term),
    FundTmEq Γ A t t' ->
    FundTyEq Γ A B ->
    FundTmEq Γ B t t'.
  Proof.
    intros * [] []; econstructor.
    1,2: eapply conv; irrValid.
    eapply convEq; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyNat : forall Γ : context, FundCon Γ -> FundTy Γ tNat.
  Proof.
    intros ??; unshelve econstructor; tea;  eapply natValid.
  Qed.

  Lemma FundTmNat : forall Γ : context, FundCon Γ -> FundTm Γ U tNat.
  Proof.
    intros ??; unshelve econstructor; tea.
    2: eapply natTermValid.
  Qed.

  Lemma FundTmZero : forall Γ : context, FundCon Γ -> FundTm Γ tNat tZero.
  Proof.
    intros; unshelve econstructor; tea. 
    2:eapply zeroValid.
  Qed.

  Lemma FundTmSucc : forall (Γ : context) (n : term),
    FundTm Γ tNat n -> FundTm Γ tNat (tSucc n).
  Proof.
    intros * []; unshelve econstructor; tea.
    eapply irrelevanceTm; eapply succValid; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTmNatElim : forall (Γ : context) (P hz hs n : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTm Γ tNat n -> FundTm Γ P[n..] (tNatElim P hz hs n).
  Proof.
    intros * [] [] [] []; unshelve econstructor; tea.
    2: eapply natElimValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTyEmpty : forall Γ : context, FundCon Γ -> FundTy Γ tEmpty.
  Proof.
    intros ??; unshelve econstructor; tea;  eapply emptyValid.
  Qed.

  Lemma FundTmEmpty : forall Γ : context, FundCon Γ -> FundTm Γ U tEmpty.
  Proof.
    intros ??; unshelve econstructor; tea.
    2: eapply emptyTermValid.
  Qed.

  Lemma FundTmEmptyElim : forall (Γ : context) (P n : term),
    FundTy (Γ,, tEmpty) P ->
    FundTm Γ tEmpty n -> FundTm Γ P[n..] (tEmptyElim P n).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    2: eapply emptyElimValid; irrValid.
    Unshelve. 1,2: irrValid. 
  Qed.

  Lemma FundTmEqSuccCong : forall (Γ : context) (n n' : term),
    FundTmEq Γ tNat n n' -> FundTmEq Γ tNat (tSucc n) (tSucc n').
  Proof.
    intros * []; unshelve econstructor; tea.
    1,2: eapply irrelevanceTm; eapply succValid; irrValid.
    eapply irrelevanceTmEq; eapply succcongValid; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTmEqNatElimCong : forall (Γ : context)
      (P P' hz hz' hs hs' n n' : term),
    FundTyEq (Γ,, tNat) P P' ->
    FundTmEq Γ P[tZero..] hz hz' ->
    FundTmEq Γ (elimSuccHypTy P) hs hs' ->
    FundTmEq Γ tNat n n' ->
    FundTmEq Γ P[n..] (tNatElim P hz hs n) (tNatElim P' hz' hs' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0] [] [].
    pose (VN := natValid (l:=one) VΓ0).
    assert (VP' : [ _ ||-v<one> P' | validSnoc VΓ0 VN]) by irrValid. 
    assert [Γ ||-v< one > hz' : P'[tZero..] | VΓ0 | substS VP' (zeroValid VΓ0)]. 1:{
      eapply conv. 2: irrValid.
      eapply substSEq. 2,3: irrValid.
      1: eapply reflValidTy.
      2: eapply reflValidTm.
      all: eapply zeroValid.
    }
    assert [Γ ||-v< one > hs' : elimSuccHypTy P' | VΓ0 | elimSuccHypTyValid VΓ0 VP']. 1:{
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

  Lemma FundTmEqNatElimZero : forall (Γ : context) (P hz hs : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTmEq Γ P[tZero..] (tNatElim P hz hs tZero) hz.
  Proof.
    intros * [] [] []; unshelve econstructor; tea.
    3: irrValid.
    3: eapply natElimZeroValid; irrValid.
    eapply natElimValid; irrValid.
    Unshelve. irrValid.
  Qed.

  Lemma FundTmEqNatElimSucc : forall (Γ : context) (P hz hs n : term),
    FundTy (Γ,, tNat) P ->
    FundTm Γ P[tZero..] hz ->
    FundTm Γ (elimSuccHypTy P) hs ->
    FundTm Γ tNat n ->
    FundTmEq Γ P[(tSucc n)..] (tNatElim P hz hs (tSucc n))
      (tApp (tApp hs n) (tNatElim P hz hs n)).
  Proof.
    intros * [] [] [] []; unshelve econstructor; tea.
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

  Lemma FundTmEqEmptyElimCong : forall (Γ : context)
      (P P' n n' : term),
    FundTyEq (Γ,, tEmpty) P P' ->
    FundTmEq Γ tEmpty n n' ->
    FundTmEq Γ P[n..] (tEmptyElim P n) (tEmptyElim P' n').
  Proof.
    intros * [? VP0 VP0'] [VΓ0].
    pose (VN := emptyValid (l:=one) VΓ0).
    assert (VP' : [ _ ||-v<one> P' | validSnoc VΓ0 VN]) by irrValid.
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

  Lemma FundTySig : forall (Γ : context) (A B : term),
  FundTy Γ A -> FundTy (Γ,, A) B -> FundTy Γ (tSig A B).
  Proof.
    intros * [] []; unshelve econstructor; tea.
    unshelve eapply SigValid; tea; irrValid.
  Qed.

  Lemma FundTmSig : forall (Γ : context) (A B : term),
    FundTm Γ U A ->
    FundTm (Γ,, A) U B -> FundTm Γ U (tSig A B).
  Proof.
    intros * [] []; unshelve econstructor.
    3: unshelve eapply SigValidU.
    3-5: irrValid.
    1: tea.
    unshelve eapply univValid; tea.
  Qed.

  Lemma FundTmPair : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b -> FundTm Γ (tSig A B) (tPair A B a b).
  Proof.
    intros * [] [] [] []; unshelve econstructor.
    3: unshelve eapply pairValid; irrValid.
    tea.
  Qed.

  Lemma FundTmFst : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTm Γ A (tFst p).
  Proof.
    intros * []; unshelve econstructor.
    3: unshelve eapply fstValid.
    5: irrValid.
    2: now eapply domSigValid.
    now eapply codSigValid.
  Qed.

  Lemma FundTmSnd : forall (Γ : context) (A B p : term),
    FundTm Γ (tSig A B) p -> FundTm Γ B[(tFst p)..] (tSnd p).
  Proof.
    intros * []; unshelve econstructor.
    3: unshelve eapply sndValid.
    5: irrValid.
    2: now eapply domSigValid.
    now eapply codSigValid.
  Qed.

  Lemma FundTyEqSigCong : forall (Γ : context) (A B C D : term),
    FundTy Γ A ->
    FundTyEq Γ A B ->
    FundTyEq (Γ,, A) C D -> FundTyEq Γ (tSig A C) (tSig B D).
  Proof.
    intros * [] [] [].
    unshelve econstructor.
    4: eapply SigCong; tea; try irrValid.
    2: eapply irrelevanceLift; irrValid.
    eapply SigValid; eapply irrelevanceLift; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSigCong :forall (Γ : context) (A A' B B' : term),
    FundTm Γ U A ->
    FundTmEq Γ U A A' ->
    FundTmEq (Γ,, A) U B B' -> FundTmEq Γ U (tSig A B) (tSig A' B').
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

  Lemma FundTmEqSigEta : forall (Γ : context) (A B p q : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ (tSig A B) p ->
    FundTm Γ (tSig A B) q ->
    FundTmEq Γ A (tFst p) (tFst q) ->
    FundTmEq Γ B[(tFst p)..] (tSnd p) (tSnd q) -> FundTmEq Γ (tSig A B) p q.
  Proof.
    intros * [] [] [] [] [] []; unshelve econstructor.
    5: eapply sigEtaValid; tea; irrValid.
    all: irrValid.
    Unshelve. all: irrValid.
  Qed.


  Lemma FundTmEqFstCong : forall (Γ : context) (A B p p' : term),
    FundTmEq Γ (tSig A B) p p' -> FundTmEq Γ A (tFst p) (tFst p').
  Proof.
    intros * []; unshelve econstructor.
    5: eapply fstCongValid; irrValid.
    2: now eapply domSigValid.
    1,2: eapply fstValid; irrValid.
    Unshelve. all: now eapply codSigValid.
  Qed.

  Lemma FundTmEqFstBeta : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b -> FundTmEq Γ A (tFst (tPair A B a b)) a.
  Proof.
    intros * [] [] [] [].
    unshelve econstructor.
    3,5: eapply pairFstValid; irrValid.
    2,3: irrValid. 
    tea.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqSndCong : forall (Γ : context) (A B p p' : term),
    FundTmEq Γ (tSig A B) p p' -> FundTmEq Γ B[(tFst p)..] (tSnd p) (tSnd p').
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

  Lemma FundTmEqSndBeta : forall (Γ : context) (A B a b : term),
    FundTy Γ A ->
    FundTy (Γ,, A) B ->
    FundTm Γ A a ->
    FundTm Γ B[a..] b ->
    FundTmEq Γ B[(tFst (tPair A B a b))..] (tSnd (tPair A B a b)) b.
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

  Lemma FundTyId : forall (Γ : context) (A x y : term),
    FundTy Γ A -> FundTm Γ A x -> FundTm Γ A y -> FundTy Γ (tId A x y).
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    unshelve eapply IdValid; irrValid.
  Qed.


  Lemma FundTmId : forall (Γ : context) (A x y : term),
    FundTm Γ U A -> FundTm Γ A x -> FundTm Γ A y -> FundTm Γ U (tId A x y).
  Proof.
      intros * [] [] [].
      unshelve econstructor; tea.
      1: eapply UValid.
      unshelve eapply IdTmValid; cycle 1; try irrValid; tea.
  Qed.

  Lemma FundTmRefl : forall (Γ : context) (A x : term),
    FundTy Γ A -> FundTm Γ A x -> FundTm Γ (tId A x x) (tRefl A x).
  Proof.
    intros * [] []; unshelve econstructor.
    3: now eapply reflValid.
    now eapply IdValid.
  Qed.

  Lemma FundTmIdElim : forall (Γ : context) (A x P hr y e : term),
    FundTy Γ A ->
    FundTm Γ A x ->
    FundTy ((Γ,, A),, tId A⟨wk1 Γ A⟩ x⟨wk1 Γ A⟩ (tRel 0)) P ->
    FundTm Γ P[tRefl A x .: x..] hr ->
    FundTm Γ A y -> FundTm Γ (tId A x y) e -> FundTm Γ P[e .: y..] (tIdElim A x P hr y e).
  Proof.
    intros * [] [] [] [] [] []; unshelve econstructor.
    3: unshelve eapply IdElimValid; try irrValid.
    tea.
  Qed.

  Lemma FundTyEqId : forall (Γ : context) (A A' x x' y y' : term),
    FundTyEq Γ A A' ->
    FundTmEq Γ A x x' -> FundTmEq Γ A y y' -> FundTyEq Γ (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] [].
    unshelve econstructor; tea.
    3: eapply IdCongValid; irrValid.
    1,2: eapply IdValid; try irrValid.
    1,2: eapply conv; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqIdCong : forall (Γ : context) (A A' x x' y y' : term),
    FundTmEq Γ U A A' ->
    FundTmEq Γ A x x' -> FundTmEq Γ A y y' -> FundTmEq Γ U (tId A x y) (tId A' x' y').
  Proof.
    intros * [] [] []; unshelve econstructor.
    5: eapply IdTmCongValid; try irrValid; tea.
    2,3: eapply IdTmValid; try irrValid; tea.
    1: tea.
    1,2: eapply conv; try irrValid; eapply univEqValid; irrValid.
    Unshelve. all: first [eapply UValid| irrValid | tea].
  Qed.

  Lemma FundTmEqReflCong : forall (Γ : context) (A A' x x' : term),
    FundTyEq Γ A A' -> FundTmEq Γ A x x' -> FundTmEq Γ (tId A x x) (tRefl A x) (tRefl A' x').
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

  Lemma FundTmEqIdElimCong : forall (Γ : context) (A A' x x' P P' hr hr' y y' e e' : term),
    FundTy Γ A ->
    FundTm Γ A x ->
    FundTyEq Γ A A' ->
    FundTmEq Γ A x x' ->
    FundTyEq ((Γ,, A),, tId A⟨wk1 Γ A⟩ x⟨wk1 Γ A⟩ (tRel 0)) P P' ->
    FundTmEq Γ P[tRefl A x .: x..] hr hr' ->
    FundTmEq Γ A y y' ->
    FundTmEq Γ (tId A x y) e e' -> FundTmEq Γ P[e .: y..] (tIdElim A x P hr y e) (tIdElim A' x' P' hr' y' e').
  Proof.
    intros * [] [] [] [] [] [] [] [].
    assert [_ ||-v<one> x' : _ | _ | VB] by (eapply conv; irrValid).
    assert [_ ||-v<one> y' : _ | _ | VB] by (eapply conv; irrValid).
    assert (VId' : [_ ||-v<one> tId A' x' y' | VΓ]) by (eapply IdValid; irrValid).
    assert [_ ||-v<one> _ ≅ tId A' x' y' | _ | VA6] by (eapply IdCongValid; irrValid).
    assert [_ ||-v<one> e' : _ | _ | VId'] by (eapply conv; irrValid).
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
    1: eapply validSnoc; now eapply idElimMotiveCtxIdValid.
    eapply convCtx2'; tea.
    1: eapply convCtx1; tea; [eapply symValidTyEq; irrValid| ].
    1,3: now eapply idElimMotiveCtxIdValid.
    eapply idElimMotiveCtxIdCongValid; tea; irrValid.
    Unshelve.
    3: eapply idElimMotiveCtxIdValid. all: irrValid.
  Qed.

  Lemma FundTmEqIdElimRefl : forall (Γ : context) (A x P hr y A' z : term),
    FundTy Γ A ->
    FundTm Γ A x ->
    FundTy ((Γ,, A),, tId A⟨wk1 Γ A⟩ x⟨wk1 Γ A ⟩ (tRel 0)) P ->
    FundTm Γ P[tRefl A x .: x..] hr ->
    FundTm Γ A y ->
    FundTy Γ A' ->
    FundTm Γ A z ->
    FundTyEq Γ A A' ->
    FundTmEq Γ A x y ->
    FundTmEq Γ A x z -> FundTmEq Γ P[tRefl A' z .: y..] (tIdElim A x P hr y (tRefl A' z)) hr.
  Proof.
    intros * [] [] [] [] [] [] [] [] [] [].
    assert (VId : [_ ||-v<one> tId A x y | VΓ]) by (unshelve eapply IdValid; irrValid).
    assert [Γ ||-v< one > tRefl A' z : tId A x y | _ | VId].
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

Lemma Fundamental : (forall Γ : context, [ |-[ de ] Γ ] -> FundCon (ta := ta) Γ)
    × (forall (Γ : context) (A : term), [Γ |-[ de ] A] -> FundTy (ta := ta) Γ A)
    × (forall (Γ : context) (A t : term), [Γ |-[ de ] t : A] -> FundTm (ta := ta) Γ A t)
    × (forall (Γ : context) (A B : term), [Γ |-[ de ] A ≅ B] -> FundTyEq (ta := ta) Γ A B)
    × (forall (Γ : context) (A t u : term), [Γ |-[ de ] t ≅ u : A] -> FundTmEq (ta := ta) Γ A t u).
  Proof.
  apply WfDeclInduction.
  + intros; now apply FundConNil.
  + intros; now apply FundConCons.
  + intros; now apply FundTyU.
  + intros; now apply FundTyPi.
  + intros; now apply FundTyNat.
  + intros; now apply FundTyEmpty.
  + intros; now apply FundTySig.
  + intros; now apply FundTyId.
  + intros; now apply FundTyUniv.
  + intros; now apply FundTmVar.
  + intros; now apply FundTmProd.
  + intros; now apply FundTmLambda.
  + intros; now eapply FundTmApp.
  + intros; now apply FundTmNat.
  + intros; now apply FundTmZero.
  + intros; now apply FundTmSucc.
  + intros; now apply FundTmNatElim.
  + intros; now apply FundTmEmpty.
  + intros; now apply FundTmEmptyElim.
  + intros; now apply FundTmSig.
  + intros; now apply FundTmPair.
  + intros; now eapply FundTmFst.
  + intros; now eapply FundTmSnd.
  + intros; now eapply FundTmId.
  + intros; now eapply FundTmRefl.
  + intros; now eapply FundTmIdElim.
  + intros; now eapply FundTmConv.
  + intros; now apply FundTyEqPiCong.
  + intros; now apply FundTyEqSigCong.
  + intros; now eapply FundTyEqId.
  + intros; now apply FundTyEqRefl.
  + intros; now apply FundTyEqUniv.
  + intros; now apply FundTyEqSym.
  + intros; now eapply FundTyEqTrans.
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
  + intros; now apply FundTmEqSigCong.
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
  Qed.

(** ** Well-typed substitutions are also valid *)

  Corollary Fundamental_subst Γ Δ σ (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ : Δ] ->
    FundSubst Γ Δ wfΓ σ.
  Proof.
    intros HΔ.
    induction 1 as [|σ Δ A Hσ IH Hσ0].
    - exists validEmpty.
      now constructor.
    - inversion HΔ as [|?? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [?? Hσ0].
      cbn in *.
      eapply reducibleTm in Hσ0.
      eapply Fundamental in HA as [].
      unshelve econstructor.
      1: now eapply validSnoc.
      unshelve econstructor.
      + now eapply irrelevanceSubst.
      + cbn; irrelevance0.
        2: eassumption.
        reflexivity.
  Qed.

  Corollary Fundamental_subst_conv Γ Δ σ σ' (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ ≅ σ' : Δ] ->
    FundSubstConv Γ Δ wfΓ σ σ'.
  Proof.
    intros HΔ.
    induction 1 as [|σ τ Δ A Hσ IH Hσ0].
    - unshelve econstructor.
      1: eapply validEmpty.
      all: now econstructor.
    - inversion HΔ as [|?? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [?? Hσ0 Hτ0 Ηστ] ; cbn in *.
      eapply Fundamental in HA as [? HA].
      unshelve econstructor.
      + now eapply validSnoc.
      + unshelve econstructor.
        1: now irrValid.
        cbn.
        irrelevanceRefl.
        now eapply reducibleTm.
      + unshelve econstructor.
        1: now eapply irrelevanceSubst.
        cbn.
        unshelve irrelevanceRefl.
        2: now unshelve eapply HA ; tea ; irrValid.
        cbn.
        unshelve eapply LRTmRedConv.
        3: now eapply reducibleTy.
        * irrelevanceRefl.
          unshelve eapply HA ; tea.
          all: now irrValid.
        * irrelevanceRefl.
          now eapply reducibleTm.
      + unshelve econstructor ; cbn in *.
        * now irrValid.
        * irrelevanceRefl.
          now eapply reducibleTmEq.
  Qed.

End Fundamental.
