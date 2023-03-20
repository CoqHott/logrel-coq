From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping DeclarativeInstance GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape.
From LogRel.Substitution.Introductions Require Import Application Universe Pi Lambda.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Primitive Projection Parameters.

(* FundCon, FundTy, ... are parameterized by a tag with a bunch of typing
  judgment predicates *)
Definition FundCon `{GenericTypingProperties}
  (Γ : context) : Type := [||-v Γ ].

Module FundTy.
  Record FundTy `{GenericTypingProperties} {Γ : context} {A : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ]
  }.

  Arguments FundTy {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
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
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
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
  Arguments FundTm {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
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
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).

Module FundSubst.
  Record FundSubst `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
  }.
  Arguments FundSubst {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
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
  Arguments FundSubstConv {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
End FundSubstConv.

Export FundSubstConv(FundSubstConv,Build_FundSubstConv).

Section Fundamental.
  (* Fundamental is parameterized by a tag that satisfies the generic typing
    properties *)
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

  Lemma FundConCons (Γ : context) (na : aname) (A : term)
  (wfΓ : [ |-[ de ] Γ]) (fΓ : FundCon Γ) (tA : [Γ |-[ de ] A]) (fA : FundTy Γ A) : FundCon (Γ,, vass na A).
  Proof.
    destruct fA as [ VΓ VA ].
    eapply validSnoc. exact VA.
  Qed.

  Lemma FundTyU (Γ : context) (tΓ : [ |-[ de ] Γ]) (fΓ : FundCon Γ) : FundTy Γ U.
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

  Lemma FundTyPi (Γ : context) (na : aname) (F G : term)
    (tF : [Γ |-[ de ] F]) (fF : FundTy Γ F)
    (tG : [Γ,, vass na F |-[ de ] G]) (fG : FundTy (Γ,, vass na F) G)
    : FundTy Γ (tProd na F G).
  Proof.
    destruct fF as [ VΓ VF ]. destruct fG as [ VΓF VG ].
    econstructor.
    unshelve eapply (PiValid VΓ).
    - assumption.
    - now eapply irrelevanceValidity.
  Qed.

  Lemma FundTyUniv (Γ : context) (A : term)
    (tA : [Γ |-[ de ] A : U]) (fA : FundTm Γ U A)
    : FundTy Γ A.
  Proof.
    destruct fA as [ VΓ VU [ RA RAext ] ]. econstructor.
    unshelve econstructor.
    - intros * vσ.
      eapply UnivEq. exact (RA _ _ wfΔ vσ).
    - intros * vσ' vσσ'.
      eapply UnivEqEq. exact (RAext _ _ _ wfΔ vσ vσ' vσσ').
  Qed.


  Ltac irrValid :=
    match goal with
    | [_ : _ |- [||-v _]] => idtac
    | [_ : _ |- [ _ ||-v _ : _ | _ | _]] => eapply irrelevanceSubst
    | [_ : _ |- [ _ ||-v _ ≅ _ : _ | _ | _ | _]] => eapply irrelevanceSubstEq
    | [_ : _ |- [_ ||-v<_> _ | _]] => eapply irrelevanceValidity
    | [_ : _ |- [_ ||-v<_> _ ≅ _ | _ | _]] => eapply irrelevanceEq
    | [_ : _ |- [_ ||-v<_> _ : _ | _ | _]] => eapply irrelevanceTm
    | [_ : _ |- [_ ||-v<_> _ ≅ _ : _ | _ | _]] => eapply irrelevanceTmEq
    end; eassumption.

  Lemma FundTmVar : forall (Γ : context) (n : nat) (decl : context_decl),
    [ |-[ de ] Γ] -> FundCon Γ ->
    in_ctx Γ n decl -> FundTm Γ (decl_type decl) (tRel n).
  Proof.
    intros Γ n d wfΓ FΓ hin; induction hin;
      destruct (invValiditySnoc FΓ) as [l [VΓ [VA _]]]; clear FΓ;
      destruct d as [nA A]; cbn.
    - renToWk; rewrite <- (wk1_ren_on Γ nA A A).
      exists (validSnoc nA VΓ VA) (embValidTyOne (wk1ValidTy nA VA VA)).
      constructor; intros; cbn.
      + epose (validHead Vσ); irrelevance.
      + epose (eqHead Vσσ'); irrelevance.
    - renToWk; rewrite <- (wk1_ren_on Γ d'.(decl_name) d'.(decl_type) A).
      destruct (IHhin (boundary_ctx_ctx wfΓ) VΓ); cbn in *.
      econstructor. set (ρ := wk1 _ _).
      replace (tRel _) with (tRel n)⟨ρ⟩ by (unfold ρ; now bsimpl).
      unshelve eapply wk1ValidTm; cycle 1; tea; now eapply irrelevanceValidity.
  Qed.

  Lemma FundTmProd : forall (Γ : context) (na : aname) (A B : term),
    [Γ |-[ de ] A : U] -> FundTm Γ U A ->
    [Γ,, vass na A |-[ de ] B : U] ->
    FundTm (Γ,, vass na A) U B -> FundTm Γ U (tProd na A B).
  Proof.
    intros * ? [] ? []; econstructor.
    eapply PiValidU; irrValid.
    Unshelve. 
    3: eapply UValid. 
    2: eapply univValid. 
    all:tea.
  Qed.

  Lemma FundTmLambda : forall (Γ : context) (na : aname) (A B t : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ,, vass na A |-[ de ] t : B] ->
    FundTm (Γ,, vass na A) B t -> FundTm Γ (tProd na A B) (tLambda na A t).
  Proof.
    intros * ?[]?[]; econstructor.
    eapply lamValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmApp : forall (Γ : context) (na : aname) (f a A B : term),
    [Γ |-[ de ] f : tProd na A B] ->
    FundTm Γ (tProd na A B) f ->
    [Γ |-[ de ] a : A] -> FundTm Γ A a -> FundTm Γ B[a..] (tApp f a).
  Proof.
    intros * ?[]?[]; econstructor.
    now eapply appValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmConv : forall (Γ : context) (t A B : term),
    [Γ |-[ de ] t : A] -> FundTm Γ A t ->
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTm Γ B t.
  Proof.
    intros * ?[]?[]; econstructor. 
    eapply conv; irrValid.
    Unshelve. all: tea.
  Qed.

  Lemma FundTyEqPiCong : forall (Γ : context) (na nb : aname) (A B C D : term),
    [Γ |-[ de ] A ] ->
    FundTy Γ A ->
    [Γ |-[ de ] A ≅ B] ->
    FundTyEq Γ A B ->
    [Γ,, vass na A |-[ de ] C ≅ D] ->
    FundTyEq (Γ,, vass na A) C D -> FundTyEq Γ (tProd na A C) (tProd nb B D).
  Proof.
    intros * ?[]?[]?[]; econstructor.
    - eapply PiValid. eapply irrelevanceLift; tea; irrValid.
    - eapply PiCong. 1: eapply irrelevanceLift; tea.
      all: irrValid.
    Unshelve. all: tea; irrValid.
  Qed.

  Lemma FundTyEqRefl : forall (Γ : context) (A : term),
    [Γ |-[ de ] A] -> FundTy Γ A -> FundTyEq Γ A A.
  Proof.
    intros * ?[]; unshelve econstructor; tea; now eapply reflValidTy.
  Qed.

  Lemma FundTyEqSym : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTyEq Γ B A.
  Proof.
    intros * ? [];  unshelve econstructor; tea.
    now eapply symValidEq.
  Qed.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B ->
    [Γ |-[ de ] B ≅ C] -> FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
    intros * ?[]?[]; unshelve econstructor; tea. 1:irrValid.
    eapply transValidEq; irrValid.
    Unshelve. tea.
  Qed.

  Lemma FundTyEqUniv : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B -> FundTyEq Γ A B.
  Proof.
    intros * ?[]; unshelve econstructor; tea.
    1,2: now eapply univValid.
    now eapply univEqValid.
  Qed.

  Lemma FundTmEqBRed : forall (Γ : context) (na : aname) (a t A B : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ,, vass na A |-[ de ] t : B] ->
    FundTm (Γ,, vass na A) B t ->
    [Γ |-[ de ] a : A] ->
    FundTm Γ A a -> FundTmEq Γ B[a..] (tApp (tLambda na A t) a) t[a..].
  Proof.
    intros * ?[]?[]?[]; econstructor.
    - eapply appValid. eapply lamValid. irrValid.
    - unshelve epose (substSTm _ _ _).
      7,9-13: irrValid.
    - unshelve epose (betaValid VA _ _ _). 3,6,7,8:irrValid.
      Unshelve. all: tea; try irrValid.
  Qed.

  Lemma FundTmEqPiCong : forall (Γ : context) (na nb : aname) (A B C D : term),
    [Γ |-[ de ] A : U] -> FundTm Γ U A ->
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B ->
    [Γ,, vass na A |-[ de ] C ≅ D : U] -> FundTmEq (Γ,, vass na A) U C D ->
    FundTmEq Γ U (tProd na A C) (tProd nb B D).
  Proof.
    intros * ?[]?[]?[].
    assert (VA' : [Γ ||-v<one> A | VΓ]) by now eapply univValid.
    assert [Γ ||-v<one> A ≅ B | VΓ | VA'] by (eapply univEqValid; irrValid).
    opector; tea.
    - edestruct FundTmProd. 5: irrValid.
      1,3: eapply ty_sound; now eapply escapeTm.
      all: unshelve econstructor; irrValid.
    - edestruct FundTmProd. 5: irrValid.
      1,3: eapply ty_sound; eapply escapeTm; tea.
      1: eapply irrelevanceTmLift; tea; irrValid.
      1: unshelve econstructor; irrValid.
      opector.
      + eapply validSnoc; now eapply univValid.
      + eapply irrelevanceLift; irrValid.
      + eapply irrelevanceTmLift; irrValid.
    - unshelve epose (PiCongTm _ _ _ _ _ _ _ _ _ _ _).
      19: irrValid.
      1: tea.
      1-4,7,9,10: irrValid.
      + now eapply univValid.
      + eapply irrelevanceLift; irrValid.
      + eapply irrelevanceTmLift; irrValid.
      Unshelve.
      all: try irrValid.
      1: unshelve eapply irrelevanceLift; cycle 3; try irrValid.
      unshelve eapply univValid; cycle 1; try irrValid.
  Qed.

  Lemma FundTmEqAppCong : forall (Γ : context) (na : aname) (a b f g A B : term),
    [Γ |-[ de ] f ≅ g : tProd na A B] -> FundTmEq Γ (tProd na A B) f g ->
    [Γ |-[ de ] a ≅ b : A] -> FundTmEq Γ A a b ->
    FundTmEq Γ B[a..] (tApp f a) (tApp g b).
  Proof.
    intros * ?[]?[]; econstructor.
    - eapply appValid; irrValid.
    - eapply conv. 2: eapply appValid; irrValid.
      eapply substSΠeq; try irrValid.
      1: eapply reflValidTy.
      now eapply symValidTmEq.
    - eapply appcongValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  Lemma FundTmEqFunExt : forall (Γ : context) (na nb : aname) (f g A B : term),
    [Γ |-[ de ] A] -> FundTy Γ A ->
    [Γ |-[ de ] f : tProd na A B] -> FundTm Γ (tProd na A B) f ->
    [Γ |-[ de ] g : tProd nb A B] -> FundTm Γ (tProd nb A B) g ->
    [Γ,, vass na A |-[ de ] tApp (f⟨↑⟩) (tRel 0) ≅ tApp (g⟨↑⟩) (tRel 0) : B] -> FundTmEq (Γ,, vass na A) B (tApp (f⟨↑⟩) (tRel 0)) (tApp (g⟨↑⟩) (tRel 0)) ->
    FundTmEq Γ (tProd na A B) f g.
  Proof.
    intros * ?[]?[VΓ0 VA0]?[]?[].
    assert [Γ ||-v< one > g : tProd na A B | VΓ0 | VA0].
    1:{
      eapply conv. 
      2: irrValid.
      eapply symValidEq. eapply PiCong.
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
    [Γ |-[ de ] t : A] -> FundTm Γ A t ->
    FundTmEq Γ A t t.
  Proof.
    intros * ?[]; econstructor; tea; now eapply reflValidTm.
  Qed.

  Lemma FundTmEqSym : forall (Γ : context) (t t' A : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t.
  Proof.
    intros * ?[]; econstructor; tea; now eapply symValidTmEq.
  Qed.

  Lemma FundTmEqTrans : forall (Γ : context) (t t' t'' A : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    [Γ |-[ de ] t' ≅ t'' : A] -> FundTmEq Γ A t' t'' ->
    FundTmEq Γ A t t''.
  Proof.
    intros * ?[]?[]; econstructor; tea.
    1: irrValid.
    eapply transValidTmEq; irrValid.
  Qed.

  Lemma FundTmEqConv : forall (Γ : context) (t t' A B : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B ->
    FundTmEq Γ B t t'.
  Proof.
    intros * ?[]?[]; econstructor.
    1,2: eapply conv; irrValid.
    eapply convEq; irrValid.
    Unshelve. all: irrValid.
  Qed.

Lemma Fundamental : (forall Γ : context, [ |-[ de ] Γ ] -> FundCon (ta := ta) Γ)
    × (forall (Γ : context) (A : term), [Γ |-[ de ] A] -> FundTy (ta := ta) Γ A)
    × (forall (Γ : context) (A t : term), [Γ |-[ de ] t : A] -> FundTm (ta := ta) Γ A t)
    × (forall (Γ : context) (A B : term), [Γ |-[ de ] A ≅ B] -> FundTyEq (ta := ta) Γ A B)
    × (forall (Γ : context) (A t u : term), [Γ |-[ de ] t ≅ u : A] -> FundTmEq (ta := ta) Γ A t u).
  Proof.
  apply WfDeclInduction.
  + apply FundConNil.
  + apply FundConCons.
  + apply FundTyU.
  + apply FundTyPi.
  + apply FundTyUniv.
  + apply FundTmVar.
  + apply FundTmProd.
  + apply FundTmLambda.
  + apply FundTmApp.
  + apply FundTmConv.
  + apply FundTyEqPiCong.
  + apply FundTyEqRefl.
  + apply FundTyEqUniv.
  + apply FundTyEqSym.
  + apply FundTyEqTrans.
  + apply FundTmEqBRed.
  + apply FundTmEqPiCong.
  + apply FundTmEqAppCong.
  + apply FundTmEqFunExt.
  + apply FundTmEqRefl.
  + apply FundTmEqConv.
  + apply FundTmEqSym.
  + apply FundTmEqTrans.
  Qed.

  Corollary wf_ctx_complete Γ :
    [|-[de] Γ] -> [|-[ta] Γ].
  Proof.
    induction 1 as [| ???? IH HA] ; refold.
    - apply wfc_nil.
    - apply wfc_cons ; tea.
      apply Fundamental in HA as [? [HA _]].
      pose proof (soundCtxId VΓ) as [? Hsubst].
      specialize (HA _ _ _ Hsubst).
      rewrite instId'_term in HA ; tea.
      now eapply escape_ in HA.
  Qed.

  Corollary Fundamental_subst Γ Δ σ (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ : Δ] ->
    FundSubst Γ Δ wfΓ σ.
  Proof.
    intros HΔ.
    induction 1 as [|σ Δ na A Hσ IH Hσ0].
    - exists validEmpty.
      now constructor.
    - inversion HΔ as [|??? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [redΓ [redA'] [redσ0]].
      cbn in *.
      clear validTyExt validTmExt.
      specialize (redσ0 _ _ _ (projT2 (soundCtxId redΓ))).
      set (redA'' := (redA' _ _ _ (projT2 (soundCtxId redΓ)))) in *.
      clearbody redA''.
      clear redA'.
      repeat rewrite instId'_term in *.
      eapply Fundamental in HA as [VΔ' VA].
      unshelve econstructor.
      1: now eapply validSnoc.
      unshelve econstructor.
      + now eapply irrelevanceSubst.
      + cbn; irrelevance0.
        2: now eapply redσ0.
        now rewrite instId'_term.
  Qed.

  Corollary Fundamental_subst_conv Γ Δ σ σ' (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ ≅ σ' : Δ] ->
    FundSubstConv Γ Δ wfΓ σ σ'.
  Proof.
    intros HΔ.
    induction 1 as [|σ τ Δ na A Hσ IH Hσ0].
    - unshelve econstructor.
      1: eapply validEmpty.
      all: now econstructor.
    - inversion HΔ as [|??? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [redΓ [redA'] [redσ0] [redτ0] [redστ0]] ; cbn in *.
      clear validTyExt validTmExt validTmExt0.
      specialize (redσ0 _ _ _ (projT2 (soundCtxId redΓ))).
      specialize (redτ0 _ _ _ (projT2 (soundCtxId redΓ))).
      specialize (redστ0 _ _ _ (projT2 (soundCtxId redΓ))).
      set (redA'' := (redA' _ _ _ (projT2 (soundCtxId redΓ)))) in *.
      clearbody redA''.
      clear redA'.
      repeat rewrite instId'_term in *.
      eapply Fundamental in HA as [VΔ' VA].
      unshelve econstructor.
      1: now eapply validSnoc.
      + unshelve econstructor.
        * now eapply irrelevanceSubst.
        * cbn; irrelevance0.
          2: now eapply redσ0.
          now rewrite instId'_term.
      + unshelve econstructor.
        * now eapply irrelevanceSubst.
        * cbn.
          eapply RedTmConv.
          4: now eapply redτ0.
          -- now unshelve eapply redA''.
          -- now eapply validTy.
          -- unshelve eapply LRTyEqIrrelevant'.
             4: rewrite instId'_term ; reflexivity.
             2,3: unshelve eapply VA ; tea.
             1-2: now eapply irrelevanceSubst.
             now eapply irrelevanceSubstEq.
      + unshelve econstructor ; cbn in *.
        * now eapply irrelevanceSubstEq.
        * eapply LRTmEqIrrelevant' ; tea.
          now bsimpl.
  Qed.

End Fundamental.
