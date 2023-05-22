(** * LogRel.Fundamental: declarative typing implies the logical relation for any generic instance. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape.
From LogRel.Substitution.Introductions Require Import Application Universe Pi Lambda Var Nat Empty SimpleArr Sigma.

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
    - now eapply irrelevanceValidity.
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
    intros Γ n d FΓ hin; induction hin;
      destruct (invValiditySnoc FΓ) as [l [VΓ [VA _]]]; clear FΓ.
    - renToWk; rewrite <- (wk1_ren_on Γ d d).
      eexists _ _; unshelve eapply var0Valid; tea.
      now eapply embValidTyOne.
    - renToWk; rewrite <- (wk1_ren_on Γ d' d).
      destruct (IHhin VΓ); cbn in *.
      econstructor. set (ρ := wk1 _).
      replace (tRel _) with (tRel n)⟨ρ⟩ by (unfold ρ; now bsimpl).
      unshelve eapply wk1ValidTm; cycle 1; tea; now eapply irrelevanceValidity.
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
    now eapply symValidEq.
  Qed.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    FundTyEq Γ A B ->
    FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
    intros * [] []; unshelve econstructor; tea. 1:irrValid.
    eapply transValidEq; irrValid.
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
      eapply symValidEq. 
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
      eapply symValidEq.
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
      eapply irrelevanceEq.
      eapply substSEq.
      1,3: eapply reflValidTy.
      1: irrValid.
      2: eapply symValidTmEq.
      1,2: eapply pairFstValid; irrValid.
    Unshelve. all: irrValid.
  Qed.

  (* TODO: Fix all lemmas for list as it was done for https://github.com/CoqHott/logrel-coq/pull/30/files *)
  Lemma FundTyList : forall (Γ : context) (A : term), [Γ |-[ de ] A] -> FundTy Γ A -> FundTy Γ (tList A).
  Proof.
  Admitted.

  Lemma FundTmList : forall (Γ : context) (A : term),
  [Γ |-[ de ] A : U] -> FundTm Γ U A -> FundTm Γ U (tList A).
  Proof.
  Admitted.

  Lemma FundTmNil : forall (Γ : context) (A : term),
    [Γ |-[ de ] A] -> FundTy Γ A -> FundTm Γ (tList A) (tNil A).
  Proof.
  Admitted.

  Lemma FundTmCons : forall (Γ : context) (A a l : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] a : A] ->
    FundTm Γ A a ->
    [Γ |-[ de ] l : tList A] -> FundTm Γ (tList A) l -> FundTm Γ (tList A) (tCons A a l).
  Proof.
  Admitted.

  Lemma FundTmMap : forall (Γ : context) (A B f l : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] B] ->
    FundTy Γ B ->
    [Γ |-[ de ] f : arr A B] ->
    FundTm Γ (arr A B) f ->
    [Γ |-[ de ] l : tList A] -> FundTm Γ (tList A) l -> FundTm Γ (tList B) (tMap A B f l).
  Proof.
  Admitted.

  Lemma FundTyEqListCong : 
    forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTyEq Γ (tList A) (tList B).
  Proof.
  Admitted.

  Lemma FundTmEqListCong : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B -> FundTmEq Γ U (tList A) (tList B).
  Proof.
  Admitted.

  Lemma FundTmEqNilCong : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTmEq Γ (tList A) (tNil A) (tNil B).
  Proof.
  Admitted.

  Lemma FundTmEqConsCong :
    forall (Γ : context) (a b ax bx A B : term),
    [Γ |-[ de ] A ≅ B] ->
    FundTyEq Γ A B ->
    [Γ |-[ de ] a ≅ b : A] ->
    FundTmEq Γ A a b ->
    [Γ |-[ de ] ax ≅ bx : tList A] ->
    FundTmEq Γ (tList A) ax bx -> FundTmEq Γ (tList A) (tCons A a ax) (tCons B b bx).
  Proof.
  Admitted.

  Lemma FundTmEqMapCong : 
    forall (Γ : context) (f g ax bx A B C D : term),
    [Γ |-[ de ] A ≅ B] ->
    FundTyEq Γ A B ->
    [Γ |-[ de ] C ≅ D] ->
    FundTyEq Γ C D ->
    [Γ |-[ de ] f ≅ g : arr A C] ->
    FundTmEq Γ (arr A C) f g ->
    [Γ |-[ de ] ax ≅ bx : tList A] ->
    FundTmEq Γ (tList A) ax bx -> FundTmEq Γ (tList C) (tMap A C f ax) (tMap B D g bx).
  Proof.
  Admitted.

  Lemma FundTmEqMapNil :
    forall (Γ : context) (f A B : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] B] ->
    FundTy Γ B ->
    [Γ |-[ de ] f : arr A B] ->
    FundTm Γ (arr A B) f -> FundTmEq Γ (tList B) (tMap A B f (tNil A)) (tNil B).
  Proof.
  Admitted.

  Lemma FundTmEqMapCons :
    forall (Γ : context) (f hd tl A B : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] B] ->
    FundTy Γ B ->
    [Γ |-[ de ] f : arr A B] ->
    FundTm Γ (arr A B) f ->
    [Γ |-[ de ] hd : A] ->
    FundTm Γ A hd ->
    [Γ |-[ de ] tl : tList A] ->
    FundTm Γ (tList A) tl ->
    FundTmEq Γ (tList B) (tMap A B f (tCons A hd tl)) (tCons B (tApp f hd) (tMap A B f tl)).
  Proof.
  Admitted.

  Lemma FundTmEqMapComp :
    forall (Γ : context) (f g l l' A B C : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] B] ->
    FundTy Γ B ->
    [Γ |-[ de ] C] ->
    FundTy Γ C ->
    [Γ |-[ de ] f : arr B C] ->
    FundTm Γ (arr B C) f ->
    [Γ |-[ de ] g : arr A B] ->
    FundTm Γ (arr A B) g ->
    [Γ |-[ de ] l ≅ l' : tList A] ->
    FundTmEq Γ (tList A) l l' ->
    FundTmEq Γ (tList C) (tMap B C f (tMap A B g l)) (tMap A C (comp A f g) l').
  Proof.
  Admitted.

  Lemma FundTmEqMapId :
    forall (Γ : context) (l l' A : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] l ≅ l' : tList A] ->
    FundTmEq Γ (tList A) l l' -> FundTmEq Γ (tList A) (tMap A A (idterm A) l) l'.
  Proof.
  Admitted.


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
  + intros; now apply FundTyList.
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
  + intros; now eapply FundTmList.
  + intros; now eapply FundTmNil.
  + intros; now eapply FundTmCons.
  + intros; now eapply FundTmMap.
  + intros; now eapply FundTmConv.
  + intros; now apply FundTyEqPiCong.
  + intros; now apply FundTyEqSigCong.
  + intros; now apply FundTyEqListCong.
  + intros; now apply FundTyEqRefl.
  + intros; now apply FundTyEqUniv.
  + intros; now apply FundTyEqSym.
  + intros; now eapply FundTyEqTrans.
  + intros; now apply FundTmEqBRed.
  + intros; now apply FundTmEqPiCong.
  + intros; now eapply FundTmEqAppCong.
  + intros; now apply FundTmEqFunExt.
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
  + intros; now eapply FundTmEqListCong.
  + intros; now eapply FundTmEqNilCong.
  + intros; now eapply FundTmEqConsCong.
  + intros; now eapply FundTmEqMapCong.
  + intros; now eapply FundTmEqMapNil.
  + intros; now eapply FundTmEqMapCons.
  + intros; now eapply FundTmEqMapComp.
  + intros; now eapply FundTmEqMapId.
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
