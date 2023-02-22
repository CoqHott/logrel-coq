From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening 
  DeclarativeTyping GenericTyping LogicalRelation
  Validity.

Set Primitive Projections.
Set Universe Polymorphism.

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

Section Fundamental.
  (* Fundamental is parameterized by a tag that satisfies the generic typing 
    properties *)
  Context `{GenericTypingProperties}.
  (* On top of this, we need to use the predicates for declarative typing,
    since we will reason by induction on them *)
  Import DeclarativeTypingData.

  Lemma FundConNil : FundCon ε.
  Proof.
  unshelve econstructor.
  + unshelve econstructor.
    - intros; exact unit.
    - intros; exact unit.
  + constructor.
  Qed.

  Lemma FundConCons : forall (Γ : context) (na : aname) (A : term),
  [ |-[ de ] Γ] -> FundCon Γ -> [Γ |-[ de ] A] -> FundTy Γ A -> FundCon (Γ,, vass na A).
  Proof.
  Admitted.

  Lemma FundTyU : forall (Γ : context),
    [ |-[ de ] Γ] -> FundCon Γ -> FundTy Γ U.
  Proof.
  Admitted.

  Lemma FundTyPi : forall (Γ : context) (na : aname) (A B : term),
    [Γ |-[ de ] A] -> FundTy Γ A ->
    [Γ,, vass na A |-[ de ] B] -> FundTy (Γ,, vass na A) B ->
    FundTy Γ (tProd na A B).
  Proof.
  Admitted.

  Lemma FundTyUniv : forall (Γ : context) (A : term),
    [Γ |-[ de ] A : U] -> FundTm Γ U A -> FundTy Γ A.
  Proof.
  Admitted.

  Lemma FundTmVar : forall (Γ : context) (n : nat) (decl : context_decl),
    [ |-[ de ] Γ] -> FundCon Γ ->
    in_ctx Γ n decl -> FundTm Γ (decl_type decl) (tRel n).
  Proof.
  Admitted.

  Lemma FundTmProd : forall (Γ : context) (na : aname) (A B : term),
    [Γ |-[ de ] A : U] -> FundTm Γ U A ->
    [Γ,, vass na A |-[ de ] B : U] ->
    FundTm (Γ,, vass na A) U B -> FundTm Γ U (tProd na A B).
  Proof.
  Admitted.

  Lemma FundTmLambda : forall (Γ : context) (na : aname) (A B t : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ,, vass na A |-[ de ] t : B] ->
    FundTm (Γ,, vass na A) B t -> FundTm Γ (tProd na A B) (tLambda na A t).
  Proof.
  Admitted.

  Lemma FundTmApp : forall (Γ : context) (na : aname) (f a A B : term),
    [Γ |-[ de ] f : tProd na A B] ->
    FundTm Γ (tProd na A B) f ->
    [Γ |-[ de ] a : A] -> FundTm Γ A a -> FundTm Γ B[a..] (tApp f a).
  Proof.
  Admitted.

  Lemma FundTmConv : forall (Γ : context) (t A B : term),
    [Γ |-[ de ] t : A] -> FundTm Γ A t ->
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTm Γ B t.
  Proof.
  Admitted.

  Lemma FundTyEqPiCong : forall (Γ : context) (na nb : aname) (A B C D : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] A ≅ B] ->
    FundTyEq Γ A B ->
    [Γ,, vass na A |-[ de ] C ≅ D] ->
    FundTyEq (Γ,, vass na A) C D -> FundTyEq Γ (tProd na A C) (tProd nb B D).
  Proof.
  Admitted.

  Lemma FundTyEqRefl : forall (Γ : context) (A : term),
    [Γ |-[ de ] A] -> FundTy Γ A -> FundTyEq Γ A A.
  Proof.
  Admitted.

  Lemma FundTyEqSym : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTyEq Γ B A.
  Proof.
  Admitted.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B ->
    [Γ |-[ de ] B ≅ C] -> FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
  Admitted.

  Lemma FundTyEqUniv : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B -> FundTyEq Γ A B.
  Proof.
  Admitted.

  Lemma FundTmEqBRed : forall (Γ : context) (na : aname) (a t A B : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ,, vass na A |-[ de ] t : B] ->
    FundTm (Γ,, vass na A) B t ->
    [Γ |-[ de ] a : A] ->
    FundTm Γ A a -> FundTmEq Γ B[a..] (tApp (tLambda na A t) a) t[a..].
  Proof.
  Admitted.

  Lemma FundTmEqPiCong : forall (Γ : context) (na nb : aname) (A B C D : term),
    [Γ |-[ de ] A] -> FundTy Γ A ->
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B ->
    [Γ,, vass na A |-[ de ] C ≅ D : U] -> FundTmEq (Γ,, vass na A) U C D ->
    FundTmEq Γ U (tProd na A C) (tProd nb B D).
  Proof.
  Admitted.

  Lemma FundTmEqAppCong : forall (Γ : context) (na : aname) (a b f g A B : term),
    [Γ |-[ de ] f ≅ g : tProd na A B] -> FundTmEq Γ (tProd na A B) f g ->
    [Γ |-[ de ] a ≅ b : A] -> FundTmEq Γ A a b ->
    FundTmEq Γ B[a..] (tApp f a) (tApp g b).
  Proof.
  Admitted.

  Lemma FundTmEqFunExt : forall (Γ : context) (na nb : aname) (f g A B : term),
    [Γ |-[ de ] A] -> FundTy Γ A ->
    [Γ |-[ de ] f : tProd na A B] -> FundTm Γ (tProd na A B) f ->
    [Γ |-[ de ] g : tProd nb A B] -> FundTm Γ (tProd nb A B) g ->
    [Γ,, vass na A |-[ de ] tApp (f⟨↑⟩) (tRel 0) ≅ tApp (g⟨↑⟩) (tRel 0) : B] -> FundTmEq (Γ,, vass na A) B (tApp (f⟨↑⟩) (tRel 0)) (tApp (g⟨↑⟩) (tRel 0)) ->
    FundTmEq Γ (tProd na A B) f g.
  Proof.
  Admitted.

  Lemma FundTmEqRefl : forall (Γ : context) (t A : term),
    [Γ |-[ de ] t : A] -> FundTm Γ A t ->
    FundTmEq Γ A t t.
  Proof.
  Admitted.

  Lemma FundTmEqSym : forall (Γ : context) (t t' A : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t.
  Proof.
  Admitted.

  Lemma FundTmEqTrans : forall (Γ : context) (t t' t'' A : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    [Γ |-[ de ] t' ≅ t'' : A] -> FundTmEq Γ A t' t'' ->
    FundTmEq Γ A t t''.
  Proof.
  Admitted.

  Lemma FundTmEqConv : forall (Γ : context) (t t' A B : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B ->
    FundTmEq Γ B t t'.
  Proof.
  Admitted.

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

End Fundamental.
