From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening 
  DeclarativeTyping GenericTyping LogicalRelation
  Validity.

Set Primitive Projections.
Set Universe Polymorphism.

(* FundCon, FundTy, ... are parameterized by a tag with a bunch of typing 
  judgment predicates *)
Definition FundCon `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta} `{RedType ta} `{RedTerm ta}
  (Γ : context) : Type := [||-v Γ ].

Module FundTy.
  Record FundTy `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
    `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta} `{RedType ta} `{RedTerm ta}
    {Γ : context} {A : term} 
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ]
  }.
  
  Arguments FundTy {_ _ _ _ _ _ _ _ _}.
End FundTy. 

Export FundTy(FundTy,Build_FundTy).

Module FundTyEq.
  Record FundTyEq `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
    `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta} `{RedType ta} `{RedTerm ta}
    {Γ : context} {A B : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    VB : [ Γ ||-v< one > B | VΓ ];
    VAB : [ Γ ||-v< one > A ≅ B | VΓ | VA ]
  }.
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _}.  
End FundTyEq.

Export FundTyEq(FundTyEq,Build_FundTyEq).

Module FundTm.
  Record FundTm `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
    `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta} `{RedType ta} `{RedTerm ta}
    {Γ : context} {A t : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ];
  }.
  Arguments FundTm {_ _ _ _ _ _ _ _ _}.  
End FundTm.

Export FundTm(FundTm,Build_FundTm).

Module FundTmEq.
  Record FundTmEq `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
    `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta} `{RedType ta} `{RedTerm ta}
    {Γ : context} {A t u : term}
  : Type := {
    VΓ : [||-v Γ ];
    VA : [ Γ ||-v< one > A | VΓ ];
    Vt : [ Γ ||-v< one > t : A | VΓ | VA ];
    Vu : [ Γ ||-v< one > u : A | VΓ | VA ];
    Vtu : [ Γ ||-v< one > t ≅ u : A | VΓ | VA ];
  }.
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _}.  
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).

Section Fundamental.
  (* Fundamental is parameterized by a tag that satisfies the generic typing 
    properties *)
  Context `{GenericTypingProperties}.
  (* On top of this, we need to use the predicates for declarative typing,
    since we will reason by induction on them *)
  Import DeclarativeTypingData.

  Lemma Fundamental : (forall Γ : context, [ |-[ de ] Γ ] -> FundCon (ta := ta) Γ)
    × (forall (Γ : context) (A : term), [Γ |-[ de ] A] -> FundTy (ta := ta) Γ A)
    × (forall (Γ : context) (A t : term), [Γ |-[ de ] t : A] -> FundTm (ta := ta) Γ A t)
    × (forall (Γ : context) (A B : term), [Γ |-[ de ] A ≅ B] -> FundTyEq (ta := ta) Γ A B)
    × (forall (Γ : context) (A t u : term), [Γ |-[ de ] t ≅ u : A] -> FundTmEq (ta := ta) Γ A t u).
  Proof.
    apply WfDeclInduction.
    (*...*)
  Abort.
  
End Fundamental.