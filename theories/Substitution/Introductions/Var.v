(** * LogRel.Introductions.Var : Validity of variables. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Var.
  Context `{GenericTypingProperties}.
  
  Lemma var0Valid {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | validSnoc VΓ VA | wk1ValidTy _ VA ].
  Proof.
    constructor; intros; cbn.
    + epose (validHead Vσ); irrelevance.
    + epose (eqHead Vσσ'); irrelevance.
  Qed.
  
End Var.