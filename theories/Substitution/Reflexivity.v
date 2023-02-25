
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.

Set Universe Polymorphism.

Section Reflexivity.
Context `{GenericTypingProperties}.

Lemma reflValidTy {Γ A l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ]) :
  [Γ ||-v<l> A ≅ A | VΓ | VA].
Proof.
  constructor; intros; apply LRTyEqRefl_.
Qed.

Lemma reflValidTm {Γ t A l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ t : A | VΓ | VA].
Proof.
  constructor; intros; apply LREqTermRefl_; now eapply validTm.
Qed.

End Reflexivity.