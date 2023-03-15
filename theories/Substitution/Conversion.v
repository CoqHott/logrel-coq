From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.

Set Universe Polymorphism.

Section Conversion.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma conv {Γ t A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Γ ||-v<l> t : B | VΓ | VB].
Proof.
  constructor; intros; [eapply LRTmRedConv| eapply LRTmEqRedConv].
  1,3: now unshelve now eapply validTyEq.
  1: now eapply validTm.
  now eapply validTmExt.
Qed.

Lemma convsym {Γ t A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t : B | VΓ | VB]) :
  [Γ ||-v<l> t : A | VΓ | VA].
Proof.
  constructor; intros; [eapply LRTmRedConv| eapply LRTmEqRedConv].
  1,3: unshelve eapply LRTyEqSym; tea; [|now unshelve now eapply validTyEq].
  1:  now unshelve now eapply validTm.
  now eapply validTmExt.
Qed.

Lemma convEq {Γ t u A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : B | VΓ | VB].
Proof.
  constructor; intros; eapply LRTmEqRedConv.
  1: now unshelve now eapply validTyEq.
  now eapply validTmEq.
Qed.

End Conversion.
