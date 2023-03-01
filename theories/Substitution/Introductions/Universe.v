From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Universe.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity.

Set Universe Polymorphism.

Section Universe.
Context `{GenericTypingProperties} {Γ : context}.

Lemma UValid (VΓ : [||-v Γ]) : [Γ ||-v<one> U | VΓ].
Proof.
  unshelve econstructor; intros.
  - eapply LRU_; econstructor; tea; [constructor|].
    cbn; eapply redtywf_refl; gen_typing.
  - cbn; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma univValid {A l l'} (VΓ : [||-v Γ])
  (VU : [Γ ||-v<l> U | VΓ])
  (VA : [Γ ||-v<l> A : U | VΓ | VU]) :
  [Γ ||-v<l'> A| VΓ].
Proof.
  unshelve econstructor; intros.
  - instValid wfΔ vσ. now eapply UnivEq.
  - instValid wfΔ vσ; instValid wfΔ vσ' ; instValidExt vσ' vσσ'.
    now eapply UnivEqEq.
Qed.

Lemma univEqValid {A B l l'} (VΓ : [||-v Γ])
  (VU : [Γ ||-v<l'> U | VΓ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VAB : [Γ ||-v<l'> A ≅ B : U | VΓ | VU]) :
  [Γ ||-v<l> A ≅ B | VΓ | VA].
Proof.
  constructor; intros; instValid wfΔ Vσ.
  now eapply UnivEqEq.
Qed.

End Universe.