From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.

Set Universe Polymorphism.

Section Application.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma appValid {Γ nF F G t u l}
  (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΠFG : [Γ ||-v<l> tProd nF F G | VΓ])
  (Vt : [Γ ||-v<l> t : tProd nF F G | VΓ | VΠFG])
  (Vu : [Γ ||-v<l> u : F | VΓ | VF]) 
  (VGu := substSΠ VΠFG Vu) :
  [Γ ||-v<l> tApp t u : G[u..] | VΓ | VGu].
Proof. 
  opector; intros.
  - instValid wfΔ Vσ.
    epose (appTerm RVΠFG RVt RVu (substSΠaux VΠFG Vu _ _ wfΔ Vσ)); refold.
    irrelevance. 
  - instValid wfΔ Vσ; instValid wfΔ Vσ'; instValidExt Vσ' Vσσ'.
    unshelve epose (appcongTerm _ REVt RVu _ REVu (substSΠaux VΠFG Vu _ _ wfΔ Vσ)).
    2: irrelevance.
    eapply LRTmRedConv; tea.
    unshelve eapply LRTyEqSym. 2,3: tea.
Qed.

End Application.