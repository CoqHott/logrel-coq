From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Untyped Weakening GenericTyping LogicalRelation Reduction.
From LogRel.LogicalRelation Require Import Irrelevance Induction.

Set Universe Polymorphism.

Section Universe.
  Context `{GenericTypingProperties}.

  Lemma univTmTy' {Γ l A} (h : [Γ ||-U l]) :
    [Γ ||-<l> A : U | LRU_ h] -> [Γ ||-<URedTy.level h> A].
  Proof.  intros []; now eapply RedTyRecFwd. Qed.

  Lemma univTmTy {Γ l A} (RU : [Γ ||-<l> U]) :
    [Γ ||-<l> A : U | RU] -> [Γ ||-<URedTy.level (invLRU RU)> A].
  Proof. 
    intros h; apply univTmTy'.
    irrelevance.
  Qed.

  Lemma univEqTmEqTy' {Γ l l' A B} (h : [Γ ||-U l]) (RA : [Γ ||-<l'> A]) :
    [Γ ||-<l> A ≅ B : U | LRU_ h] -> [Γ ||-<l'> A ≅ B | RA].
  Proof. intros [????? RA']. apply TyEqRecFwd in RA'. irrelevance. Qed.

  Lemma univEqTmEqTy {Γ l l' A B} (RU : [Γ ||-<l> U]) (RA : [Γ ||-<l'> A]) :
    [Γ ||-<l> A ≅ B : U | RU] -> [Γ ||-<l'> A ≅ B | RA].
  Proof. intros h; eapply (univEqTmEqTy' (invLRU RU)); irrelevance. Qed.

End Universe.

    