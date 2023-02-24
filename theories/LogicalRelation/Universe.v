From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Untyped Weakening GenericTyping LogicalRelation Reduction.
From LogRel.LogicalRelation Require Import Irrelevance Induction.

Set Universe Polymorphism.

Section Universe.
  Context `{GenericTypingProperties}.

  Set Printing Universes.
  Lemma univTmTy'@{h i j k l} {Γ l A} (h : [Γ ||-U l]) :
    [LogRel@{i j k l} l | Γ ||- A : U | LRU_ h] -> [LogRel@{h i j k} (URedTy.level h) | Γ ||- A].
  Proof.  intros []; now eapply RedTyRecFwd. Qed.

  Lemma univTmTy@{h i j k l} {Γ l A} (RU : [Γ ||-<l> U]) :
    [LogRel@{i j k l} l | Γ ||- A : U | RU] -> [LogRel@{h i j k} (URedTy.level (invLRU RU)) | Γ ||- A].
  Proof. 
    intros h; apply univTmTy'.
    irrelevance.
  Qed.

  Lemma univEqTmEqTy'@{h i j k l} {Γ l l' A B} (h : [Γ ||-U l]) (RA : [Γ ||-<l'> A]) :
    [LogRel@{i j k l} l | Γ ||- A ≅ B : U | LRU_ h] ->
    [LogRel@{h i j k} l' | Γ ||- A ≅ B | RA].
  Proof. intros [????? RA']. apply TyEqRecFwd in RA'. irrelevance. Qed.

  Lemma univEqTmEqTy@{h i j k l} {Γ l l' A B} (RU : [Γ ||-<l> U]) (RA : [Γ ||-<l'> A]) :
    [LogRel@{i j k l} l | Γ ||- A ≅ B : U | RU] ->
    [LogRel@{h i j k} l' | Γ ||- A ≅ B | RA].
  Proof. intros h; eapply (univEqTmEqTy' (invLRU RU)); irrelevance. Qed.

End Universe.

    
