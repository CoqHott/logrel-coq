From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance.

Set Universe Polymorphism.
Set Printing Universes.

Section UniverseReducibility.
  Context `{GenericTypingProperties}.

  Lemma redUOne {wl Γ l A} : [Γ ||-<l> A]< wl > -> [Γ ||-U<one> U]< wl >.
  Proof.
    intros ?%escape; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
  Qed.

  Lemma UnivEq'@{i j k l} {wl Γ A l} (rU : [ LogRel@{i j k l} l | Γ ||- U ]< wl >) (rA : [ LogRel@{i j k l} l | Γ ||- A : U | rU]< wl >)
    : [ LogRel@{i j k l} zero | Γ ||- A]< wl >.
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A : U | LRU_@{i j k l} (redUOne rU)]< wl >
             as [ _ _ _ _ _ hA ] by irrelevance.
    exact (LRCumulative hA).
  Qed.

  Lemma UnivEq@{i j k l} {wl Γ A l} l' (rU : [ LogRel@{i j k l} l | Γ ||- U]< wl >) (rA : [ LogRel@{i j k l} l | Γ ||- A : U | rU]< wl >)
    : [ LogRel@{i j k l} l' | Γ ||- A]< wl >.
  Proof.
    destruct l'.
    - eapply (UnivEq' rU rA).
    - econstructor. eapply LR_embedding.
      + exact Oi.
      + apply (UnivEq' rU rA).
  Qed.

  Lemma UnivEqEq@{i j k l} {wl Γ A B l l'} (rU : [ LogRel@{i j k l} l | Γ ||- U ]< wl >) (rA : [LogRel@{i j k l} l' | Γ ||- A ]< wl >) (rAB : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU ]< wl >)
    : [ LogRel@{i j k l} l' | Γ ||- A ≅ B | rA ]< wl >.
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A ≅ B : U | LRU_@{i j k l} (redUOne rU) ]< wl > as [ _ _ _ hA _ hAB ] by irrelevance.
    eapply LRTyEqIrrelevantCum. exact hAB.
  Qed.


  (* The lemmas below does not seem to be
     at the right levels for fundamental lemma ! *)

  Set Printing Universes.
  Lemma univTmTy'@{h i j k l} {wl Γ l UU A} (h : [Γ ||-U<l> UU ]< wl >) :
    [LogRel@{i j k l} l | Γ ||- A : UU | LRU_ h]< wl > -> [LogRel@{h i j k} (URedTy.level h) | Γ ||- A]< wl >.
  Proof.  intros []; now eapply RedTyRecFwd. Qed.

  Lemma univTmTy@{h i j k l} {wl Γ l A} (RU : [Γ ||-<l> U]< wl >) :
    [LogRel@{i j k l} l | Γ ||- A : U | RU]< wl > -> [LogRel@{h i j k} (URedTy.level (invLRU RU)) | Γ ||- A]< wl >.
  Proof.
    intros h; apply univTmTy'.
    irrelevance.
  Qed.

  Lemma univEqTmEqTy'@{h i j k l} {wl Γ l l' UU A B} (h : [Γ ||-U<l> UU]< wl >) (RA : [Γ ||-<l'> A]< wl >) :
    [LogRel@{i j k l} l | Γ ||- A ≅ B : UU | LRU_ h]< wl > ->
    [LogRel@{h i j k} l' | Γ ||- A ≅ B | RA]< wl >.
  Proof. intros [????? RA']. apply TyEqRecFwd in RA'. irrelevance. Qed.

  Lemma univEqTmEqTy@{h i j k l} {wl Γ l l' A B} (RU : [Γ ||-<l> U]< wl >) (RA : [Γ ||-<l'> A]< wl >) :
    [LogRel@{i j k l} l | Γ ||- A ≅ B : U | RU]< wl > ->
    [LogRel@{h i j k} l' | Γ ||- A ≅ B | RA]< wl >.
  Proof. intros h; eapply (univEqTmEqTy' (invLRU RU)); irrelevance. Qed.

End UniverseReducibility.
