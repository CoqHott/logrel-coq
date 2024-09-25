From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance.

Set Universe Polymorphism.
Set Printing Universes.

Section UniverseReducibility.
  Context `{GenericTypingProperties}.

  Lemma redUOne {Γ l A} : [Γ ||-<l> A] -> [Γ ||-U<one> U].
  Proof.
    intros ?%escape; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
  Qed.

  Lemma UnivEq'@{i j k l} {Γ A l} (rU : [ LogRel@{i j k l} l | Γ ||- U ]) (rA : [ LogRel@{i j k l} l | Γ ||- A : U | rU])
    : [ LogRel@{i j k l} zero | Γ ||- A].
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A : U | LRU_@{i j k l} (redUOne rU)]
             as [ _ _ _ _ hA ] by irrelevance.
    exact (LRCumulative hA).
  Qed.

  Lemma UnivEq@{i j k l} {Γ A l} l' (rU : [ LogRel@{i j k l} l | Γ ||- U]) (rA : [ LogRel@{i j k l} l | Γ ||- A : U | rU])
    : [ LogRel@{i j k l} l' | Γ ||- A].
  Proof.
    destruct l'.
    - eapply (UnivEq' rU rA).
    - econstructor. eapply LR_embedding.
      + exact Oi.
      + apply (UnivEq' rU rA).
  Qed.

  Lemma UnivEqEq@{i j k l} {Γ A B l l'} (rU : [ LogRel@{i j k l} l | Γ ||- U ]) (rA : [LogRel@{i j k l} l' | Γ ||- A ]) (rAB : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU ])
    : [ LogRel@{i j k l} l' | Γ ||- A ≅ B | rA ].
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A ≅ B : U | LRU_@{i j k l} (redUOne rU) ] as [ _ _ _ hA _ hAB ] by irrelevance.
    eapply LRTyEqIrrelevantCum. exact hAB.
  Qed.


  (* The lemmas below does not seem to be
     at the right levels for fundamental lemma ! *)

  Set Printing Universes.
  Lemma univTmTy'@{h i j k l} {Γ l UU A} (h : [Γ ||-U<l> UU ]) :
    [LogRel@{i j k l} l | Γ ||- A : UU | LRU_ h] -> [LogRel@{h i j k} (URedTy.level h) | Γ ||- A].
  Proof.  intros []; now eapply RedTyRecFwd. Qed.

  Lemma univTmTy@{h i j k l} {Γ l A} (RU : [Γ ||-<l> U]) :
    [LogRel@{i j k l} l | Γ ||- A : U | RU] -> [LogRel@{h i j k} (URedTy.level (invLRU RU)) | Γ ||- A].
  Proof.
    intros h; apply univTmTy'.
    irrelevance.
  Qed.

  Lemma univEqTmEqTy'@{h i j k l} {Γ l l' UU A B} (h : [Γ ||-U<l> UU]) (RA : [Γ ||-<l'> A]) :
    [LogRel@{i j k l} l | Γ ||- A ≅ B : UU | LRU_ h] ->
    [LogRel@{h i j k} l' | Γ ||- A ≅ B | RA].
  Proof. intros [????? RA']. apply TyEqRecFwd in RA'. irrelevance. Qed.

  Lemma univEqTmEqTy@{h i j k l} {Γ l l' A B} (RU : [Γ ||-<l> U]) (RA : [Γ ||-<l'> A]) :
    [LogRel@{i j k l} l | Γ ||- A ≅ B : U | RU] ->
    [LogRel@{h i j k} l' | Γ ||- A ≅ B | RA].
  Proof. intros h; eapply (univEqTmEqTy' (invLRU RU)); irrelevance. Qed.

End UniverseReducibility.
