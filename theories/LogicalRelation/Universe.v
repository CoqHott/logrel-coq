From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance.

Set Universe Polymorphism.
Set Printing Universes.

Section UniverseReducibility.
  Context `{GenericTypingProperties}.

  (* These proofs are somewhat hack-ish and do not generalize properly to arbitrarily many universes *)
  (* In particular, they exploit the following lemma, which proves "cumulativity" of LogRel0, but
     unfortunately this lemma does not generalize to LogRel l *)
  (* In proper generality, one would need to show that
     LogRel@{i j k} l Γ A EqTy RedTm EqTm -> LogRel@{j k l} l Γ A EqTy' RedTm' EqTm'
     where EqTy' RedTm' EqTm' are equivalent but non definitionally equal predicates *)

  Definition LogRel0_Cumulative@{i j k l} {Γ A} {EqTy RedTm : term -> Type@{j}} {EqTm : term -> term -> Type@{j}}
    (lr : LogRel0@{i j k} Γ A EqTy RedTm EqTm) : LogRel0@{j k l} Γ A EqTy RedTm EqTm.
  Proof.
    induction lr as [ ? HU | ? ? neA | ? ? ? ? domAd codAd ].
    - exact (match elim HU.(URedTy.lt) with end).
    - exact (LRne _ neA).
    - eapply LRPi@{j k l}. unshelve econstructor.
      + exact domAd.
      + exact codAd.
  Defined.

  Definition TyRed_Cumulative@{i j k l} {Γ} {A} (rA : [ LogRel0@{i j k} | Γ ||- A ])
      : [ LogRel0@{j k l} | Γ ||- A ].
  Proof.
    destruct rA as [Pack PackAd].
    unshelve econstructor.
    - exact Pack.
    - exact (LogRel0_Cumulative@{i j k l} PackAd).
  Defined.

  Lemma redUOne {Γ l A} : [Γ ||-<l> A] -> [Γ ||-U one].
  Proof.
    intros ?%escape_; econstructor; [easy| gen_typing].
  Qed.

  Lemma UnivEq'@{i j k l} {Γ A l} (rU : [ LogRel@{i j k l} l | Γ ||- U ]) (rA : [ LogRel@{i j k l} l | Γ ||- A : U | rU])
    : [ LogRel@{i j k l} zero | Γ ||- A].
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A : U | LRU_@{i j k l} (redUOne rU)]
             as [ _ _ _ _ hA ] by irrelevance.
    exact (TyRed_Cumulative hA).
  Defined.

  Lemma UnivEq@{i j k l} {Γ A l} l' (rU : [ LogRel@{i j k l} l | Γ ||- U]) (rA : [ LogRel@{i j k l} l | Γ ||- A : U | rU])
    : [ LogRel@{i j k l} l' | Γ ||- A].
  Proof.
    destruct l'.
    - eapply (UnivEq' rU rA).
    - econstructor. eapply LR_embedding.
      + exact Oi.
      + apply (UnivEq' rU rA).
  Defined.

  Lemma UnivEqEq@{i j k l} {Γ A B l l'} (rU : [ LogRel@{i j k l} l | Γ ||- U ]) (rA : [LogRel@{i j k l} l' | Γ ||- A ]) (rAB : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU ])
    : [ LogRel@{i j k l} l' | Γ ||- A ≅ B | rA ].
  Proof.
    assert [ LogRel@{i j k l} one | Γ ||- A ≅ B : U | LRU_@{i j k l} (redUOne rU) ] as [ _ _ _ hA _ hAB ] by irrelevance.
    change ([ TyRed_Cumulative@{i j k l} hA | Γ ||- A ≅ B ]) in hAB.
    eapply LRTyEqIrrelevant. exact hAB.
  Qed.


  (* The lemmas below does not seem to be
     at the right levels for fundamental lemma ! *)

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

End UniverseReducibility.