(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity.

Set Universe Polymorphism.
Set Printing Universes.

(** We show a general version of irrelevance, saying that if A and A' are reducible (at levels logical relation levels lA, lA')
and A' is reducibly convertible to A, then the reducibility predicates they decode to are equivalent.
From this, both a simpler version of irrelevance and symmetry follow, by using reflexivity
in the right places. *)
(** Interestingly, we also show irrelevance with respect to universe levels, which is crucial
in later parts of the development, where this avoids creating spurious constraints on universe levels.*)


Section Irrelevances.
Context `{GenericTypingProperties}.


(** *** Equivalences of LRPack *)

Section EquivLRPack.
  Universe i i' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Definition equivLRPack {Γ Γ' A A'} (P: LRPack@{i} Γ A) (P': LRPack@{i'} Γ' A'):=
    and3@{v v v} 
      (forall B, [P | Γ ||- A ≅ B] <≈> [P' | Γ' ||- A' ≅ B])
      (forall t, [P | Γ ||- t : A] <≈> [P' | Γ' ||- t : A'])
      (forall t u, [P | Γ ||- t ≅ u : A] <≈> [P' | Γ' ||- t ≅ u : A']).
End EquivLRPack.

Lemma symLRPack@{i i' v} {Γ Γ' A A'} {P: LRPack@{i} Γ A} {P': LRPack@{i'} Γ' A'} :
    equivLRPack@{i i' v} P P' -> equivLRPack@{i' i v} P' P.
Proof.
  intros [eqT rTm eqTm]; constructor;split ;
    apply eqT + apply rTm + apply eqTm.
Qed.
  


(** *** Lemmas for product types *)

(** A difficulty is that we need to show the equivalence right away, rather than only an implication,
because of contravariance in the case of Π types. To save up work, we factor out some lemmas to
avoid having to basically duplicate their proofs. *)

Section ΠIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {Γ lA A lA' A'} 
  (ΠA : PiRedTyPack@{i j k l} Γ A lA) 
  (ΠA' : PiRedTyPack@{i' j' k' l'} Γ A' lA')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (domRed := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (domRed' := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _  ΠA'))
  (codRed := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (codRed' := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _  ΠA'))
  (eqPi : [Γ |- PiRedTyPack.prod ΠA ≅ PiRedTyPack.prod ΠA']).

Context (eqvDom : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ]),
          equivLRPack@{k k' v} (domRed Δ ρ wfΔ) (domRed' Δ ρ wfΔ))
        (eqvCod : forall {Δ a} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ])
          (ha : [domRed Δ ρ wfΔ| Δ ||- a : _])
          (ha' : [domRed' Δ ρ wfΔ | Δ ||- a : _]),
          equivLRPack@{k k' v} (codRed Δ a ρ wfΔ ha) (codRed' Δ a ρ wfΔ ha')).

Lemma ΠIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros [] ; cbn in *; econstructor.
  - now gen_typing.
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros ; now apply eqvDom.
  - intros; cbn; unshelve eapply eqvCod.
    2: eauto.
    now eapply eqvDom.
Qed.

Lemma ΠIrrelevanceTm t : [Γ ||-<lA> t : A | RA] -> [Γ ||-<lA'> t : A' | RA'].
Proof.
  intros []; cbn in *; econstructor; tea.
  - now eapply redtmwf_conv.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqvCod.
    2: now auto.
    now apply eqvDom.
  - intros; unshelve eapply eqvCod, eq.
    all: now eapply eqvDom.
Defined.

Lemma ΠIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΠIrrelevanceTm.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqvCod.
    2: now auto.
    now apply eqvDom.
Qed.

End ΠIrrelevanceLemmas.

Lemma ΠIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'} 
  (ΠA : PiRedTyPack@{i j k l} Γ A lA) 
  (ΠA' : PiRedTyPack@{i' j' k' l'} Γ A' lA')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (domRed := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (domRed' := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _  ΠA'))
  (codRed := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (codRed' := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _  ΠA'))
  (eqPi : [Γ |- PiRedTyPack.prod ΠA ≅ PiRedTyPack.prod ΠA'])
  (eqvDom : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ]),
          equivLRPack@{k k' v} (domRed Δ ρ wfΔ) (domRed' Δ ρ wfΔ))
  (eqvCod : forall {Δ a} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ])
          (ha : [Δ ||-<lA> a : _| domRed Δ ρ wfΔ])
          (ha' : [Δ ||-<lA'> a : _| domRed' Δ ρ wfΔ ]),
          equivLRPack@{k k' v} (codRed Δ a ρ wfΔ ha) (codRed' Δ a ρ wfΔ ha'))
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (eqvDom' := fun Δ ρ wfΔ => symLRPack (@eqvDom Δ ρ wfΔ)).
  pose proof (eqvCod' := fun Δ a ρ wfΔ ha ha' => symLRPack (@eqvCod Δ a ρ wfΔ ha ha')).
  constructor.
  - split; now apply ΠIrrelevanceTyEq.
  - split; now apply ΠIrrelevanceTm.
  - split; now apply ΠIrrelevanceTmEq.
Qed.

(** *** Irrelevance for neutral types *)

Lemma NeIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ A A'} lA lA'
  (neA : [Γ ||-ne A])
  (neA' : [Γ ||-ne A'])
  (RA := LRne_@{i j k l} lA neA)
  (RA' := LRne_@{i' j' k' l'} lA' neA')
  (eqAA' : [Γ ||-ne A ≅ A' | neA ])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  destruct neA as [ty], neA' as [ty'], eqAA' as [ty0']; cbn in *.
  assert (ty0' = ty') by (eapply redtywf_det; tea; now constructor); subst.
  assert [Γ |- ty ≅ ty'] as convty by gen_typing.
  split.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    all: etransitivity ; [| tea]; tea; now symmetry.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    1,3: now eapply redtmwf_conv.
    all: now eapply convneu_conv.
  + intros ??; split; intros []; econstructor; cbn in *.
    1-2,6-7: now eapply redtmwf_conv.
    all: tea.
    all: now eapply convneu_conv.
Qed.

(** *** Lemmas for conversion of reducible neutral terms at arbitrary types *)

Lemma NeNfconv {Γ k A A'} : [Γ |- A ≅ A'] -> [Γ ||-NeNf k : A] -> [Γ ||-NeNf k : A'].
Proof.
  intros ? []; econstructor; tea; gen_typing.
Qed.

Lemma NeNfEqconv {Γ k k' A A'} : [Γ |- A ≅ A'] -> [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k ≅ k' : A'].
Proof.
  intros ? []; econstructor; tea; gen_typing.
Qed.



Section LRIrrelevant.
Universe u v.
(** u is a small universe level that may be instanciated to Set. v is a large universe level *)

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Section LRIrrelevantInductionStep.

Universe i j k l i' j' k' l'.

Definition IHStatement lA lA' :=
  (forall l0 (ltA : l0 << lA) (ltA' : l0 << lA'),
      prod@{v v}
        (forall Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
        (forall Γ t
           (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ])
           (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
           u,
            [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ] <≈>
            [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ])).

Lemma UnivIrrelevanceLRPack
  {Γ lA lA' A A'}
  (IH : IHStatement lA lA')
  (hU : [Γ ||-U<lA> A]) (hU' : [Γ ||-U<lA'> A'])
  (RA := LRU_@{i j k l} hU) (RA' := LRU_@{i' j' k' l'} hU') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  revert IH; destruct hU as [_ []], hU' as [_ []]; intro IH; destruct (IH zero Oi Oi) as [IHty IHeq].
  constructor.
  + intros; cbn; split; intros []; now constructor.
  + intros ?; destruct (IHty Γ t) as [tfwd tbwd]; split; intros [];
      unshelve econstructor.
    6: now apply tfwd.
    9: now apply tbwd.
    all : tea.
  + cbn ; intros ? ?;
    destruct (IHty Γ t) as [tfwd tbwd];
    destruct (IHty Γ u) as [ufwd ubwd].
    split; intros [[] []]; cbn in *; unshelve econstructor.
    3: now apply tfwd.
    5: now apply tbwd.
    6: now apply ufwd.
    8: now apply ubwd.
    (* all: apply todo. *)
    all: cbn.
    6: now refine (fst (IHeq _ _ _ _ _) _).
    7: now refine (snd (IHeq _ _ _ _ _) _).
    1-4: now econstructor.
    all: cbn; tea.
Qed.

(** ** The main theorem *)

Lemma LRIrrelevantPreds {lA lA'}
  (IH : IHStatement lA lA')
  (Γ : context) (A A' : term)
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' redTmA' eqTmA')
  (RA := Build_LRPack Γ A eqTyA redTmA eqTmA)
  (RA' := Build_LRPack Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (fun Γ l0 ltA ltA' => fst (IH l0 ltA ltA') Γ) as IHty.
  pose proof (fun Γ l0 ltA ltA' => snd (IH l0 ltA ltA') Γ) as IHeq.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? h1 | ? ? neA | ? A ΠA HAad IHdom IHcod]
    in RA, A', RA', eqTyA', eqTmA', redTmA', lrA', he, s |- *.
  - destruct lrA' as [? ? h2 | | ]; try solve [destruct s] ; clear s.
    now apply UnivIrrelevanceLRPack.
  - destruct lrA' as [|? A' neA'| ] ; try solve [destruct s] ; clear s.
    exact (NeIrrelevanceLRPack lA lA' neA neA' he).
  - destruct lrA' as [| | ? A' ΠA' HAad'] ; try solve [destruct s] ; clear s.
    pose (PA := PiRedTyPack.pack ΠA HAad).
    pose (PA' := PiRedTyPack.pack ΠA' HAad').
    destruct he as [na0 dom0 cod0 ?? domRed codRed], ΠA' as [na1 dom1 cod1];
    assert (tProd na0 dom0 cod0 = tProd na1 dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    eapply (ΠIrrelevanceLRPack PA PA').
    + eassumption.
    + intros; unshelve eapply IHdom.
      1: eapply (LRAd.adequate (PiRedTyPack.domRed PA' _ _)).
      eapply domRed.
    + intros; unshelve eapply IHcod.
      1: eapply (LRAd.adequate (PiRedTyPack.codRed PA' _ _ _)).
      eapply codRed.
Qed.


Lemma LRIrrelevantCumTy {lA}
  (IH : IHStatement lA lA)
  (Γ : context) (A : term)
  : [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ].
Proof.
  intros [ [] lrA ] ; cbn in lrA.
  induction lrA as [? ? [l1 lt1] | ? | ? A [] [] IHdom IHcod].
  - eapply LRU_. econstructor ; tea.
  - eapply LRne_. exact neA.
  - cbn in *. eapply LRPi'. unshelve econstructor.
    6: eassumption.
    3,4,5: tea.
    + exact IHdom.
    + intros Δ a ρ tΔ ra. eapply IHcod.
      destruct (LRIrrelevantPreds IH Δ (dom⟨ρ⟩) (dom⟨ρ⟩)
                  (domAd Δ ρ tΔ) (IHdom Δ ρ tΔ : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHdom Δ ρ tΔ))
                  (LRTyEqRefl (domAd Δ ρ tΔ))) as [_ irrTmRed _].
      eapply (snd (irrTmRed a)). exact ra.
    + cbn. intros Δ a b ρ tΔ ra rb rab.
      destruct (LRIrrelevantPreds IH Δ (dom⟨ρ⟩) (dom⟨ρ⟩)
                  (domAd Δ ρ tΔ) (IHdom Δ ρ tΔ : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHdom Δ ρ tΔ))
                  (LRTyEqRefl (domAd Δ ρ tΔ))) as [_ irrTmRed irrTmEq].
      destruct (LRIrrelevantPreds IH Δ (cod[a .: ρ >> tRel]) (cod[a .: ρ >> tRel])
                  (codAd Δ a ρ tΔ (snd (irrTmRed a) ra))
                  (IHcod Δ a ρ tΔ (snd (irrTmRed a) ra)
                    : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHcod Δ a ρ tΔ (snd (irrTmRed a) ra)))
                  (LRTyEqRefl (codAd Δ a ρ tΔ (snd (irrTmRed a) ra))))
        as [irrTyEq _ _].
      eapply (fst (irrTyEq (cod[b .: ρ >> tRel]))).
      eapply codExt.
      exact (snd (irrTmRed b) rb).
      exact (snd (irrTmEq a b) rab).
Qed.


Lemma IrrRec0 : IHStatement zero zero.
Proof.
  intros ? ltA; inversion ltA.
Qed.

End LRIrrelevantInductionStep.

Theorem IrrRec@{i j k l i' j' k' l'} {lA} {lA'} :
  IHStatement@{i j k l i' j' k' l'} lA lA'.
Proof.
  intros l0 ltA ltA'.
  destruct ltA. destruct ltA'. cbn in *.
  split.
  - intros Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} Γ t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (LRTyEqRefl_ lr1)) as [tyEq _ _].
    exact (tyEq u).
Qed.

Theorem LRIrrelevantCum@{i j k l i' j' k' l'}
  (Γ : context) (A A' : term) {lA lA'}
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  @and3@{v v v} (forall B, eqTyA B <≈> eqTyA' B)
    (forall t, redTmA t <≈> redTmA' t)
    (forall t u, eqTmA t u <≈> eqTmA' t u).
Proof.
  exact (LRIrrelevantPreds@{i j k l i' j' k' l'} IrrRec Γ A A' lrA lrA').
Qed.

Theorem LRCumulative@{i j k l i' j' k' l'} {lA}
  {Γ : context} {A : term}
  : [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ].
Proof.
  exact (LRIrrelevantCumTy@{i j k l i' j' k' l'} IrrRec Γ A).
Qed.

Corollary LRCumulative' @{i j k l i' j' k' l'} {lA}
  {Γ : context} {A A' : term}
  : A = A' -> [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A' ].
Proof.
  intros ->; apply LRCumulative.
Qed.
End LRIrrelevant.


Corollary TyEqIrrelevantCum Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A eqTyA' redTmA' eqTmA') :
  forall B, eqTyA B -> eqTyA' B.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A ≅ B | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary RedTmIrrelevantCum Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A eqTyA' redTmA' eqTmA') :
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmRedIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.


Corollary TmEqIrrelevantCum Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A eqTyA' redTmA' eqTmA') :
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.



Corollary TyEqSym Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' -> eqTyA' A.
Proof.
  intros.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  1: eauto.
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqSym lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA] -> [Γ ||-< lA' > A' ≅ A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqSym.
Qed.

Corollary RedTmConv Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
Qed.

Corollary LRTmRedConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A' ]) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmConv.
Qed.

Corollary TmEqRedConv Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
Qed.

Corollary LRTmEqRedConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqRedConv.
Qed.

Corollary LRTmTmEqIrrelevant' lA lA' Γ A A' (e : A = A')
  (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  forall t u, 
  [Γ ||-<lA> t : A | lrA] × [Γ ||-< lA > t ≅ u : A | lrA] -> 
  [Γ ||-<lA'> t : A' | lrA'] × [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  intros ?? []; split; [eapply LRTmRedIrrelevant'| eapply LRTmEqIrrelevant']; tea.
Qed.

Set Printing Primitive Projection Parameters.

Lemma NeNfEqSym {Γ k k' A} : [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k' ≅ k : A].
Proof.
  intros []; constructor; tea; now symmetry.
Qed.

Lemma LRTmEqSym@{h i j k l} lA Γ A (lrA : [LogRel@{i j k l} lA | Γ ||- A]) : forall t u,
  [Γ ||-<lA> t ≅ u : A |lrA] -> [Γ ||-<lA> u ≅ t : A |lrA].
Proof.
  pattern lA, Γ, A, lrA. apply LR_rect_TyUr; clear lA Γ A lrA.
  - intros * []. unshelve econstructor; try eassumption.
    1: symmetry; eassumption.
    (* Need an additional universe level h < i *)
    eapply TyEqSym@{h i j k h i j k}. 3:exact relEq.
    all: eapply LogRelRec_unfold; eapply LRAd.adequate; eassumption.
  - intros * []. unshelve econstructor.
    3,4: eassumption.
    1,2: eassumption.
    symmetry; eassumption.
  - intros * ihdom ihcod * []. unshelve econstructor.
    1,2: eassumption.
    1: symmetry; eassumption.
    intros. apply ihcod. eapply eqApp.
Qed.

End Irrelevances.


(** ** Tactics for irrelevance, with and without universe cumulativity *)

Ltac irrelevanceCum0 :=
  lazymatch goal with
  | [|- [_ ||-<_> _]] => (now eapply LRCumulative) + eapply LRCumulative'
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ | _ ||- _ ≅ _ : _ ] ] => eapply LRTmEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevantCum'
  end.

Ltac irrelevanceCum := irrelevanceCum0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceCumRefl := irrelevanceCum0 ; [reflexivity|].

Ltac irrelevance0 :=
  lazymatch goal with
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevant'
  | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevant'
  | [|- [_ | _ ||- _ ≅ _ : _ ] ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ : _ | _] × [_ ||-<_> _≅ _ : _ | _]] => eapply LRTmTmEqIrrelevant'
  end.

Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceRefl := irrelevance0 ; [reflexivity|].
