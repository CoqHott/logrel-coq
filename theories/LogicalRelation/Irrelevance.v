From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context Untyped Weakening GenericTyping LogicalRelation Reduction.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity.

Set Universe Polymorphism.

Section Irrelevances.
Context `{GenericTypingProperties}.

Section ΠIrrelevanceLemmas.
Universe u u' v.
Context Γ A A' (ΠA : PiRedTy@{u} Γ A) (ΠA' : PiRedTy@{u'} Γ A')
  (dom := PiRedTy.dom ΠA)
  (dom' := PiRedTy.dom ΠA')
  (domRed := (@PiRedTy.domRed _ _ _ _ _ _ _ ΠA))
  (domRed' := (@PiRedTy.domRed _ _ _ _ _ _ _ ΠA'))
  (cod := PiRedTy.cod ΠA)
  (cod' := PiRedTy.cod ΠA')
  (codRed := (@PiRedTy.codRed _ _ _ _ _ _ _ ΠA))
  (codRed' := (@PiRedTy.codRed _ _ _ _ _ _ _ ΠA'))
  (eqPi : [Γ |- tProd (PiRedTy.na ΠA) dom cod ≅ tProd (PiRedTy.na ΠA') dom' cod']).

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Lemma ΠIrrelevanceTyEq  :
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [  |- Δ]),
  (and3@{v v v} (forall B : term,
      [domRed Δ ρ h | Δ ||- dom⟨ρ⟩ ≅ B] <≈> [domRed' Δ ρ h | Δ ||- dom'⟨ρ⟩ ≅ B])
    (forall t : term,
      [domRed Δ ρ h | Δ ||- t : dom⟨ρ⟩] <≈> [domRed' Δ ρ h | Δ ||- t : dom'⟨ρ⟩])
    (forall t u : term,
      [domRed Δ ρ h | Δ ||- t ≅ u : dom⟨ρ⟩ ] <≈> [domRed' Δ ρ h | Δ ||- t ≅ u : dom'⟨ρ⟩]))) ->
  (forall (Δ : context) (ρ : Δ ≤ Γ) (a : term) (h : [  |- Δ])
      (ha : [domRed Δ ρ h | Δ ||- a : dom⟨ρ⟩])
      (ha' : [domRed' Δ ρ h | Δ ||- a : dom'⟨ρ⟩]),
  (and3@{v v v} (forall B : term,
      [codRed Δ a ρ h ha | Δ ||- cod[a .: (ρ >> tRel)] ≅ B] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- cod'[a .: (ρ >> tRel)] ≅ B])
    (forall t : term,
      [codRed Δ a ρ h ha | Δ ||- t : cod[a .: (ρ >> tRel)] ] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- t : cod'[a .: (ρ >> tRel)]])
    (forall t u : term,
      [codRed Δ a ρ h ha | Δ ||- t ≅ u : cod[a .: (ρ >> tRel)]] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- t ≅ u : cod'[a .: (ρ >> tRel)] ]))) ->
  forall B, [Γ ||-Π A ≅ B | ΠA] -> [Γ ||-Π A' ≅ B | ΠA'].
Proof.
  intros IHdom IHcod B [] ; cbn in *.
  econstructor.
  - now gen_typing.
  - cbn in *.
    etransitivity.
    2: eassumption.
    now symmetry.
  - intros ; now apply IHdom.
  - intros.
    cbn in *.
    unshelve eapply IHcod.
    2: eauto.
    now eapply IHdom.
Qed.

Lemma ΠIrrelevanceTm  :
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [  |- Δ]),
  (and3@{v v v} (forall B : term,
      [domRed Δ ρ h | Δ ||- dom⟨ρ⟩ ≅ B] <≈> [domRed' Δ ρ h | Δ ||- dom'⟨ρ⟩ ≅ B])
    (forall t : term,
      [domRed Δ ρ h | Δ ||- t : dom⟨ρ⟩] <≈> [domRed' Δ ρ h | Δ ||- t : dom'⟨ρ⟩])
    (forall t u : term,
      [domRed Δ ρ h | Δ ||- t ≅ u : dom⟨ρ⟩ ] <≈> [domRed' Δ ρ h | Δ ||- t ≅ u : dom'⟨ρ⟩]))) ->
  (forall (Δ : context) (ρ : Δ ≤ Γ) (a : term) (h : [  |- Δ])
      (ha : [domRed Δ ρ h | Δ ||- a : dom⟨ρ⟩])
      (ha' : [domRed' Δ ρ h | Δ ||- a : dom'⟨ρ⟩]),
  (and3@{v v v} (forall B : term,
      [codRed Δ a ρ h ha | Δ ||- cod[a .: (ρ >> tRel)] ≅ B] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- cod'[a .: (ρ >> tRel)] ≅ B])
    (forall t : term,
      [codRed Δ a ρ h ha | Δ ||- t : cod[a .: (ρ >> tRel)] ] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- t : cod'[a .: (ρ >> tRel)]])
    (forall t u : term,
      [codRed Δ a ρ h ha | Δ ||- t ≅ u : cod[a .: (ρ >> tRel)]] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- t ≅ u : cod'[a .: (ρ >> tRel)] ]))) ->
  forall t, [Γ ||-Π t : A | ΠA] -> [Γ ||-Π t : A' | ΠA'].
Proof.
  intros IHdom IHcod B [] ; cbn in *.
  econstructor.
  - cbn.
    econstructor.
    all: gen_typing.
  - eassumption.
  - cbn.
    gen_typing.
  - intros.
    unshelve eapply IHcod.
    2: now auto.
    now apply IHdom.
  - intros.
    unshelve eapply IHcod, eq.
    all: now eapply IHdom.
Defined.

Lemma ΠIrrelevanceTmEq  :
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [  |- Δ]),
  (and3@{v v v} (forall B : term,
      [domRed Δ ρ h | Δ ||- dom⟨ρ⟩ ≅ B] <≈> [domRed' Δ ρ h | Δ ||- dom'⟨ρ⟩ ≅ B])
    (forall t : term,
      [domRed Δ ρ h | Δ ||- t : dom⟨ρ⟩] <≈> [domRed' Δ ρ h | Δ ||- t : dom'⟨ρ⟩])
    (forall t u : term,
      [domRed Δ ρ h | Δ ||- t ≅ u : dom⟨ρ⟩ ] <≈> [domRed' Δ ρ h | Δ ||- t ≅ u : dom'⟨ρ⟩]))) ->
  (forall (Δ : context) (ρ : Δ ≤ Γ) (a : term) (h : [  |- Δ])
      (ha : [domRed Δ ρ h | Δ ||- a : dom⟨ρ⟩])
      (ha' : [domRed' Δ ρ h | Δ ||- a : dom'⟨ρ⟩]),
  (and3@{v v v} (forall B : term,
      [codRed Δ a ρ h ha | Δ ||- cod[a .: (ρ >> tRel)] ≅ B] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- cod'[a .: (ρ >> tRel)] ≅ B])
    (forall t : term,
      [codRed Δ a ρ h ha | Δ ||- t : cod[a .: (ρ >> tRel)] ] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- t : cod'[a .: (ρ >> tRel)]])
    (forall t u : term,
      [codRed Δ a ρ h ha | Δ ||- t ≅ u : cod[a .: (ρ >> tRel)]] <≈>
      [codRed' Δ a ρ h ha' | Δ ||- t ≅ u : cod'[a .: (ρ >> tRel)] ]))) ->
  forall t u, [Γ ||-Π t ≅ u : A | ΠA] -> [Γ ||-Π t ≅ u : A' | ΠA'].
Proof.
  intros IHdom IHcod t u [] ; cbn in *.
  unshelve econstructor.
  - now eapply ΠIrrelevanceTm.
  - now eapply ΠIrrelevanceTm.
  - cbn.
    gen_typing.
  - intros.
    unshelve eapply IHcod.
    2: now auto.
    now apply IHdom.
Qed.

End ΠIrrelevanceLemmas.

Section LRIrrelevant.
Universe u v. (* u is a small universe level that may be instanciated to Set. v is a large universe level *)

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Lemma LRIrrelevantPreds@{i j k l i' j' k' l'} {lA lA'}
  (IH : forall l0 (ltA : l0 << lA) (ltA' : l0 << lA')
    , prod@{v v}
        (forall Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
        (forall Γ t (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ])
                (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ]) u
          , [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ]))
  (Γ : context) (A A' : term)
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
  pose proof (fun Γ l0 ltA ltA' => fst (IH l0 ltA ltA') Γ) as IHty.
  pose proof (fun Γ l0 ltA ltA' => snd (IH l0 ltA ltA') Γ) as IHeq.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? [l1 lt1] | ? ? [] | ? A [] [] IHdom IHcod]
    in A', eqTyA', eqTmA', redTmA', lrA', he, s |- *.
  - destruct lrA' as [? ? [l2 lt2] | | ]; try solve [destruct s] ; clear s.
    destruct lt2 ; destruct lt1. split.
    + intros ?.
      split.
      all: eauto.
    + intros ?.
      split.
      all: intros [].
      all: econstructor.
      1, 2, 3, 5, 6, 7: tea.
      * apply (fst (IHty Γ zero Oi Oi t)). exact rel.
      * apply (snd (IHty Γ zero Oi Oi t)). exact rel.
    + cbn ; intros ? ?.
      split.
      all: intros [[] []] ; cbn in *.
      all: unshelve econstructor.
      * econstructor. 1, 2, 3: tea.
        apply (fst (IHty Γ zero Oi Oi t)). exact relL.
      * econstructor. 1, 2, 3: tea.
        apply (fst (IHty Γ zero Oi Oi u)). exact relR.
      * apply (fst (IHty Γ zero Oi Oi t)). exact relL.
      * econstructor. 1, 2, 3: tea.
        apply (snd (IHty Γ zero Oi Oi t)). exact relL.
      * econstructor. 1, 2, 3: tea.
        apply (snd (IHty Γ zero Oi Oi u)). exact relR.
      * apply (snd (IHty Γ zero Oi Oi t)). exact relL.
      * cbn. eassumption.
      * apply (fst (IHty Γ zero Oi Oi u)). exact relR.
      * apply (fst (IHeq Γ zero Oi Oi t relL (fst (IHty Γ zero Oi Oi t) relL) u)). exact relEq.
      * cbn. eassumption.
      * apply (snd (IHty Γ zero Oi Oi u)). exact relR.
      * apply (snd (IHeq Γ zero Oi Oi t (snd (IHty Γ zero Oi Oi t) relL) relL u)). exact relEq.
  - destruct lrA' as [|? A' neA'|] ; try solve [destruct s] ; clear s.
    destruct he as [AA], neA' as [AA'] ; cbn in *.
    assert (AA' = AA) as eqAA'.
    {
      all: eapply whredty_det ; econstructor ; [idtac |now econstructor| idtac |now econstructor].
      all: gen_typing.
    }
    revert red1 ne1 eq1. pattern AA'.
    set (P := fun _ => _). apply (tr P (eq_sym eqAA')). subst P; cbn.
    intros red1 ne1 eq1.
    assert [Γ |- ty ≅ AA] as convtAA by gen_typing.
    split.
    + intros ?.
      split.
      all: intros [].
      all: econstructor.
      all: cbn in *.
      all: try eauto.
      2: etransitivity ; eassumption.
      clear eq1; etransitivity ; [symmetry|..]; eassumption.
    + intros ?.
      split.
      2: symmetry in convtAA.
      all: intros [].
      all: econstructor ; cbn in *.
      all: try eauto.
      1,3: eapply redtmwf_conv ; eassumption.
      all: gen_typing.
    + intros ? ?.
      split.
      2: symmetry in convtAA.
      all: intros [].
      all: econstructor.
      all: cbn in *.
      1-2,6-7: eapply redtmwf_conv ; eassumption.
      1-2,4-5: eassumption.
      all: now gen_typing.
  - destruct lrA' as [| | ? A' [] []] ; try solve [destruct s] ; clear s.
    destruct he ; cbn -[subst1] in *.
    assert (tProd na0 dom0 cod0 = tProd na1 dom1 cod1) as ePi
      by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    pose proof (IHdom_ := fun Δ ρ h => IHdom Δ ρ h _ _ _ _ (domAd0 Δ ρ h) (domRed1 Δ ρ h)).
    assert (IHcod_ : forall Δ a (ρ : Δ ≤ Γ) (h : [|- Δ])
      (ha : [domRed Δ ρ h | Δ ||- a : dom⟨ρ⟩])
      (ha' : [domRed0 Δ ρ h | Δ ||- a : dom1⟨ρ⟩]),
      [×
        (forall B,
          [codRed Δ a ρ h ha | Δ ||- cod[a .: (ρ >> tRel)] ≅ B] <≈>
          [codRed0 Δ a ρ h ha' | Δ ||- cod1[a .: (ρ >> tRel)] ≅ B]),
        (forall t,
          [codRed Δ a ρ h ha | Δ ||- t : cod[a .: (ρ >> tRel)]] <≈>
          [codRed0 Δ a ρ h ha' | Δ ||- t : cod1[a .: (ρ >> tRel)]]) &
      (forall t u,
        [codRed Δ a ρ h ha | Δ ||- t ≅ u : cod[a .: (ρ >> tRel)]] <≈>
        [codRed0 Δ a ρ h ha' | Δ ||- t ≅ u : cod1[a .: (ρ >> tRel)]])
      ]).
    {
      intros.
      eapply IHcod.
      1: eapply codAd0.
      eauto.
    }
    split.
    + split ; intros.
      all: eapply ΠIrrelevanceTyEq.
      4,8: eassumption.
      1,4: assumption + now symmetry.
      1-2: now eauto.
      * do 2 split ; intros.
        all: now eapply IHdom_ ; eauto.
      * do 2 split ; intros.
        all: now eapply IHcod_ ; eauto.
    + split ; intros.
      all: eapply ΠIrrelevanceTm.
      4,8: eassumption.
      1,4: assumption + now symmetry.
      1-2: now eauto.
      * do 2 split ; intros.
        all: now eapply IHdom_ ; eauto.
      * do 2 split ; intros.
        all: now eapply IHcod_ ; eauto.
    + split ; intros.
      all: eapply ΠIrrelevanceTmEq.
      4,8: eassumption.
      1,4: assumption + now symmetry.
      1-2: now eauto.
      * do 2 split ; intros.
        all: now eapply IHdom_ ; eauto.
      * do 2 split ; intros.
        all: now eapply IHcod_ ; eauto.
Qed.

Lemma LRIrrelevantCumTy@{i j k l i' j' k' l'} {lA}
  (IH : forall l0 (ltA : l0 << lA) (ltA' : l0 << lA)
    , prod@{v v}
        (forall Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} lA l0 ltA' | Γ ||- t ])
        (forall Γ t (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ])
                (lr2 : [ LogRelRec@{i' j' k'} lA l0 ltA' | Γ ||- t ]) u
          , [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ] <≈> [ LogRelRec@{i' j' k'} lA l0 ltA' | Γ ||- t ≅ u | lr2 ]))
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
      destruct (LRIrrelevantPreds@{i j k l i' j' k' l'} IH Δ (dom⟨ρ⟩) (dom⟨ρ⟩)
                  (domAd Δ ρ tΔ) (IHdom Δ ρ tΔ : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHdom Δ ρ tΔ))
                  (LRTyEqRefl (domAd Δ ρ tΔ))) as [_ irrTmRed _].
      eapply (snd (irrTmRed a)). exact ra.
    + cbn. intros Δ a b ρ tΔ ra rb rab.
      destruct (LRIrrelevantPreds@{i j k l i' j' k' l'} IH Δ (dom⟨ρ⟩) (dom⟨ρ⟩)
                  (domAd Δ ρ tΔ) (IHdom Δ ρ tΔ : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHdom Δ ρ tΔ))
                  (LRTyEqRefl (domAd Δ ρ tΔ))) as [_ irrTmRed irrTmEq].
      destruct (LRIrrelevantPreds@{i j k l i' j' k' l'} IH Δ (cod[a .: ρ >> tRel]) (cod[a .: ρ >> tRel])
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

Lemma IrrRec0@{i j k i' j' k'} l0 (ltA : l0 << zero) (ltA' : l0 << zero)
  : prod@{v v}
      (forall Γ t, [ LogRelRec@{i j k} zero l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} zero l0 ltA' | Γ ||- t ])
      (forall Γ t (lr1 : [ LogRelRec@{i j k} zero l0 ltA | Γ ||- t ])
              (lr2 : [ LogRelRec@{i' j' k'} zero l0 ltA' | Γ ||- t ]) u
        , [ LogRelRec@{i j k} zero l0 ltA | Γ ||- t ≅ u | lr1 ] <≈> [ LogRelRec@{i' j' k'} zero l0 ltA' | Γ ||- t ≅ u | lr2 ]).
Proof.
  inversion ltA.
Qed.

Theorem IrrRec@{i j k i' j' k'} {lA} {lA'} l0 (ltA : l0 << lA) (ltA' : l0 << lA')
  : prod@{v v}
      (forall Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
      (forall Γ t (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ])
              (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ]) u
        , [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ]).
Proof.
  destruct ltA. destruct ltA'. cbn in *.
  split.
  - intros Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j u i' j'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' u i j}).
  - intros Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j u i' j'} Γ t t
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

Set Printing Primitive Projection Parameters.

Lemma LRTmEqSym@{h i j k l} lA Γ A (lrA : [LogRel@{i j k l} lA | Γ ||- A]) : forall t u,
  [Γ ||-<lA> t ≅ u : A |lrA] -> [Γ ||-<lA> u ≅ t : A |lrA].
Proof.
  pattern lA, Γ, A, lrA. apply LR_rect_TyUr.
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
  end.

Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceRefl := irrelevance0 ; [reflexivity|].