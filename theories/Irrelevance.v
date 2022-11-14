From MetaCoq Require Import PCUICAst.
Require Import Utils Automation Untyped MLTTTyping LogicalRelation Properties Reduction LRInduction ShapeView Reflexivity.

Lemma ΠIrrelevanceTyEq Γ A A' na na' dom dom' cod cod'
  (domTy : [Γ |- dom])
  (codTy : [Γ,, vass na dom |- cod])
  (red : [Γ |- A :⇒*: tProd na dom cod])
  (domRed : forall Δ : context, [  |- Δ] -> LRPack Δ dom)
  (codRed : forall (Δ : context) (a : term) (h : [  |- Δ]),
            [domRed Δ h | Δ ||- a : dom] -> LRPack Δ (cod {0 := a}))
  (codExt : forall (Δ : context) (a b : term) (h : [  |- Δ])
              (ha : [domRed Δ h | Δ ||- a : dom]),
            [domRed Δ h | Δ ||- b : dom] ->
            [domRed Δ h | Δ ||- a ≅ b : dom] ->
            [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ cod{0 := b}])
  (domTy': [Γ |- dom'])
  (codTy': [Γ,, vass na' dom' |- cod'])
  (red': [Γ |- A' :⇒*: tProd na' dom' cod'])
  (domRed': forall Δ : context, [  |- Δ] -> LRPack Δ dom')
  (codRed': forall (Δ : context) (a : term) (h : [  |- Δ]),
            [domRed' Δ h | Δ ||- a : dom'] -> LRPack Δ (cod' {0 := a}))
  (codExt': forall (Δ : context) (a b : term) (h : [  |- Δ])
              (ha : [domRed' Δ h | Δ ||- a : dom']),
            [domRed' Δ h | Δ ||- b : dom'] ->
            [domRed' Δ h | Δ ||- a ≅ b : dom'] ->
            [codRed' Δ a h ha | Δ ||- cod'{0 := a} ≅ cod'{0 := b}])
  (eqPi : [Γ |- tProd na dom cod ≅ tProd na' dom' cod']) :
  
  (forall (Δ : context) (h : [  |- Δ]),
  [× (forall B : term,
      [domRed Δ h | Δ ||- dom ≅ B] <-> [domRed' Δ h | Δ ||- dom' ≅ B]),
    (forall t : term,
      [domRed Δ h | Δ ||- t : dom] <-> [domRed' Δ h | Δ ||- t : dom']) &
    (forall t u : term,
      [domRed Δ h | Δ ||- t ≅ u : dom ] <-> [domRed' Δ h | Δ ||- t ≅ u : dom'])]) ->
  (forall (Δ : context) (a : term) (h : [  |- Δ])
      (ha : [domRed Δ h | Δ ||- a : dom])
      (ha' : [domRed' Δ h | Δ ||- a : dom']),
  [× (forall B : term,
      [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ B] <->
      [codRed' Δ a h ha' | Δ ||- cod'{0 := a} ≅ B]),
    (forall t : term,
      [codRed Δ a h ha | Δ ||- t : cod{0 := a} ] <->
      [codRed' Δ a h ha' | Δ ||- t : cod'{0 := a} ]) &
    (forall t u : term,
      [codRed Δ a h ha | Δ ||- t ≅ u : cod{0 := a} ] <->
      [codRed' Δ a h ha' | Δ ||- t ≅ u : cod'{0 := a} ])]) ->
  let ΠA : PiRedTy Γ A := {|
      PiRedTy.na := na ; PiRedTy.dom := dom ;
      PiRedTy.cod := cod ;
      PiRedTy.red := red ;
      PiRedTy.domTy := domTy ;
      PiRedTy.codTy := codTy ;
      PiRedTy.domRed := domRed ;
      PiRedTy.codRed := codRed ;
      PiRedTy.codExt := codExt
        |} in
  let ΠA' : PiRedTy Γ A' := {|
    PiRedTy.na := na' ; PiRedTy.dom := dom' ;
    PiRedTy.cod := cod' ;
    PiRedTy.red := red' ;
    PiRedTy.domTy := domTy' ;
    PiRedTy.codTy := codTy' ;
    PiRedTy.domRed := domRed' ;
    PiRedTy.codRed := codRed' ;
    PiRedTy.codExt := codExt'
      |} in
  forall B, [Γ ||-Π A ≅ B | ΠA] -> [Γ ||-Π A' ≅ B | ΠA'].
Proof.
  intros IHdom IHcod ΠA ΠA' B [] ; cbn in *.
  econstructor.
  1-2: now mltt.
  1: intros ; now apply IHdom.
  intros.
  cbn in *.
  unshelve eapply IHcod.
  2: eauto.
  now eapply IHdom.
Qed.

Lemma ΠIrrelevanceTm Γ A na dom cod A' na' dom' cod'
  (domTy : [Γ |- dom])
  (codTy : [Γ,, vass na dom |- cod])
  (red : [Γ |- A :⇒*: tProd na dom cod])
  (domRed : forall Δ : context, [  |- Δ] -> LRPack Δ dom)
  (codRed : forall (Δ : context) (a : term) (h : [  |- Δ]),
            [domRed Δ h | Δ ||- a : dom] -> LRPack Δ (cod {0 := a}))
  (codExt : forall (Δ : context) (a b : term) (h : [  |- Δ])
              (ha : [domRed Δ h | Δ ||- a : dom]),
            [domRed Δ h | Δ ||- b : dom] ->
            [domRed Δ h | Δ ||- a ≅ b : dom] ->
            [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ cod{0 := b}])
  (domTy': [Γ |- dom'])
  (codTy': [Γ,, vass na' dom' |- cod'])
  (red': [Γ |- A' :⇒*: tProd na' dom' cod'])
  (domRed': forall Δ : context, [  |- Δ] -> LRPack Δ dom')
  (codRed': forall (Δ : context) (a : term) (h : [  |- Δ]),
            [domRed' Δ h | Δ ||- a : dom'] -> LRPack Δ (cod' {0 := a}))
  (codExt': forall (Δ : context) (a b : term) (h : [  |- Δ])
              (ha : [domRed' Δ h | Δ ||- a : dom']),
            [domRed' Δ h | Δ ||- b : dom'] ->
            [domRed' Δ h | Δ ||- a ≅ b : dom'] ->
            [codRed' Δ a h ha | Δ ||- cod'{0 := a} ≅ cod'{0 := b}])
  (eqPi : [Γ |- tProd na dom cod ≅ tProd na' dom' cod']) :
  
  (forall (Δ : context) (h : [  |- Δ]),
  [× (forall B : term,
      [domRed Δ h | Δ ||- dom ≅ B] <-> [domRed' Δ h | Δ ||- dom' ≅ B]),
    (forall t : term,
      [domRed Δ h | Δ ||- t : dom] <-> [domRed' Δ h | Δ ||- t : dom']) &
    (forall t u : term,
      [domRed Δ h | Δ ||- t ≅ u : dom ] <-> [domRed' Δ h | Δ ||- t ≅ u : dom'])]) ->
  (forall (Δ : context) (a : term) (h : [  |- Δ])
      (ha : [domRed Δ h | Δ ||- a : dom])
      (ha' : [domRed' Δ h | Δ ||- a : dom']),
  [× (forall B : term,
      [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ B] <->
      [codRed' Δ a h ha' | Δ ||- cod'{0 := a} ≅ B]),
    (forall t : term,
      [codRed Δ a h ha | Δ ||- t : cod{0 := a} ] <->
      [codRed' Δ a h ha' | Δ ||- t : cod'{0 := a} ]) &
    (forall t u : term,
      [codRed Δ a h ha | Δ ||- t ≅ u : cod{0 := a} ] <->
      [codRed' Δ a h ha' | Δ ||- t ≅ u : cod'{0 := a} ])]) ->
  let ΠA : PiRedTy Γ A := {|
      PiRedTy.na := na ; PiRedTy.dom := dom ;
      PiRedTy.cod := cod ;
      PiRedTy.red := red ;
      PiRedTy.domTy := domTy ;
      PiRedTy.codTy := codTy ;
      PiRedTy.domRed := domRed ;
      PiRedTy.codRed := codRed ;
      PiRedTy.codExt := codExt
        |} in
  let ΠA' : PiRedTy Γ A' := {|
    PiRedTy.na := na' ; PiRedTy.dom := dom' ;
    PiRedTy.cod := cod' ;
    PiRedTy.red := red' ;
    PiRedTy.domTy := domTy' ;
    PiRedTy.codTy := codTy' ;
    PiRedTy.domRed := domRed' ;
    PiRedTy.codRed := codRed' ;
    PiRedTy.codExt := codExt'
      |} in
  forall t, [Γ ||-Π t : A | ΠA] -> [Γ ||-Π t : A' | ΠA'].
Proof.
  intros IHdom IHcod ΠA ΠA' B [] ; cbn in *.
  econstructor.
  1-3: now mltt.
  - intros.
    unshelve eapply IHcod.
    2: now auto.
    now apply IHdom.
  - intros.
    unshelve eapply IHcod, eq.
    all: now eapply IHdom.
Qed.

Lemma ΠIrrelevanceTmEq Γ A na dom cod A' na' dom' cod'
  (domTy : [Γ |- dom])
  (codTy : [Γ,, vass na dom |- cod])
  (red : [Γ |- A :⇒*: tProd na dom cod])
  (domRed : forall Δ : context, [  |- Δ] -> LRPack Δ dom)
  (codRed : forall (Δ : context) (a : term) (h : [  |- Δ]),
            [domRed Δ h | Δ ||- a : dom] -> LRPack Δ (cod {0 := a}))
  (codExt : forall (Δ : context) (a b : term) (h : [  |- Δ])
              (ha : [domRed Δ h | Δ ||- a : dom]),
            [domRed Δ h | Δ ||- b : dom] ->
            [domRed Δ h | Δ ||- a ≅ b : dom] ->
            [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ cod{0 := b}])
  (domTy': [Γ |- dom'])
  (codTy': [Γ,, vass na' dom' |- cod'])
  (red': [Γ |- A' :⇒*: tProd na' dom' cod'])
  (domRed': forall Δ : context, [  |- Δ] -> LRPack Δ dom')
  (codRed': forall (Δ : context) (a : term) (h : [  |- Δ]),
            [domRed' Δ h | Δ ||- a : dom'] -> LRPack Δ (cod' {0 := a}))
  (codExt': forall (Δ : context) (a b : term) (h : [  |- Δ])
              (ha : [domRed' Δ h | Δ ||- a : dom']),
            [domRed' Δ h | Δ ||- b : dom'] ->
            [domRed' Δ h | Δ ||- a ≅ b : dom'] ->
            [codRed' Δ a h ha | Δ ||- cod'{0 := a} ≅ cod'{0 := b}])
  (eqPi : [Γ |- tProd na dom cod ≅ tProd na' dom' cod']) :
  
  (forall (Δ : context) (h : [  |- Δ]),
  [× (forall B : term,
      [domRed Δ h | Δ ||- dom ≅ B] <-> [domRed' Δ h | Δ ||- dom' ≅ B]),
    (forall t : term,
      [domRed Δ h | Δ ||- t : dom] <-> [domRed' Δ h | Δ ||- t : dom']) &
    (forall t u : term,
      [domRed Δ h | Δ ||- t ≅ u : dom ] <-> [domRed' Δ h | Δ ||- t ≅ u : dom'])]) ->
  (forall (Δ : context) (a : term) (h : [  |- Δ])
      (ha : [domRed Δ h | Δ ||- a : dom])
      (ha' : [domRed' Δ h | Δ ||- a : dom']),
  [× (forall B : term,
      [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ B] <->
      [codRed' Δ a h ha' | Δ ||- cod'{0 := a} ≅ B]),
    (forall t : term,
      [codRed Δ a h ha | Δ ||- t : cod{0 := a} ] <->
      [codRed' Δ a h ha' | Δ ||- t : cod'{0 := a} ]) &
    (forall t u : term,
      [codRed Δ a h ha | Δ ||- t ≅ u : cod{0 := a} ] <->
      [codRed' Δ a h ha' | Δ ||- t ≅ u : cod'{0 := a} ])]) ->
  let ΠA : PiRedTy Γ A := {|
      PiRedTy.na := na ; PiRedTy.dom := dom ;
      PiRedTy.cod := cod ;
      PiRedTy.red := red ;
      PiRedTy.domTy := domTy ;
      PiRedTy.codTy := codTy ;
      PiRedTy.domRed := domRed ;
      PiRedTy.codRed := codRed ;
      PiRedTy.codExt := codExt
       |} in
  let ΠA' : PiRedTy Γ A' := {|
    PiRedTy.na := na' ; PiRedTy.dom := dom' ;
    PiRedTy.cod := cod' ;
    PiRedTy.red := red' ;
    PiRedTy.domTy := domTy' ;
    PiRedTy.codTy := codTy' ;
    PiRedTy.domRed := domRed' ;
    PiRedTy.codRed := codRed' ;
    PiRedTy.codExt := codExt'
     |} in
  forall t u, [Γ ||-Π t ≅ u : A | ΠA] -> [Γ ||-Π t ≅ u : A' | ΠA'].
Proof.
  intros IHdom IHcod ΠA ΠA' t u [] ; cbn in *.
  unshelve econstructor.
  - now eapply ΠIrrelevanceTm.
  - now eapply ΠIrrelevanceTm.
  - cbn.
    mltt.
  - intros.
    unshelve eapply IHcod.
    2: now auto.
    now apply IHdom.
Qed.

Theorem LRIrrelevant Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
    (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A' eqTyA' redTmA' eqTmA') :
    eqTyA A' ->
    [× forall B, eqTyA B <-> eqTyA' B ,
    forall t, redTmA t <-> redTmA' t &
    forall t u, eqTmA t u <-> eqTmA' t u ].
Proof.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? [? []] | ? ? [] | ? A [] [] IHdom IHcod]
    using LR_rect in lA', A', eqTyA', eqTmA', redTmA', lrA', he, s |- *.
  - destruct lrA' as [? [? []] | | ]; try solve [destruct s] ; clear s.
    split.
    + intros ?.
      split.
      all: eauto.
    + intros ?.
      split.
      all: intros [].
      all: now econstructor.
    + intros ? ?.
      split.
      all: intros [[] []].
      all: unshelve econstructor ; tea.
      1-4: now econstructor.
      all: eassumption.
  - destruct lrA' as [|? A' neA'|] ; try solve [destruct s] ; clear s.
    destruct he as [AA], neA' as [AA'] ; cbn in *.
    assert (AA' = AA) as ->
      by (eapply nred_det_ty ; mltt).
    split.
    + intros ?.
      split.
      all: intros [].
      all: econstructor.
      all: now mltt.
    + intros ?.
      split.
      all: intros [].
      all: econstructor.
      all: now mltt.
    + intros ? ?.
      split.
      all: intros [].
      all: econstructor.
      all: cbn in *.
      1-2,6-7: now eapply TermRedWFConv ; mltt.
      1-2,4-5: eassumption.
      all: assert [Γ |- A ≅ A'] by (eapply TypeTrans ; mltt).
      all: now mltt.
  - destruct lrA' as [| | ? A' [] []] ; try solve [destruct s] ; clear s.
    destruct he ; cbn -[subst1] in *.
    assert (redPi0 = redPi1) as ePi
      by (eapply nred_det_ty ; mltt).
    subst redPi redPi0 redPi1.
    inversion ePi ; subst ; clear ePi.
    pose proof (IHdom_ := fun Δ h => IHdom Δ h _ _ _ _ _ (domAd0 Δ h) (domRed1 Δ h)).
    assert (IHcod_ : forall Δ a (h : [ |- Δ])
      (ha : [domRed Δ h | Δ ||- a : dom])
      (ha' : [domRed0 Δ h | Δ ||- a : dom1]),
      [×
        (forall B,
          [codRed Δ a h ha | Δ ||- cod{0 := a} ≅ B] <->
          [codRed0 Δ a h ha' | Δ ||- cod1{0 := a} ≅ B]),
        (forall t,
          [codRed Δ a h ha | Δ ||- t : cod{0 := a}] <->
          [codRed0 Δ a h ha' | Δ ||- t : cod1{0 := a}]) &
      (forall t u,
        [codRed Δ a h ha | Δ ||- t ≅ u : cod{0 := a}] <->
        [codRed0 Δ a h ha' | Δ ||- t ≅ u : cod1{0 := a}])
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
      1,4: mltt.
      1-2: now eauto.
      * do 2 split ; intros.
        all: now eapply IHdom_ ; eauto.
      * do 2 split ; intros.
        all: now eapply IHcod_ ; eauto.
    + split ; intros.
      all: eapply ΠIrrelevanceTm.
      4,8: eassumption.
      1,4: mltt.
      1-2: now eauto.
      * do 2 split ; intros.
        all: now eapply IHdom_ ; eauto.
      * do 2 split ; intros.
        all: now eapply IHcod_ ; eauto.
    + split ; intros.
      all: eapply ΠIrrelevanceTmEq.
      4,8: eassumption.
      1,4: mltt.
      1-2: now eauto.
      * do 2 split ; intros.
        all: now eapply IHdom_ ; eauto.
      * do 2 split ; intros.
        all: now eapply IHcod_ ; eauto.
Qed.

Corollary TyEqIrrelevant Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A eqTyA' redTmA' eqTmA') :
  forall B, eqTyA B -> eqTyA' B.
Proof.
  apply (LRIrrelevant _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqIrrelevant lA lA' Γ A (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A ≅ B | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqIrrelevant.
Qed.

Corollary RedTmIrrelevant Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A eqTyA' redTmA' eqTmA') :
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevant _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmRedIrrelevant lA lA' Γ A (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A]) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmIrrelevant.
Qed.

Corollary TmEqIrrelevant Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A eqTyA' redTmA' eqTmA') :
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevant _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmEqIrrelevant lA lA' Γ A (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqIrrelevant.
Qed.


Corollary TyEqSym Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' -> eqTyA' A.
Proof.
  intros.
  apply (LRIrrelevant _ _ _ lrA lrA').
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
  (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevant _ _ _ lrA lrA').
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
  (lrA : LRl lA Γ A eqTyA redTmA eqTmA) (lrA' : LRl lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevant _ _ _ lrA lrA').
Qed.

Corollary LRTmEqRedConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqRedConv.
Qed.