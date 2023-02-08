From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation.

Set Universe Polymorphism.

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Fixpoint LR_embedding@{i j k l} {l l'} (l_ : l << l')
    {Γ A rEq rTe rTeEq} (lr : LogRel@{i j k l} l Γ A rEq rTe rTeEq) {struct lr} : (LogRel@{i j k l} l' Γ A rEq rTe rTeEq) :=
    match lr with
    | LRU _ H =>
        match
          (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
        with end
    | LRne _ neA => LRne _ neA
    | LRPi _ ΠA ΠAad => LRPi _ ΠA
        {|
          PiRedTy.domAd :=
            fun (Δ : context) (ρ : Δ ≤ _) (h : [  |- Δ]) => LR_embedding l_ (ΠAad.(PiRedTy.domAd) ρ h) ;
          PiRedTy.codAd :=
            fun (Δ : context) (a : term) (ρ : Δ ≤ _) (h : [  |- Δ])
              (ha : [PiRedTy.domRed ΠA ρ h | Δ ||- a : _]) =>
            LR_embedding l_ (ΠAad.(PiRedTy.codAd) ρ h ha)
        |}
    end.

  Theorem LR_rect@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {c t rEq rTe rTeEq},
      LR@{i j k} rec c t rEq rTe rTeEq  -> Type@{o}) :

    (forall (Γ : context) (h : [Γ ||-U l]),
      P (LRU rec h)) ->

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec neA)) -> 

    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) ρ h)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
    P (HAad.(PiRedTy.codAd) ρ h ha)) ->
    P (LRPi rec ΠA HAad)) ->

    forall (Γ : context) (t : term) (rEq rTe : term -> Type@{j})
      (rTeEq  : term -> term -> Type@{j}) (lr : LR@{i j k} rec Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    cbn.
    intros HU Hne HPi.
    fix HRec 6.
    destruct lr.
    - eapply HU.
    - eapply Hne.
    - eapply HPi.
      all: intros ; eapply HRec.
  Defined.

  Lemma LR_rect_Π_eq@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {c t rEq rTe rTeEq},
      LR@{i j k} rec c t rEq rTe rTeEq  -> Type@{o})
    (hU : forall (Γ : context) (h : [Γ ||-U l]), P (LRU rec h))
    (hne : forall (Γ : context) (A : term) (neA : [Γ ||-ne A]), P (LRne rec neA))
    (hΠ : forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
      (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (HAad.(PiRedTy.domAd) ρ h)) ->
      (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
      P (HAad.(PiRedTy.codAd) ρ h ha)) ->
      P (LRPi rec ΠA HAad)) :
    forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
    let ihdom {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]) : P (HAad.(PiRedTy.domAd) ρ h) :=
      LR_rect l rec (@P) hU hne hΠ _ _ _ _ _ (HAad.(PiRedTy.domAd) ρ h)
    in
    let ihcod {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      : P (HAad.(PiRedTy.codAd) ρ h ha) :=
      LR_rect l rec (@P) hU hne hΠ _ _ _ _ _ (HAad.(PiRedTy.codAd) ρ h ha)
    in
    LR_rect l rec (@P) hU hne hΠ Γ A _ _ _ (LRPi rec ΠA HAad) = hΠ Γ A ΠA HAad (@ihdom) (@ihcod).
  Proof. intros; reflexivity. Qed.


  Theorem LR_rec@{i j k}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {c t rEq rTe rTeEq},
      LR@{i j k} rec c t rEq rTe rTeEq  -> Set) :

    (forall (Γ : context) (h : [Γ ||-U l]),
      P (LRU rec h)) ->

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec neA)) ->

    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) ρ h)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
    P (HAad.(PiRedTy.codAd) ρ h ha)) ->
    P (LRPi rec ΠA HAad)) ->

    forall (Γ : context) (t : term) (rEq rTe : term -> Type@{j})
      (rTeEq  : term -> term -> Type@{j}) (lr : LR@{i j k} rec Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    intros.
    now apply LR_rect.
  Defined.

  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l Γ t rEq rTe rTeEq},
    LogRel@{i j k l} l Γ t rEq rTe rTeEq -> Type@{o}) :

    (forall l (Γ : context) (h : [Γ ||-U l]),
      P (LRU (LogRelRec l) h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTy@{k} Γ A)
      (HAad : PiRedTyAdequate (LogRel l) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) ρ h)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
    P (HAad.(PiRedTy.codAd) ρ h ha)) ->
    P (LRPi (LogRelRec l) ΠA HAad)) ->

    forall (l : TypeLevel) (Γ : context) (t : term) (rEq rTe : term -> Type@{k})
      (rTeEq  : term -> term -> Type@{k}) (lr : LR@{j k l} (LogRelRec@{i j k} l) Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    intros.
    eapply LR_rect@{j k l o}; auto.
    (* - intros. clear lr. (* this is important for unfold equations *) destruct l.
      2: auto.
      destruct (elim (URedTy.lt h)).
    - auto.
    - auto. *)
  Defined.

  Lemma LR_rect_LogRelRecΠ_eq@{i j k l o}
    (P : forall {l Γ t rEq rTe rTeEq}, LogRel@{i j k l} l Γ t rEq rTe rTeEq -> Type@{o})
    (hU : forall l (Γ : context) (h : [Γ ||-U l]), P (LRU (LogRelRec l) h))
    (hne : forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]), P (LRne (LogRelRec l) neA))

    (hΠ : forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTy@{k} Γ A) 
      (HAad : PiRedTyAdequate (LogRel l) ΠA)
      (ihdom : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (HAad.(PiRedTy.domAd) ρ h))
      (ihcod : forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
        P (HAad.(PiRedTy.codAd) ρ h ha)),
    P (LRPi (LogRelRec l) ΠA HAad)) :
    forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTy@{k} Γ A) 
      (HAad : PiRedTyAdequate (LogRel l) ΠA),
      let ihdom {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]) : P (HAad.(PiRedTy.domAd) ρ h) :=
        LR_rect_LogRelRec (@P) hU hne hΠ _ _ _ _ _ _ (HAad.(PiRedTy.domAd) ρ h)
      in
      let ihcod {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]) :
        P (HAad.(PiRedTy.codAd) ρ h ha) :=
        LR_rect_LogRelRec (@P) hU hne hΠ _ _ _ _ _ _ (HAad.(PiRedTy.codAd) ρ h ha)
      in
      LR_rect_LogRelRec (@P) hU hne hΠ _ _ _ _ _ _ (LRPi (LogRelRec l) ΠA HAad) =
      hΠ l Γ A ΠA HAad (@ihdom) (@ihcod).
  Proof. reflexivity. Qed. 

  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l Γ A}, [LogRel@{i j k l} l | Γ ||- A] -> Type@{o}) :

    (forall l (Γ : context) (h : [Γ ||-U l]),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTyPack@{i j k l} Γ A l),
      (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PiRedTyPack.domRed) ρ h)) ->
      (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
       (ha : [ ΠA.(PiRedTyPack.domRed) ρ h | Δ ||- a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ ]),
      P (ΠA.(PiRedTyPack.codRed) ρ h ha)) ->
    P (LRPi' l ΠA)) ->
    (* (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTy@{k} Γ A) (HAad : PiRedTyAdequate (LogRel l) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (LRbuild (HAad.(PiRedTy.domAd) ρ h))) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
    P (LRbuild (HAad.(PiRedTy.codAd) ρ h ha))) ->
    P (LRPi_ l ΠA HAad)) -> *)

    forall (l : TypeLevel) (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]),
      P lr.
  Proof.
    intros HU Hne HPi l Γ A lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l Γ A _ _ _ lr => P l Γ A (LRbuild lr))).
    1,2: auto.
    intros; eapply (HPi _ _ _ (PiRedTyPack.pack ΠA HAad)); eauto.    
  Defined.

  Theorem LR_rect_TyUr_Π_eq@{i j k l o}
    (P : forall {l Γ A}, [LogRel@{i j k l} l | Γ ||- A] -> Type@{o})
    (hU : forall l (Γ : context) (h : [Γ ||-U l]), P (LRU_ h))
    (hne : forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]), P (LRne_ l neA))
    (hΠ : forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTyPack@{i j k l} Γ A l)
      (ihdom : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PiRedTyPack.domRed) ρ h))
      (ihcod : forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
        (ha : [ ΠA.(PiRedTyPack.domRed) ρ h | Δ ||- a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ ]),
        P (ΠA.(PiRedTyPack.codRed) ρ h ha)),
      P (LRPi' l ΠA)) :
    forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTyPack@{i j k l} Γ A l),
      let ihdom {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]) : P (ΠA.(PiRedTyPack.domRed) ρ h) :=
        LR_rect_TyUr (@P) hU hne hΠ _ _ _ (ΠA.(PiRedTyPack.domRed) ρ h)
      in
      let ihcod {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
        (ha : [ ΠA.(PiRedTyPack.domRed) ρ h | Δ ||- a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ ]) :
        P (ΠA.(PiRedTyPack.codRed) ρ h ha) :=
        LR_rect_TyUr (@P) hU hne hΠ _ _ _ (ΠA.(PiRedTyPack.codRed) ρ h ha)
      in
      LR_rect_TyUr (@P) hU hne hΠ _ _ _ (LRPi' l ΠA) = hΠ l Γ A ΠA (@ihdom) (@ihcod).
    Proof.
      reflexivity.
    Qed. 


  (* Induction principle specialized at level 0 to minimize universe constraints *)
  (* Useful anywhere ? *)
  Theorem LR_rect0@{i j k o}
    (P : forall {c t rEq rTe rTeEq},
      LogRel0@{i j k} c t rEq rTe rTeEq  -> Type@{o}) :

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec0 neA)) -> 

    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LogRel0@{i j k}) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) ρ h)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
    P (HAad.(PiRedTy.codAd) ρ h ha)) ->
    P (LRPi rec0 ΠA HAad)) ->

    forall (Γ : context) (t : term) (rEq rTe : term -> Type@{j})
      (rTeEq  : term -> term -> Type@{j}) (lr : LogRel0@{i j k} Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    cbn.
    intros Hne HPi.
    fix HRec 6.
    destruct lr.
    - destruct H as [? lt]; destruct (elim lt).
    - eapply Hne.
    - eapply HPi.
      all: intros ; eapply HRec.
  Defined.

  Theorem LR_rect_TyUr0@{i j k o}
    (P : forall {Γ A}, [LogRel0@{i j k} | Γ ||- A] -> Type@{o}) :

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRbuild0@{i j k} (LRne@{i j k} rec0 neA))) ->

    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate LogRel0 ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (LRbuild0@{i j k} (HAad.(PiRedTy.domAd) ρ h))) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
    P (LRbuild0@{i j k} (HAad.(PiRedTy.codAd) ρ h ha))) ->
    P (LRbuild0@{i j k} (LRPi rec0 ΠA HAad))) ->

    forall (Γ : context) (A : term) (lr : [LogRel0@{i j k} | Γ ||- A]),
      P lr.
  Proof.
    intros Hne HPi Γ A lr.
    apply (LR_rect0 (fun Γ A _ _ _ lr => P Γ A (LRbuild0 lr))).
    all: auto.
  Defined.

End Inductions.
