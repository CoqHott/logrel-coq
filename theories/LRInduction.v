From MetaCoq.PCUIC Require Import PCUICAst PCUICRenameConv PCUICInstConv PCUICSigmaCalculus.
From LogRel Require Import Notations Untyped Weakening GenericTyping LogicalRelation.

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeu ta}
    `{!OneRedType ta} `{!OneRedTerm ta}.

  #[universes(polymorphic)]Fixpoint LR_embedding {l l'} (l_ : l << l')
    {Γ A rEq rTe rTeEq} (lr : LRl l Γ A rEq rTe rTeEq) {struct lr} : (LRl l' Γ A rEq rTe rTeEq) :=
    match lr with
    | LRU Γ H =>
        match
          (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
        with end
    | LRne _ _ neA => LRne _ neA
    | LRPi _ _ ΠA ΠAad => LRPi _ ΠA
        {|
          PiRedTy.domAd :=
            fun (Δ : context) (ρ : Δ ≤ _) (h : [  |- Δ]) => LR_embedding l_ (ΠAad.(PiRedTy.domAd) ρ h) ;
          PiRedTy.codAd :=
            fun (Δ : context) (a : term) (ρ : Δ ≤ _) (h : [  |- Δ])
              (ha : [PiRedTy.domRed ΠA ρ h | Δ ||- a : _]) =>
            LR_embedding l_ (ΠAad.(PiRedTy.codAd) ρ h ha)
        |}
    end.

  #[universes(polymorphic)]Theorem LR_rect
    (l : TypeLevel)
    (rec : forall l', l' << l -> LogRelKit)
    (P : forall {c t rEq rTe rTeEq},
      LR rec c t rEq rTe rTeEq  -> Type) :

    (forall (Γ : context) (h : [Γ ||-U l]),
      P (LRU rec h)) ->

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec neA)) ->

    (forall (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ]) (HAad : PiRedTyAdequate (LR rec) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) ρ h)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom).[ren ρ] ]),
    P (HAad.(PiRedTy.codAd) ρ h ha)) ->
    P (LRPi rec ΠA HAad)) ->

    forall (Γ : context) (t : term) (rEq rTe : term -> Type)
      (rTeEq  : term -> term -> Type) (lr : LR rec Γ t rEq rTe rTeEq),
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
  Qed.

  Theorem LR_rect_LogRelRec
    (P : forall {l Γ t rEq rTe rTeEq},
    LRl l Γ t rEq rTe rTeEq  -> Type) :

    (forall (Γ : context) (h : [Γ ||-U one]),
      P (LRU (rec1) h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ])
      (HAad : PiRedTyAdequate (LRl l) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (HAad.(PiRedTy.domAd) ρ h)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom).[ren ρ] ]),
    P (HAad.(PiRedTy.codAd) ρ h ha)) ->
    P (LRPi (LogRelRec l) ΠA HAad)) ->

    forall (l : TypeLevel) (Γ : context) (t : term) (rEq rTe : term -> Type)
      (rTeEq  : term -> term -> Type) (lr : LR (LogRelRec l) Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    intros.
    apply LR_rect.
    - intros.
      destruct l.
      2: auto.
      destruct h as [? lt].
      inversion lt.
    - auto.
    - auto.
  Qed.

  Theorem LR_rect_TyUr
    (P : forall {l Γ A}, [Γ ||-< l > A] -> Type) :

    (forall (Γ : context) (h : [Γ ||-U one]),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : [ Γ ||-Πd A ]) (HAad : PiRedTyAdequate (LRl l) ΠA),
    (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
      P (LRbuild (HAad.(PiRedTy.domAd) ρ h))) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom).[ren ρ] ]),
    P (LRbuild (HAad.(PiRedTy.codAd) ρ h ha))) ->
    P (LRPi_ l ΠA HAad)) ->

    forall (l : TypeLevel) (Γ : context) (A : term) (lr : [Γ ||-< l > A]),
      P lr.
  Proof.
    intros HU Hne HPi l Γ A lr.
    apply (LR_rect_LogRelRec (fun l Γ A _ _ _ lr => P l Γ A (LRbuild lr))).
    all: auto.
  Qed.

End Inductions.