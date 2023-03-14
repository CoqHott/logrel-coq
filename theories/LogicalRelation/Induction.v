From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation.

Set Universe Polymorphism.

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.
  
  Fixpoint LR_embedding@{i j k l} {l l'} (l_ : l << l')
    {Γ A rEq rTe rTeEq} (lr : LogRel@{i j k l} l Γ A rEq rTe rTeEq) {struct lr} : (LogRel@{i j k l} l' Γ A rEq rTe rTeEq) :=
    let embedΠad {Γ A} {ΠA : [Γ ||-Πd A]} (ΠAad : PiRedTyAdequate _ ΠA) :=
        {|
          PiRedTy.domAd :=
            fun (Δ : context) (ρ : Δ ≤ _) (h : [  |- Δ]) => LR_embedding l_ (ΠAad.(PiRedTy.domAd) ρ h) ;
          PiRedTy.codAd :=
            fun (Δ : context) (a : term) (ρ : Δ ≤ _) (h : [  |- Δ])
              (ha : [PiRedTy.domRed ΠA ρ h | Δ ||- a : _]) =>
            LR_embedding l_ (ΠAad.(PiRedTy.codAd) ρ h ha)
        |}
    in
    match lr with
    | LRU _ H =>
        match
          (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
        with end
    | LRne _ neA => LRne _ neA
    | LRPi _ ΠA ΠAad => LRPi _ ΠA (embedΠad ΠAad)
    end.

  Notation PiHyp P Γ ΠA HAad G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
        P (HAad.(PiRedTy.domAd) ρ h)) ->
      (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
        (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
        P (HAad.(PiRedTy.codAd) ρ h ha)) -> G).

  Theorem LR_rect@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {c t rEq rTe rTeEq},
      LR@{i j k} rec c t rEq rTe rTeEq  -> Type@{o}) :

    (forall (Γ : context) A (h : [Γ ||-U<l> A]),
      P (LRU rec h)) ->

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec neA)) -> 

    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
      PiHyp P Γ ΠA HAad (P (LRPi rec ΠA HAad))) ->

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

  Definition LR_rec@{i j k} := LR_rect@{i j k Set}.
  
  Notation PiHypLogRel P Γ ΠA G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PiRedTyPack.domRed) ρ h).(LRAd.adequate)) ->
    (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ Δ ||-< _ > a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ |  ΠA.(PiRedTyPack.domRed) ρ h ]),
      P (ΠA.(PiRedTyPack.codRed) ρ h ha).(LRAd.adequate)) -> G).


  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l Γ t rEq rTe rTeEq},
    LogRel@{i j k l} l Γ t rEq rTe rTeEq -> Type@{o}) :

    (forall l (Γ : context) A (h : [Γ ||-U<l> A]),
      P (LRU (LogRelRec l) h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTyPack@{i j k l} Γ A l),
      PiHypLogRel P Γ ΠA (P (LRPi' ΠA).(LRAd.adequate ))) ->

    forall (l : TypeLevel) (Γ : context) (t : term) (rEq rTe : term -> Type@{k})
      (rTeEq  : term -> term -> Type@{k}) (lr : LR@{j k l} (LogRelRec@{i j k} l) Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    intros HU Hne HPi **; eapply LR_rect@{j k l o}.
    1,2: auto.
    - intros; eapply (HPi _ _ _ (PiRedTyPack.pack ΠA HAad)); eauto.
  Defined.


  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l Γ A}, [LogRel@{i j k l} l | Γ ||- A] -> Type@{o}) :

    (forall l (Γ : context) A (h : [Γ ||-U<l> A]),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A : term) (ΠA : PiRedTyPack@{i j k l} Γ A l),
      (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PiRedTyPack.domRed) ρ h)) ->
      (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
       (ha : [ ΠA.(PiRedTyPack.domRed) ρ h | Δ ||- a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ ]),
      P (ΠA.(PiRedTyPack.codRed) ρ h ha)) ->
    P (LRPi' ΠA)) ->

    forall (l : TypeLevel) (Γ : context) (A : term) (lr : [LogRel@{i j k l} l | Γ ||- A]),
      P lr.
  Proof.
    intros HU Hne HPi l Γ A lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l Γ A _ _ _ lr => P l Γ A (LRbuild lr))).
    1-3: auto.
  Defined.

  Notation PiHyp0 P Γ ΠA HAad G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]),
        P (HAad.(PiRedTy.domAd) ρ h)) ->
      (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
        (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
        P (HAad.(PiRedTy.codAd) ρ h ha)) -> G).


  (* Induction principle specialized at level 0 to minimize universe constraints *)
  (* Useful anywhere ? *)
  Theorem LR_rect0@{i j k o}
    (P : forall {c t rEq rTe rTeEq},
      LogRel0@{i j k} c t rEq rTe rTeEq  -> Type@{o}) :

    (forall (Γ : context) (A : term) (neA : [Γ ||-ne A]),
      P (LRne rec0 neA)) -> 
    
    (forall (Γ : context) (A : term) (ΠA : PiRedTy@{j} Γ A) (HAad : PiRedTyAdequate LogRel0@{i j k} ΠA),
      PiHyp0 P Γ ΠA HAad (P (LRPi rec0 ΠA HAad))) ->

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
    - eapply HPi; intros ; eapply HRec.
  Defined.

End Inductions.


Section Inversions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta} `{!RedTypeProperties}.

  Lemma invLR {Γ l A} (lr : [Γ ||-<l> A]) : 
    whnf A ->
    match A return Type with
    | tSort _ => [Γ ||-U<l> A]
    | tProd _ _ _ => [Γ ||-Π<l> A]
    | _ => [Γ ||-ne A]
    end.
  Proof.
    pattern l, Γ, A, lr; eapply LR_rect_TyUr; clear l Γ A lr.
    + intros * h whA.
      epose proof (redtywf_whnf (URedTy.red h) whA); subst; assumption.
    + intros * h whA. pose (h' := h); destruct h' as [ty r ne].
      pose proof (redtywf_whnf r whA); subst.
      destruct ty; inversion ne; eassumption.
    + intros ??? h _ _ whA. pose (h' := h); destruct h' as [??? r].
      pose proof (redtywf_whnf r whA); subst. eassumption.
  Qed.

  Lemma invLRU {Γ l} : [Γ ||-<l> U] -> [Γ ||-U<l> U].
  Proof.
    intros h;  eapply (invLR h); constructor.
  Qed.

  Lemma invLRne {Γ l A} : whne A -> [Γ ||-<l> A] -> [Γ ||-ne A].
  Proof.
    intros ne h. epose proof (invLR h (whnf_whne ne)).
    destruct A; inversion ne; assumption.
  Qed.

  Lemma invLRΠ {Γ l na dom cod} : [Γ ||-<l> tProd na dom cod] -> [Γ ||-Π<l> tProd na dom cod].
  Proof.
    intros h; eapply (invLR h); constructor.
  Qed.

End Inversions.