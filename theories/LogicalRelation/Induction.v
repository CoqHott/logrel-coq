(** * LogRel.LogicalRelation.Induction: good induction principles for the logical relation. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening UntypedReduction
GenericTyping LogicalRelation.

Set Universe Polymorphism.

(** As Coq is not currently able to define induction principles for nested inductive types
as our LR, we need to prove them by hand. We use this occasion to write down principles which
do not directly correspond to what LR would give us. More precisely, our induction principles:
- handle the two levels uniformly, rather than having to do two separate
  proofs, one at level zero and one at level one;
- apply directly to an inhabitant of the bundled logical relation, rather than the raw LR;
- give a more streamlined minor premise to prove for the case of Π type reducibility,
  which hides the separation needed in LR between the reducibility data and its adequacy
  (ie the two ΠA and ΠAad arguments to constructor LRPi).
Also, and crucially, all induction principles are universe-polymorphic, so that their usage
does not create global constraints on universes. *)

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!TypeNf ta} `{!TypeNe ta} `{!RedTerm ta} `{!TermNf ta} `{!TermNe ta}.

(** ** Embedding *)

(** Reducibility at a lower level implies reducibility at a higher level, and their decoding are the
same. Both need to be proven simultaneously, because of contravariance in the product case. *)
  Fixpoint LR_embedding@{i j k l} {l l'} (l_ : l << l')
    {wl Γ A rEq rTe rTeEq} (lr : LogRel@{i j k l} l wl Γ A rEq rTe rTeEq) {struct lr} :
    (LogRel@{i j k l} l' wl Γ A rEq rTe rTeEq) :=
    let embedΠad {wl Γ A} {ΠA : [Γ ||-Πd A]< wl >} (ΠAad : PiRedTyAdequate _ ΠA) :=
        {|
          PiRedTy.domAd :=
            fun (Δ : context) wl' (ρ : Δ ≤ _) (τ : wl' ≤ε wl) Ninfl (h : [  |- Δ]< wl' >) => LR_embedding l_ (ΠAad.(PiRedTy.domAd) ρ τ Ninfl h) ;
          PiRedTy.codAd :=
            fun (Δ : context) (a : term)  (wl' : wfLCon) (ρ : Δ ≤ _) (τ : wl' ≤ε wl)
                (Ninfl : AllInLCon _  wl') (h : [ |- Δ ]< wl' >) 
                (ha : [PiRedTy.domRed ΠA ρ τ Ninfl h | Δ ||- a : _]< wl' >)
                wl'' (τ' : wl'' ≤ε wl')
                (Minfl : AllInLCon _ wl'')  =>
            LR_embedding l_ (ΠAad.(PiRedTy.codAd) ρ τ Ninfl h ha τ' Minfl)
        |}
    in
    match lr with
    | LRU _ H =>
        match
          (match l_ with Oi => fun H' => elim H'.(URedTy.lt) end H)
        with end
    | LRne _ neA => LRne _ neA
    | LRPi _ ΠA ΠAad => LRPi _ ΠA (embedΠad ΠAad)
    | LRNat _ NA => LRNat _ NA
    | LRBool _ NA => LRBool _ NA
    | LREmpty _ NA => LREmpty _ NA
    end.

  (** A basic induction principle, that handles only the first point in the list above *)

  Notation PiHyp P wl Γ ΠA HAad G :=
    ((forall {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ]< wl' >),
        P (HAad.(PiRedTy.domAd) ρ τ Ninfl h)) ->
     (forall {Δ wl' a} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ ]< wl' >) 
             (ha : [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< wl' >)
             {wl''} (τ' : wl'' ≤ε wl')
             (Minfl : AllInLCon _ wl''),
         P (HAad.(PiRedTy.codAd) ρ τ Ninfl h ha τ' Minfl)) -> G).
        
  Theorem LR_rect@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {wl c t rEq rTe rTeEq},
      LR@{i j k} rec wl c t rEq rTe rTeEq  -> Type@{o}) :

    (forall (wl : wfLCon) (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
      P (LRU rec h)) ->

    (forall (wl : wfLCon) (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne rec neA)) -> 

    (forall (wl : wfLCon) (Γ : context) (A : term)
            (ΠA : PiRedTy@{j} wl Γ A) (HAad : PiRedTyAdequate (LR rec) ΠA),
      PiHyp P wl Γ ΠA HAad (P (LRPi rec ΠA HAad))) ->

    (forall wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat rec NA)) ->

    (forall wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool rec NA)) ->
    
    (forall wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty rec NA)) ->

    forall (wl : wfLCon) (Γ : context) (t : term) (rEq rTe : term -> Type@{j})
           (rTeEq  : term -> term -> Type@{j})
           (lr : LR@{i j k} rec wl Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    cbn.
    intros HU Hne HPi HNat HBool HEmpty.
    fix HRec 7.
    destruct lr.
    - eapply HU.
    - eapply Hne.
    - eapply HPi.
      all: intros ; eapply HRec.
    - eapply HNat.
    - eapply HBool.
    - eapply HEmpty.
  Defined.

  Definition LR_rec@{i j k} := LR_rect@{i j k Set}.
  
  Notation PiHypLogRel P wl Γ ΠA G :=
    ((forall {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ]< wl' >),
         P (ΠA.(PiRedTyPack.domRed) ρ τ Ninfl h).(LRAd.adequate)) ->
    (forall {Δ wl' a} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ ]< wl' >) 
             (ha : [ Δ ||-< _ > a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ |  ΠA.(PiRedTyPack.domRed) ρ τ Ninfl h ]< wl' >)
             {wl''} (τ' : wl'' ≤ε wl')
             (Minfl : AllInLCon _ wl''),
        P (ΠA.(PiRedTyPack.codRed) ρ τ Ninfl h ha τ' Minfl).(LRAd.adequate)) -> G).


  (** Induction principle specialized to LogRel as the reducibility relation on lower levels *)
  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l wl Γ t rEq rTe rTeEq},
    LogRel@{i j k l} l wl Γ t rEq rTe rTeEq -> Type@{o}) :

    (forall l (wl : wfLCon) (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
      P (LRU (LogRelRec l) h)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term)
            (neA : [Γ ||-ne A]< wl >),
      P (LRne (LogRelRec l) neA)) ->

    (forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (A : term)
            (ΠA : PiRedTyPack@{i j k l} wl Γ A l),
      PiHypLogRel P wl Γ ΠA (P (LRPi' ΠA).(LRAd.adequate ))) ->
    
    (forall l wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat (LogRelRec l) NA)) ->
    
    (forall l wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool (LogRelRec l) NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty (LogRelRec l) NA)) ->

    forall (l : TypeLevel) (wl : wfLCon) (Γ : context) (t : term)
           (rEq rTe : term -> Type@{k})
           (rTeEq  : term -> term -> Type@{k})
           (lr : LR@{j k l} (LogRelRec@{i j k} l) wl Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    intros HU Hne HPi **; eapply LR_rect@{j k l o}.
    1,2,4,5,6: auto.
    - intros; eapply (HPi _ _ _ _ (PiRedTyPack.pack ΠA HAad)); eauto.
  Defined.


  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l wl Γ A}, [LogRel@{i j k l} l | Γ ||- A]< wl > -> Type@{o}) :

    (forall l wl (Γ : context) A (h : [Γ ||-U<l> A]< wl >),
      P (LRU_ h)) ->

    (forall (l : TypeLevel) wl (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne_ l neA)) ->

    (forall (l : TypeLevel) wl (Γ : context) (A : term)
            (ΠA : PiRedTyPack@{i j k l} wl Γ A l),
        (forall {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ ]< wl' >),
            P (ΠA.(PiRedTyPack.domRed) ρ τ Ninfl h)) ->
        (forall {Δ wl' a} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ ]< wl' >)
             (ha : [ ΠA.(PiRedTyPack.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTyPack.dom)⟨ρ⟩ ]< wl' >) {wl''} (τ' : wl'' ≤ε wl')
             (Minfl : AllInLCon _ wl''),
            P (ΠA.(PiRedTyPack.codRed) ρ τ Ninfl h ha τ' Minfl)) ->
        P (LRPi' ΠA)) ->

    (forall l wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat_ l NA)) ->
    
    (forall l wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool_ l NA)) ->

    (forall l wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty_ l NA)) ->

    forall (l : TypeLevel) wl (Γ : context) (A : term)
           (lr : [LogRel@{i j k l} l | Γ ||- A]< wl >),
      P lr.
  Proof.
    intros HU Hne HPi HNat HBool HEmpty l wl Γ A lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l wl Γ A _ _ _ lr => P l wl Γ A (LRbuild lr))).
    all: auto.
  Defined.

  Notation PiHyp0 wl P Γ ΠA HAad G :=
    ((forall {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
             (Ninfl : AllInLCon _ wl')
             (h : [ |- Δ]< wl' >),
         P (HAad.(PiRedTy.domAd) ρ τ Ninfl h)) ->
      (forall {Δ wl' a} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
              (Ninfl : AllInLCon _ wl')
              (h : [ |- Δ ]< wl' >) 
              (ha : [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< wl' >)
             {wl''} (τ' : wl'' ≤ε wl')
             (Minfl : AllInLCon _ wl''),
        P (HAad.(PiRedTy.codAd) ρ τ Ninfl h ha τ' Minfl)) -> G).

  

  (** Induction principle specialized at level 0 to minimize universe constraints. *)
  (* Useful anywhere ? *)
  Theorem LR_rect0@{i j k o}
    (P : forall {wl c t rEq rTe rTeEq},
      LogRel0@{i j k} wl c t rEq rTe rTeEq  -> Type@{o}) :

    (forall wl (Γ : context) (A : term) (neA : [Γ ||-ne A]< wl >),
      P (LRne rec0 neA)) -> 
    
    (forall wl (Γ : context) (A : term) (ΠA : PiRedTy@{j} wl Γ A) (HAad : PiRedTyAdequate LogRel0@{i j k} ΠA),
      PiHyp0 wl P Γ ΠA HAad (P (LRPi rec0 ΠA HAad))) ->

    (forall wl Γ A (NA : [Γ ||-Nat A]< wl >), P (LRNat rec0 NA)) ->
    
    (forall wl Γ A (NA : [Γ ||-Bool A]< wl >), P (LRBool rec0 NA)) ->

    (forall wl Γ A (NA : [Γ ||-Empty A]< wl >), P (LREmpty rec0 NA)) ->

    forall wl (Γ : context) (t : term) (rEq rTe : term -> Type@{j})
      (rTeEq  : term -> term -> Type@{j}) (lr : LogRel0@{i j k} wl Γ t rEq rTe rTeEq),
      P lr.
  Proof.
    cbn.
    intros Hne HPi HNat HBool HEmpty.
    fix HRec 7.
    destruct lr.
    - destruct H as [? lt]; destruct (elim lt).
    - eapply Hne.
    - eapply HPi; intros ; eapply HRec.
    - eapply HNat.
    - eapply HBool.
    - eapply HEmpty.
  Defined.

End Inductions.

(** ** Inversion principles *)

Section Inversions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!TypeNf ta} `{!TypeNe ta} `{!RedTerm ta} `{!TermNf ta} `{!TermNe ta} `{!RedTypeProperties}
    `{!TypeNeProperties}.

  Lemma invLR {wl Γ l A A'}
    (lr : [Γ ||-<l> A]< wl >) (r : [A ⇒* A']< wl >) (w : isType A') :
    match w return Type with
    | UnivType => [Γ ||-U<l> A]< wl >
    | ProdType => [Γ ||-Π<l> A]< wl >
    | NatType => [Γ ||-Nat A]< wl >
    | BoolType => [Γ ||-Bool A]< wl >
    | EmptyType => [Γ ||-Empty A]< wl >
    | NeType _ => [Γ ||-ne A]< wl >
    end.
  Proof.
    revert A' r w.
    pattern l, wl, Γ, A, lr ; eapply LR_rect_TyUr; clear l wl Γ A lr.
    - intros * h ? red whA.
      assert (A' = U) as ->.
      {
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, h.
      }
      dependent inversion whA.
      1: assumption.
      exfalso.
      gen_typing.
    - intros * ? A' red whA.
      enough ({w' & whA = NeType w'}) as [? ->] by easy.
      destruct neA as [A'' redA neA''].
      apply ty_ne_whne in neA''.
      assert (A' = A'') as <-.
      + eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
      + dependent inversion whA ; subst.
        all: inv_whne.
        all: now eexists.
    - intros ???? PiA _ _ A' red whA.
      enough (∑ dom cod, A' = tProd cod dom) as (?&?&->).
      + dependent inversion whA ; subst.
        2: exfalso ; gen_typing.
        assumption.
      + destruct PiA as [?? redA].
        do 2 eexists.
        eapply whred_det.
        1-3: gen_typing.
        eapply redty_red, redA.
    - intros ???? [redA] ???.
      enough (A' = tNat) as ->.
      + dependent inversion w. 
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ???? [redA] ???.
      enough (A' = tBool) as ->.
      + dependent inversion w. 
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
    - intros ???? [redA] ???.
      enough (A' = tEmpty) as ->.
      + dependent inversion w. 
        1: now econstructor.
        inv_whne.
      + eapply whred_det; tea.
        all: gen_typing.
  Qed.

  Lemma invLRU {wl Γ l} : [Γ ||-<l> U]< wl > -> [Γ ||-U<l> U]< wl >.
  Proof.
    intros.
    now unshelve eapply (invLR _ redIdAlg (UnivType)).
  Qed.

  Lemma invLRne {wl Γ l A} : whne A -> [Γ ||-<l> A]< wl > -> [Γ ||-ne A]< wl >.
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg (NeType _)).
  Qed.

  Lemma invLRΠ {wl Γ l dom cod} : [Γ ||-<l> tProd dom cod]< wl > -> [Γ ||-Π<l> tProd dom cod]< wl >.
  Proof.
    intros.
    now unshelve eapply  (invLR _ redIdAlg (ProdType)).
  Qed.

  (* invLRNat is useless *)

End Inversions.
