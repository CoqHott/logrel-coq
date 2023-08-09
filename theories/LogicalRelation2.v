(** * LogRel.LogicalRelation: Definition of the logical relation *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening GenericTyping Monad2.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Create HintDb logrel.
#[global] Hint Constants Opaque : logrel.
#[global] Hint Variables Transparent : logrel.
Ltac logrel := eauto with logrel.

(** Note: modules are used as a hackish solution to provide a form of namespaces for record projections. *)

(** ** Preliminaries *)

(** Instead of using induction-recursion, we encode simultaneously the fact that a type is reducible,
  and the graph of its decoding, as a single inductive relation.
  Concretely, the type of our reducibility relation is the following RedRel:
  for some R : RedRel, R Γ A eqTy redTm eqTm says
  that according to R, A is reducible in Γ and the associated reducible type equality
  (resp. term reducibility, term reducible equality) are eqTy (resp. redTm eqTm).
  One should think of RedRel as a functional relation taking two arguments (Γ and A) and returning
  three outputs (eqTy, redTm and eqTm). *)

  Definition RedRel@{i j} :=
  wfLCon               ->
  context               ->
  term                  ->
  (term -> Type@{i})         ->
  (term -> Type@{i})         ->
  (term -> term -> Type@{i}) ->
  Type@{j}.

(** An LRPack contains the data corresponding to the codomain of RedRel seen as a functional relation. *)

Module LRPack.

  Record LRPack@{i} {l : wfLCon} {Γ : context} {A : term} :=
  {
    eqTy : term -> Type@{i};
    redTm : term -> Type@{i};
    eqTm :  term -> term -> Type@{i};
  }.

  Arguments LRPack : clear implicits.

End LRPack.

Export LRPack(LRPack,Build_LRPack).

Notation "[ P | Γ ||- A ≅ B ]< l >" := (@LRPack.eqTy l Γ A P B).
Notation "[ P | Γ ||- t : A ]< l >" := (@LRPack.redTm l Γ A P t).
Notation "[ P | Γ ||- t ≅ u : A ]< l >" := (@LRPack.eqTm l Γ A P t u).

(** An LRPack is adequate wrt. a RedRel when its three unpacked components are. *)
Definition LRPackAdequate@{i j} {l : wfLCon} {Γ : context} {A : term}
  (R : RedRel@{i j}) (P : LRPack@{i} l Γ A) : Type@{j} :=
  R l Γ A P.(LRPack.eqTy) P.(LRPack.redTm) P.(LRPack.eqTm).

Arguments LRPackAdequate _ _ _ /.

Module LRAd.
  
  Record > LRAdequate@{i j} {l : wfLCon} {Γ : context} {A : term} {R : RedRel@{i j}} : Type :=
  {
    pack :> LRPack@{i} l Γ A ;
    adequate :> LRPackAdequate@{i j} R pack
  }.

  Arguments LRAdequate : clear implicits.
  Arguments Build_LRAdequate {_ _ _ _ _}.

End LRAd.

Export LRAd(LRAdequate,Build_LRAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion LRAd.pack : LRAdequate >-> LRPack.
Coercion LRAd.adequate : LRAdequate >-> LRPackAdequate.

(* TODO : update these for LRAdequate *)

Notation "[ R | Γ ||- A ]< l >"              := (@LRAdequate l Γ A R).
Notation "[ R | Γ ||- A ≅ B | RA ]< l >"     := (RA.(@LRAd.pack l Γ A R).(LRPack.eqTy) B).
Notation "[ R | Γ ||- t : A | RA ]< l >"     := (RA.(@LRAd.pack l Γ A R).(LRPack.redTm) t).
Notation "[ R | Γ ||- t ≅ u : A | RA ]< l >" := (RA.(@LRAd.pack l Γ A R).(LRPack.eqTm) t u).

(** ** Universe levels *)

Inductive TypeLevel : Set :=
  | zero : TypeLevel
  | one  : TypeLevel.

Inductive TypeLevelLt : TypeLevel -> TypeLevel -> Set :=
    | Oi : TypeLevelLt zero one.

Notation "A << B" := (TypeLevelLt A B).

Definition LtSubst {l} (h : l = one) : zero << l.
Proof.
  rewrite h.
  constructor.
Qed.

Definition elim {l : TypeLevel} (h : l << zero) : False :=
  match h in _ << lz return (match lz with | zero => False | one => True end) with
    | Oi => I
  end.

(** ** Reducibility of neutral types *)

Module neRedTy.

  Record neRedTy `{ta : tag}
    `{WfType ta} `{ConvNeuConv ta} `{RedType ta} `{TypeNe ta}
    {wl : wfLCon} {Γ : context} {A : term}
  : Set := {
    ty : term;
    red : [ Γ |- A :⇒*: ty]< wl >;
    ne : Ne[ Γ |- ty]< wl >;
    eq : [ Γ |- ty ~ ty : U]< wl > ;
  }.

  Arguments neRedTy {_ _ _ _ _}.

End neRedTy.

Export neRedTy(neRedTy, Build_neRedTy).
Notation "[ Γ ||-ne A ]< l >" := (neRedTy l Γ A).

Module neRedTyEq.

  Record neRedTyEq `{ta : tag}
    `{WfType ta} `{ConvNeuConv ta} `{RedType ta} `{TypeNe ta}
    {wl : wfLCon} {Γ : context} {A B : term} {neA : [ Γ ||-ne A ]< wl >}
  : Set := {
    ty   : term;
    red  : [ Γ |- B :⇒*: ty]< wl >;
    ne : Ne[ Γ |- ty]< wl >;
    eq  : [ Γ |- neA.(neRedTy.ty) ~ ty : U]< wl >;
  }.

  Arguments neRedTyEq {_ _ _ _ _}.

End neRedTyEq.

Export neRedTyEq(neRedTyEq,Build_neRedTyEq).
Notation "[ Γ ||-ne A ≅ B | R ]< l >" := (neRedTyEq l Γ A B R).

Module neRedTm.

  Record neRedTm `{ta : tag}
    `{WfType ta} `{RedType ta} `{TypeNe ta}
    `{Typing ta} `{ConvNeuConv ta} `{ConvType ta} `{RedTerm ta} `{TermNe ta}
    {l : wfLCon} {Γ : context} {t A : term} {R : [ Γ ||-ne A ]< l >}
  : Set := {
    te  : term;
    red  : [ Γ |- t :⇒*: te : R.(neRedTy.ty)]< l >;
    ne : Ne[ Γ |- te : R.(neRedTy.ty)]< l >;
    eq : [Γ |- te ~ te : R.(neRedTy.ty)]< l > ;
  }.

  Arguments neRedTm {_ _ _ _ _ _ _ _ _}.

End neRedTm.

Export neRedTm(neRedTm, Build_neRedTm).

Notation "[ Γ ||-ne t : A | B ]< l >" := (neRedTm l Γ t A B).

Module neRedTmEq.

  Record neRedTmEq `{ta : tag}
    `{WfType ta} `{RedType ta} `{TypeNe ta}
    `{Typing ta} `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta} `{TermNe ta}
    {l : wfLCon} {Γ : context} {t u A : term} {R : [ Γ ||-ne A ]< l >}
  : Set := {
    termL     : term;
    termR     : term;
    redL      : [ Γ |- t :⇒*: termL : R.(neRedTy.ty) ]< l >;
    redR      : [ Γ |- u :⇒*: termR : R.(neRedTy.ty) ]< l >;
    whneL : Ne[Γ |- termL : R.(neRedTy.ty) ]< l >;
    whneR : Ne[Γ |- termR : R.(neRedTy.ty) ]< l >;
    eq : [ Γ |- termL ~ termR : R.(neRedTy.ty)]< l > ;
  }.

  Arguments neRedTmEq {_ _ _ _ _ _ _ _ _ _}.

End neRedTmEq.

Export neRedTmEq(neRedTmEq, Build_neRedTmEq).
Notation "[ Γ ||-ne t ≅ u : A | R ]< l > " := (neRedTmEq l Γ t u A R).

(** ** Reducibility of the universe *)

Module URedTy.

  Record URedTy `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
    {l} {wl : wfLCon} {Γ : context} {A : term}
  : Set := {
    level  : TypeLevel;
    lt  : level << l;
    wfCtx : [|- Γ]< wl > ;
    red : [ Γ |- A  :⇒*: U ]< wl >
  }.

  Arguments URedTy {_ _ _ _}.

End URedTy.

Export URedTy(URedTy,Build_URedTy).


Notation "[ Γ ||-U< l > A ]< wl >" := (URedTy l wl Γ A) (at level 0, Γ, wl, l, A at level 50).

Module URedTyEq.

  Record URedTyEq `{ta : tag} `{!WfType ta} `{!RedType ta} 
   {l : wfLCon} {Γ : context} {B : term} : Set := {
    red : [Γ |- B :⇒*: U]< l >
  }.

  Arguments URedTyEq : clear implicits.
  Arguments URedTyEq {_ _ _}.

End URedTyEq.

Export URedTyEq(URedTyEq,Build_URedTyEq).

Notation "[ Γ ||-U≅ B ]< l >" := (URedTyEq l Γ B).

Module URedTm.

  Record URedTm@{i j} `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta} `{TermNf ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {wl : wfLCon} {Γ : context} {t A : term} {R : [Γ ||-U<l> A]< wl >}
  : Type@{j} := {
    te : term;
    red : [ Γ |- t :⇒*: te : U ]< wl >;
    type : isType  te;
    val : Nf[Γ |- te : U]< wl >;
    eqr : [Γ |- te ≅ te : U]< wl >;
    rel : [rec R.(URedTy.lt) | Γ ||- t ]< wl > ;
  }.

  Arguments URedTm {_ _ _ _ _ _ _ _ _} rec.

  Record URedTmEq@{i j} `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta} `{TermNf ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {wl : wfLCon} {Γ : context} {t u A : term} {R : [Γ ||-U<l> A]< wl >}
  : Type@{j} := {
      redL : URedTm (@rec) wl Γ t A R ;
      redR : URedTm (@rec) wl Γ u A R ;
      eq   : [ Γ |- redL.(te) ≅ redR.(te) : U ]< wl >;
      relL    : [ rec R.(URedTy.lt) | Γ ||- t ]< wl > ;
      relR    : [ rec R.(URedTy.lt) | Γ ||- u ]< wl > ;
      relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u | relL ]< wl > ;
  }.

  Arguments URedTmEq {_ _ _ _ _ _ _ _ _} rec.

End URedTm.

Export URedTm(URedTm,Build_URedTm,URedTmEq,Build_URedTmEq).
Notation "[ R | Γ ||-U t : A | l ]< wl >" := (URedTm R wl Γ t A l) (at level 0, R, Γ, t, A, wl, l at level 50).
Notation "[ R | Γ ||-U t ≅ u : A | l ]< wl >" := (URedTmEq R wl Γ t u A l) (at level 0, R, Γ, t, u, A, wl, l at level 50).

(** ** Reducibility of product types *)

Module PiRedTy.
  Print BType.
  
  Lemma ez  `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term} : True.
  Proof.
    assert (dom : term) by admit.
    assert (cod : term) by admit.
    assert (domRed : forall Δ (ρ : Δ ≤ Γ),
               Dial l (fun l' => [ |- Δ ]< l' > -> LRPack l' Δ dom⟨ρ⟩)) by admit.
    assert (Δ : context) by admit.
    assert (ρ : Δ ≤ Γ) by admit.
    pose (zfe := fun Q => BType l _ Q (domRed _ ρ) ) ; cbn in zfe.
    assert ( forall wl' : wfLCon,
               ([ |-[ ta ] Δ ]< wl' > -> LRPack wl' Δ dom⟨ρ⟩) -> Type).
    intros wl' Dom.
    refine (forall (Hd : [ |-[ ta ] Δ ]< wl' >), _).
    refine (forall a : term, _).
    refine (forall ha : [ Dom Hd |  Δ ||- a : dom⟨ρ⟩]< wl' >, _).
    refine (Dial wl' _).
    intros wl''.
    eapply LRPack.
    exact wl''.
    exact Δ.
    exact (cod[a .: (ρ >> tRel)]).
    pose (test:= fun R => BType_dep l _
         (fun wl' Dom => forall (a : term)
                                (Hd : [ |-[ ta ] Δ ]< wl' >)
                                (ha : [ Dom Hd |  Δ ||- a : dom⟨ρ⟩]< wl' >),
              Dial wl' (fun wl'' => LRPack wl'' Δ (cod[a .: (ρ >> tRel)])))
         R (domRed _ ρ)).
    cbn in test.
    assert ( forall (wl' : wfLCon)
                  (p : [ |-[ ta ] Δ ]< wl' > -> LRPack wl' Δ dom⟨ρ⟩),
                (forall (a : term) (Hd : [ |-[ ta ] Δ ]< wl' >),
                 [p Hd | _ ||- a : _ ]< _ > ->
                 Dial wl' (fun wl'' : wfLCon => LRPack wl'' Δ cod[a .: ρ >> tRel])) ->
           Type).
    clear test X zfe.
    intros.
    
    
    pose (test := BType l _
                    (fun wl' Dom => forall (a : term)
                                           (Hd : [ |-[ ta ] Δ ]< wl' >)
                                           (ha : [ Dom Hd |  Δ ||- a : dom⟨ρ⟩]< wl' >),
                         Dial wl' (fun wl'' => LRPack wl'' Δ (cod[a .: (ρ >> tRel)])))
                    (domRed _ ρ) ).
    
    
    pose (q:= fun (wl' : wfLCon) (Hd : [ |-[ ta ] Δ ]< wl' >) => True).
    admit.
    Admitted.
    Set Printing Universes.
    Print Dial.
  Record PiRedTy@{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term}
  : Type (* @ max(Set, i+1) *) := {
    dom : term ;
    cod : term ;
    red : [Γ |- A :⇒*: tProd dom cod]< l >;
    domTy : [Γ |- dom]< l >;
    codTy : [Γ ,, dom |- cod]< l > ;
    eq : [Γ |- tProd dom cod ≅ tProd dom cod]< l > ;
    domN : nat ;
    domRed {Δ} (ρ : Δ ≤ Γ) :
      Dial l (fun l' => [ |- Δ ]< l' > -> LRPack@{i} l' Δ dom⟨ρ⟩) ;
    codRed {Δ} {a} (ρ : Δ ≤ Γ) :
      BType l _ (fun wl' (Dom : [ |- Δ ]< wl' > -> LRPack@{i} wl' Δ dom⟨ρ⟩) =>
                   forall (Hd : [ |-[ ta ] Δ ]< wl' >)
                          (ha : [ Dom Hd |  Δ ||- a : dom⟨ρ⟩]< wl' >),
                     Dial wl' (fun wl'' => LRPack@{i} wl'' Δ (cod[a .: (ρ >> tRel)])))
        (domRed ρ);
    codExt
      {Δ a b}
      (ρ : Δ ≤ Γ) :
      BType l _ (fun wl' (Dom : [ |- Δ ]< wl' > -> LRPack@{i} wl' Δ dom⟨ρ⟩) =>
                   forall (Hd : [ |-[ ta ] Δ ]< wl' >)
                          (ha : [ Dom Hd |  Δ ||- a : dom⟨ρ⟩]< wl' >)
                          (hb : [ Dom Hd |  Δ ||- b : dom⟨ρ⟩]< wl' >)
                          (hab : [ Dom Hd |  Δ ||- a ≅ b : dom⟨ρ⟩]< wl' >),
                     Dial wl' (fun wl'' => LRPack@{i} wl'' Δ (cod[a .: (ρ >> tRel)])))
        (domRed ρ);
      (h :  [ |- Δ ]< l' >)
      (ha : [ (domRed ρ τ Ninfl h) | Δ ||- a : dom⟨ρ⟩ ]< l' >) :
      [ (domRed ρ τ Ninfl h) | Δ ||- b : dom⟨ρ⟩]< l' > ->
      [ (domRed ρ τ Ninfl h) | Δ ||- a ≅ b : dom⟨ρ⟩]< l' > ->
      forall {l''} (τ' : l'' ≤ε l') (Minfl : AllInLCon (codomN ρ τ Ninfl h ha) l''),
      [ (codRed ρ τ Ninfl h ha τ' Minfl) | Δ ||- (cod[a .: (ρ >> tRel)]) ≅ (cod[b .: (ρ >> tRel)]) ]< l'' >
  }.

  Arguments PiRedTy {_ _ _ _ _}.

  (** We separate the recursive "data", ie the fact that we have reducibility data (an LRPack)
  for the domain and codomain, and the fact that these are in the graph of the logical relation.
  This is crucial for Coq to accept the definition, because it makes the nesting simple enough
  to be accepted. We later on show an induction principle that does not have this separation to
  make reasoning easier. *)
  Record PiRedTyAdequate@{i j} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term} {R : RedRel@{i j}} {ΠA : PiRedTy@{i} l Γ A}
  : Type@{j} := {
      domAd {Δ l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(domN) l') (h : [ |- Δ ]< l' >) :
      LRPackAdequate@{i j} R (ΠA.(domRed) ρ τ Ninfl h) ;
      codAd {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(domN) l') (h : [ |- Δ ]< l' >)
        (ha : [ (ΠA.(domRed) ρ τ Ninfl h) | Δ ||- a : ΠA.(dom)⟨ρ⟩ ]< l' >)
        {l''} (τ' : l'' ≤ε l')
        (Minfl : AllInLCon (ΠA.(codomN) ρ τ Ninfl h ha) l'')
      : LRPackAdequate@{i j} R (ΠA.(codRed) ρ τ Ninfl h ha τ' Minfl);
  }.

  Arguments PiRedTyAdequate {_ _ _ _ _ _ _ _}.

End PiRedTy.

Export PiRedTy(PiRedTy,Build_PiRedTy,PiRedTyAdequate,Build_PiRedTyAdequate).
Notation "[ Γ ||-Πd A ]< l >" := (PiRedTy l Γ A).

Module PiRedTyEq.

  Record PiRedTyEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta} {l : wfLCon}
    {Γ : context} {A B : term} {ΠA : PiRedTy l Γ A}
  : Type := {
      dom : term;
      cod : term;
      red : [Γ |- B :⇒*: tProd dom cod]< l > ;
      eq  : [Γ |- tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ≅ tProd dom cod ]< l > ;
      domN : nat ;
      domRed {Δ l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
      (Ninfl' : AllInLCon domN l') (h : [ |- Δ ]< l' >) :
      [ (ΠA.(PiRedTy.domRed) ρ τ Ninfl h) | Δ ||- ΠA.(PiRedTy.dom)⟨ρ⟩ ≅ dom⟨ρ⟩ ]< l' > ;
      codomN {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon domN l')  (h : [ |- Δ ]< l' >) :
      [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' > ->
      nat ;
(*      codomN_Ltrans {Δ a l' l''}
        (ρ : Δ ≤ Γ) (τ : l' ≤ε l) (τ' : l'' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon ΠA.(PiRedTy.domN) l'')
        (Minfl : AllInLCon domN l')
        (Minfl' : AllInLCon domN l'')
        (h : [ |- Δ ]< l' >)
        (h' : [ |- Δ ]< l'' >)
        (ha : [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' >)
        (ha' : [ ΠA.(PiRedTy.domRed) ρ τ' Ninfl' h' | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l'' >):
      l'' ≤ε l' -> codomN ρ τ' Ninfl' Minfl' h' ha' <=  codomN ρ τ Ninfl Minfl h ha ;*)
      codRed {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon domN l') (h : [ |- Δ ]< l' >)
        (ha : [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' >)
        {l''} (τ' : l'' ≤ε l')
        (Minfl : AllInLCon (ΠA.(PiRedTy.codomN) ρ τ Ninfl h ha) l'')
        (Minfl' : AllInLCon (codomN ρ τ Ninfl Ninfl' h ha) l'') :
        [ (ΠA.(PiRedTy.codRed) ρ τ Ninfl h ha τ' Minfl) | Δ ||- ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)] ≅ cod[a .: (ρ >> tRel)] ]< l'' >;
  }.

  Arguments PiRedTyEq {_ _ _ _ _}.

End PiRedTyEq.

Export PiRedTyEq(PiRedTyEq,Build_PiRedTyEq).
Notation "[ Γ ||-Π A ≅ B | ΠA ]< l >" := (PiRedTyEq l Γ A B ΠA).

Module PiRedTm.

  Record PiRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{RedTerm ta} `{TermNf ta} {l : wfLCon}
    {Γ : context} {t A : term} {ΠA : PiRedTy l Γ A}
  : Type := {
      nf : term;
      red : [ Γ |- t :⇒*: nf : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ]< l > ;
      isfun : isFun nf ;
      isnf  : Nf[Γ |- nf : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod)]< l > ;
      refl : [ Γ |- nf ≅ nf : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ]< l > ;
      redN : nat ;
      appN {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon redN l') (h : [ |- Δ ]< l' >) :
      [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' >
      -> nat ;
(*      appN_Ltrans {Δ a l' l''}
        (ρ : Δ ≤ Γ) (τ : l' ≤ε l) (τ' : l'' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon ΠA.(PiRedTy.domN) l'')
        (Minfl : AllInLCon redN l')
        (Minfl' : AllInLCon redN l'')
        (h : [ |- Δ ]< l' >)
        (h' : [ |- Δ ]< l'' >)
        (ha : [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' >)
        (ha' : [ ΠA.(PiRedTy.domRed) ρ τ' Ninfl' h' | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l'' >):
      l'' ≤ε l' -> appN ρ τ' Ninfl' Minfl' h' ha' <=  appN ρ τ Ninfl Minfl h ha ; *)
      app {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon redN l') (h : [ |- Δ ]< l' >)
        (ha : [ (ΠA.(PiRedTy.domRed) ρ τ Ninfl h) | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< l' >)
        {l''} (τ' : l'' ≤ε l')
        (Minfl : AllInLCon (ΠA.(PiRedTy.codomN) ρ τ Ninfl h ha) l'')
        (Minfl' : AllInLCon (appN ρ τ Ninfl Ninfl' h ha) l'') :
      [(ΠA.(PiRedTy.codRed) ρ τ Ninfl h ha τ' Minfl) | Δ ||- tApp nf⟨ρ⟩ a : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]]< l'' > ;
      eq {Δ l' a b} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon redN l') (h : [ |- Δ ]< l' >)
        (ha : [ (ΠA.(PiRedTy.domRed) ρ τ Ninfl h) | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< l' >)
        (hb : [ (ΠA.(PiRedTy.domRed) ρ τ Ninfl h) | Δ ||- b : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< l' >)
        (eq : [ (ΠA.(PiRedTy.domRed) ρ τ Ninfl h) | Δ ||- a ≅ b : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< l' >)
        {l''} (τ' : l'' ≤ε l')
        (Minfl : AllInLCon (ΠA.(PiRedTy.codomN) ρ τ Ninfl h ha) l'')
        (Minfl' : AllInLCon (appN ρ τ Ninfl Ninfl' h ha) l'') :
      [ (ΠA.(PiRedTy.codRed) ρ τ Ninfl h ha τ' Minfl) | Δ ||- tApp nf⟨ρ⟩ a ≅ tApp nf⟨ρ⟩ b : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)] ]< l'' >
  }.

  Arguments PiRedTm {_ _ _ _ _ _ _ _ _}.

End PiRedTm.

Export PiRedTm(PiRedTm,Build_PiRedTm).
Notation "[ Γ ||-Π t : A | ΠA ]< l >" := (PiRedTm l Γ t A ΠA).

Module PiRedTmEq.

  Record PiRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{RedTerm ta} `{TermNf ta} {l : wfLCon}
    {Γ : context} {t u A : term} {ΠA : PiRedTy l Γ A}
  : Type := {
      redL : [ Γ ||-Π t : A | ΠA ]< l > ;
      redR : [ Γ ||-Π u : A | ΠA ]< l > ;
      eq : [ Γ |- redL.(PiRedTm.nf) ≅ redR.(PiRedTm.nf) : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ]< l > ;
      eqN : nat;
      eqappN {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon eqN l') (h : [ |- Δ ]< l' >) :
      [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' >
      -> nat ; 
(*      eqappN_Ltrans {Δ a l' l''}
        (ρ : Δ ≤ Γ) (τ : l' ≤ε l) (τ' : l'' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon ΠA.(PiRedTy.domN) l'')
        (Minfl : AllInLCon eqN l')
        (Minfl' : AllInLCon eqN l'')
        (h : [ |- Δ ]< l' >)
        (h' : [ |- Δ ]< l'' >)
        (ha : [ ΠA.(PiRedTy.domRed) ρ τ Ninfl h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l' >)
        (ha' : [ ΠA.(PiRedTy.domRed) ρ τ' Ninfl' h' | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]< l'' >):
      l'' ≤ε l' -> eqappN ρ τ' Ninfl' Minfl' h' ha' <=  eqappN ρ τ Ninfl Minfl h ha ;*)
      eqApp {Δ a l'} (ρ : Δ ≤ Γ) (τ : l' ≤ε l)
        (Ninfl : AllInLCon ΠA.(PiRedTy.domN) l')
        (Ninfl' : AllInLCon eqN l') (h : [ |- Δ ]< l' >)
        (ha : [(ΠA.(PiRedTy.domRed) ρ τ Ninfl h) | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]< l' >)
        {l''} (τ' : l'' ≤ε l')
        (Minfl : AllInLCon (ΠA.(PiRedTy.codomN) ρ τ Ninfl h ha) l'')
        (Minfl' : AllInLCon (eqappN ρ τ Ninfl Ninfl' h ha) l'') :
      [ (ΠA.(PiRedTy.codRed) ρ τ Ninfl h ha τ' Minfl) | Δ ||-
          tApp redL.(PiRedTm.nf)⟨ρ⟩ a ≅ tApp redR.(PiRedTm.nf)⟨ρ⟩ a : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]]< l'' >
  }.

  Arguments PiRedTmEq {_ _ _ _ _ _ _ _ _}.

End PiRedTmEq.

Export PiRedTmEq(PiRedTmEq,Build_PiRedTmEq).

Notation "[ Γ ||-Π t ≅ u : A | ΠA ]< l >" := (PiRedTmEq l Γ t u A ΠA).

(** ** Reducibility of neutrals at an arbitrary type *)

Module NeNf.
  Record RedTm `{ta : tag} `{Typing ta} `{ConvNeuConv ta} `{TermNe ta} {l Γ k A} : Set :=
    {
      ne : Ne[Γ |- k : A]< l >;
      ty : [Γ |- k : A]< l > ;
      refl : [Γ |- k ~ k : A]< l >
    }.
  Arguments RedTm {_ _ _ _}.

  Record RedTmEq `{ta : tag} `{ConvNeuConv ta} `{TermNe ta} {l Γ k k' A} : Set :=
    {
      neL : Ne[Γ |- k : A]< l >;
      neR : Ne[Γ |- k' : A]< l >;
      conv : [Γ |- k ~ k' : A]< l >
    }.

  Arguments RedTmEq {_ _ _}.
End NeNf.

Notation "[ Γ ||-NeNf k : A ]< l >" := (NeNf.RedTm l Γ k A) (at level 0, Γ, l,  k, A at level 50).
Notation "[ Γ ||-NeNf k ≅ i : A ]< l >" := (NeNf.RedTmEq l Γ k i A) (at level 0, Γ, k, l, i, A at level 50).


(** ** Reducibility of natural number type *)
Module NatRedTy.

  Record NatRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term}
  : Set := 
  {
    red : [Γ |- A :⇒*: tNat]< l >
  }.

  Arguments NatRedTy {_ _ _}.
End NatRedTy.

Export NatRedTy(NatRedTy, Build_NatRedTy).
Notation "[ Γ ||-Nat A ]< l >" := (NatRedTy l Γ A) (at level 0, l, Γ, A at level 50).

Module NatRedTyEq.

  Record NatRedTyEq `{ta : tag} `{WfType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term} {NA : NatRedTy l Γ A} {B : term}
  : Set := {
    red : [Γ |- B :⇒*: tNat]< l >;
  }.

  Arguments NatRedTyEq {_ _ _ _ _ _}.

End NatRedTyEq.

Export NatRedTyEq(NatRedTyEq,Build_NatRedTyEq).

Notation "[ Γ ||-Nat A ≅ B | RA ]< l >" := (@NatRedTyEq _ _ _ l Γ A RA B) (at level 0, l, Γ, A, B, RA at level 50).

Module NatRedTm.
Section NatRedTm.
  Context `{ta : tag} `{WfType ta} 
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} `{TermNe ta}.

  Inductive NatRedTm {l : wfLCon} {Γ : context} {A: term} {NA : NatRedTy l Γ A} : term -> Set :=
  | Build_NatRedTm {t}
    (nf : term)
    (red : [Γ |- t :⇒*: nf : tNat ]< l >)
    (eq : [Γ |- nf ≅ nf : tNat]< l >)
    (prop : NatProp nf) : NatRedTm t

  with NatProp {l : wfLCon} {Γ : context} {A: term} {NA : NatRedTy l Γ A} : term -> Set :=
  | zeroR  : NatProp tZero
  | succR {n} :
    NatRedTm n ->
    NatProp (tSucc n)
  | neR {ne} : [Γ ||-NeNf ne : tNat]< l > -> NatProp ne.


Scheme NatRedTm_mut_rect := Induction for NatRedTm Sort Type with
    NatProp_mut_rect := Induction for NatProp Sort Type.

Combined Scheme _NatRedInduction from
  NatRedTm_mut_rect,
  NatProp_mut_rect.

Let _NatRedInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _NatRedInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let NatRedInductionType :=
  ltac: (let ind := eval cbv delta [_NatRedInductionType] zeta
    in _NatRedInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma NatRedInduction : NatRedInductionType.
Proof.
  intros ???? PRed PProp **; split ; now apply (_NatRedInduction _ _ _ _ PRed PProp).
Defined.

Definition nf {l Γ A n} {NA : [Γ ||-Nat A]< l > } : @NatRedTm _ _ _ NA n -> term.
Proof.
  intros [? nf]. exact nf.
Defined.

Definition red {l Γ A n} {NA : [Γ ||-Nat A]< l >} (Rn : @NatRedTm _ _ _ NA n) : [Γ |- n :⇒*: nf Rn : tNat]< l >.
Proof.
  dependent inversion Rn; subst; cbn; tea.
Defined.

End NatRedTm.
Arguments NatRedTm {_ _ _ _ _ _ _ _ _ _ _}.
Arguments NatProp {_ _ _ _ _ _ _ _ _ _ _}.

End NatRedTm.

Export NatRedTm(NatRedTm,Build_NatRedTm, NatProp, NatRedInduction).

Notation "[ Γ ||-Nat t : A | RA ]< l >" := (@NatRedTm _ _ _ _ _ _ _ _ l Γ A RA t) (at level 0, l, Γ, t, A, RA at level 50).


Module NatRedTmEq.
Section NatRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} `{TermNe ta}.

  Inductive NatRedTmEq {l : wfLCon} {Γ : context} {A: term} {NA : NatRedTy l Γ A} : term -> term -> Set :=
  | Build_NatRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⇒*: nfL : tNat]< l >)
    (redR : [Γ |- u :⇒*: nfR : tNat ]< l >)
    (eq : [Γ |- nfL ≅ nfR : tNat]< l >)
    (prop : NatPropEq nfL nfR) : NatRedTmEq t u

  with NatPropEq {l : wfLCon} {Γ : context} {A: term} {NA : NatRedTy l Γ A} : term -> term -> Set :=
  (* KM: plugging in the parameter type directly... Is that ok ? *)
  | zeroReq :
    NatPropEq tZero tZero
  | succReq {n n'} :
    NatRedTmEq n n' ->
    NatPropEq (tSucc n) (tSucc n')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tNat]< l > -> NatPropEq ne ne'.

Scheme NatRedTmEq_mut_rect := Induction for NatRedTmEq Sort Type with
    NatPropEq_mut_rect := Induction for NatPropEq Sort Type.

Combined Scheme _NatRedInduction from
  NatRedTmEq_mut_rect,
  NatPropEq_mut_rect.

Combined Scheme _NatRedEqInduction from
  NatRedTmEq_mut_rect,
  NatPropEq_mut_rect.

Let _NatRedEqInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _NatRedEqInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let NatRedEqInductionType :=
  ltac: (let ind := eval cbv delta [_NatRedEqInductionType] zeta
    in _NatRedEqInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma NatRedEqInduction : NatRedEqInductionType.
Proof.
  intros ???? PRedEq PPropEq **; split; now apply (_NatRedEqInduction _ _ _ _ PRedEq PPropEq).
Defined.

End NatRedTmEq.
Arguments NatRedTmEq {_ _ _ _ _ _ _ _ _ _ _}.
Arguments NatPropEq {_ _ _ _ _ _ _ _ _ _ _}.
End NatRedTmEq.

Export NatRedTmEq(NatRedTmEq,Build_NatRedTmEq, NatPropEq, NatRedEqInduction).

Notation "[ Γ ||-Nat t ≅ u : A | RA ]< l >" := (@NatRedTmEq _ _ _ _ _ _ _ _ l Γ A RA t u) (at level 0, l, Γ, t, u, A, RA at level 50).


(** ** Reducibility of boolean type *)
Module BoolRedTy.

  Record BoolRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term}
  : Set := 
  {
    red : [Γ |- A :⇒*: tBool]< l >
  }.

  Arguments BoolRedTy {_ _ _}.
End BoolRedTy.

Export BoolRedTy(BoolRedTy, Build_BoolRedTy).
Notation "[ Γ ||-Bool A ]< l >" := (BoolRedTy l Γ A) (at level 0, l, Γ, A at level 50).

Module BoolRedTyEq.

  Record BoolRedTyEq `{ta : tag} `{WfType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term} {NA : BoolRedTy l Γ A} {B : term}
  : Set := {
    red : [Γ |- B :⇒*: tBool]< l >;
  }.

  Arguments BoolRedTyEq {_ _ _ _ _ _}.

End BoolRedTyEq.

Export BoolRedTyEq(BoolRedTyEq,Build_BoolRedTyEq).

Notation "[ Γ ||-Bool A ≅ B | RA ]< l >" := (@BoolRedTyEq _ _ _ l Γ A RA B) (at level 0, l, Γ, A, B, RA at level 50).

Module BoolRedTm.
Section BoolRedTm.
  Context `{ta : tag} `{WfType ta} 
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} `{TermNe ta}.

  Inductive BoolProp {l : wfLCon} {Γ : context} {A: term} {NA : BoolRedTy l Γ A} : term -> Set :=
  | trueR  : BoolProp tTrue
  | falseR  : BoolProp tFalse
  | neR {ne} : [Γ ||-NeNf ne : tBool]< l > -> BoolProp ne.
  
  Inductive BoolRedTm {l : wfLCon} {Γ : context} {A: term} {NA : BoolRedTy l Γ A} : term -> Set :=
  | Build_BoolRedTm {t}
    (nf : term)
    (red : [Γ |- t :⇒*: nf : tBool ]< l >)
    (eq : [Γ |- nf ≅ nf : tBool]< l >)
    (prop : BoolProp (l := l) (Γ := Γ) (A := A) (NA := NA) nf) : BoolRedTm t.


Scheme BoolRedTm_mut_rect := Induction for BoolRedTm Sort Type.
Scheme BoolProp_mut_rect := Induction for BoolProp Sort Type.

(*Combined Scheme _BoolRedInduction from
  BoolRedTm_mut_rect,
  BoolProp_mut_rect.

Let _BoolRedInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _BoolRedInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let BoolRedInductionType :=
  ltac: (let ind := eval cbv delta [_BoolRedInductionType] zeta
    in _BoolRedInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma BoolRedInduction : BoolRedInductionType.
Proof.
  intros ???? PRed PProp **; split ; now apply (_BoolRedInduction _ _ _ _ PRed PProp).
Defined.*)

Definition nf {l Γ A n} {NA : [Γ ||-Bool A]< l > } : @BoolRedTm _ _ _ NA n -> term.
Proof.
  intros [? nf]. exact nf.
Defined.

Definition red {l Γ A n} {NA : [Γ ||-Bool A]< l >} (Rn : @BoolRedTm _ _ _ NA n) : [Γ |- n :⇒*: nf Rn : tBool]< l >.
Proof.
  dependent inversion Rn; subst; cbn; tea.
Defined.

End BoolRedTm.
Arguments BoolRedTm {_ _ _ _ _ _ _ _ _ _ _}.
Arguments BoolProp {_ _ _ _ _ _ _ _ _}.

End BoolRedTm.

Export BoolRedTm(BoolRedTm,Build_BoolRedTm, BoolProp).

Notation "[ Γ ||-Bool t : A | RA ]< l >" := (@BoolRedTm _ _ _ _ _ _ _ _ l Γ A RA t) (at level 0, l, Γ, t, A, RA at level 50).


Module BoolRedTmEq.
Section BoolRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} `{TermNe ta}.

  Inductive BoolPropEq {l : wfLCon} {Γ : context} {A: term} {NA : BoolRedTy l Γ A} : term -> term -> Set :=
  (* KM: plugging in the parameter type directly... Is that ok ? *)
  | trueReq :
    BoolPropEq tTrue tTrue
  | falseReq :
    BoolPropEq tFalse tFalse
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tBool]< l > -> BoolPropEq ne ne'.
  
  Inductive BoolRedTmEq {l : wfLCon} {Γ : context} {A: term} {NA : BoolRedTy l Γ A} : term -> term -> Set :=
  | Build_BoolRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⇒*: nfL : tBool]< l >)
    (redR : [Γ |- u :⇒*: nfR : tBool ]< l >)
    (eq : [Γ |- nfL ≅ nfR : tBool]< l >)
    (prop : BoolPropEq (l := l) (Γ := Γ) (A := A) (NA := NA) nfL nfR) :
    BoolRedTmEq t u.

 

Scheme BoolRedTmEq_mut_rect := Induction for BoolRedTmEq Sort Type.
Scheme BoolPropEq_mut_rect := Induction for BoolPropEq Sort Type.

(*Combined Scheme _BoolRedInduction from
  BoolRedTmEq_mut_rect,
  BoolPropEq_mut_rect.

Combined Scheme _BoolRedEqInduction from
  BoolRedTmEq_mut_rect,
  BoolPropEq_mut_rect.

Let _BoolRedEqInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _BoolRedEqInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let BoolRedEqInductionType :=
  ltac: (let ind := eval cbv delta [_BoolRedEqInductionType] zeta
    in _BoolRedEqInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma BoolRedEqInduction : BoolRedEqInductionType.
Proof.
  intros ???? PRedEq PPropEq **; split; now apply (_BoolRedEqInduction _ _ _ _ PRedEq PPropEq).
Defined.
*)
End BoolRedTmEq.
Arguments BoolRedTmEq {_ _ _ _ _ _ _ _ _ _ _}.
Arguments BoolPropEq {_ _ _ _ _ _ _ _}.
End BoolRedTmEq.

Export BoolRedTmEq(BoolRedTmEq,Build_BoolRedTmEq, BoolPropEq).

Notation "[ Γ ||-Bool t ≅ u : A | RA ]< l >" := (@BoolRedTmEq _ _ _ _ _ _ _ _ l Γ A RA t u) (at level 0, l, Γ, t, u, A, RA at level 50).

(** ** Reducibility of empty type *)
Module EmptyRedTy.

  Record EmptyRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term}
  : Set := 
  {
    red : [Γ |- A :⇒*: tEmpty]< l >
  }.

  Arguments EmptyRedTy {_ _ _}.
End EmptyRedTy.

Export EmptyRedTy(EmptyRedTy, Build_EmptyRedTy).
Notation "[ Γ ||-Empty A ]< l >" := (EmptyRedTy l Γ A) (at level 0, l, Γ, A at level 50).

Module EmptyRedTyEq.

  Record EmptyRedTyEq `{ta : tag} `{WfType ta} `{RedType ta}
    {l : wfLCon} {Γ : context} {A : term} {NA : EmptyRedTy l Γ A} {B : term}
  : Set := {
    red : [Γ |- B :⇒*: tEmpty]< l >;
  }.

  Arguments EmptyRedTyEq {_ _ _ _ _ _}.

End EmptyRedTyEq.

Export EmptyRedTyEq(EmptyRedTyEq,Build_EmptyRedTyEq).

Notation "[ Γ ||-Empty A ≅ B | RA ]< l >" := (@EmptyRedTyEq _ _ _ l Γ A RA B) (at level 0, l, Γ, A, B, RA at level 50).

Module EmptyRedTm.
Section EmptyRedTm.
  Context `{ta : tag} `{WfType ta} 
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} `{TermNe ta}.

  Inductive EmptyProp {l : wfLCon} {Γ : context} : term -> Set :=
  | neR {ne} : [Γ ||-NeNf ne : tEmpty]< l > -> EmptyProp ne.

  Inductive EmptyRedTm {l : wfLCon} {Γ : context} {A: term} {NA : EmptyRedTy l Γ A} : term -> Set :=
  | Build_EmptyRedTm {t}
    (nf : term)
    (red : [Γ |- t :⇒*: nf : tEmpty ]< l >)
    (eq : [Γ |- nf ≅ nf : tEmpty]< l >)
    (prop : @EmptyProp l Γ nf) : EmptyRedTm t.

(* Scheme EmptyRedTm_mut_rect := Induction for EmptyRedTm Sort Type with *)
(*     EmptyProp_mut_rect := Induction for EmptyProp Sort Type. *)

(* Combined Scheme _EmptyRedInduction from *)
(*   EmptyRedTm_mut_rect, *)
(*   EmptyProp_mut_rect. *)

(* Let _EmptyRedInductionType := *)
(*   ltac:(let ind := fresh "ind" in *)
(*       pose (ind := _EmptyRedInduction); *)
(*       let ind_ty := type of ind in *)
(*       exact ind_ty). *)

(* Let EmptyRedInductionType := *)
(*   ltac: (let ind := eval cbv delta [_EmptyRedInductionType] zeta *)
(*     in _EmptyRedInductionType in *)
(*     let ind' := polymorphise ind in *)
(*   exact ind'). *)

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
(* Lemma EmptyRedInduction : EmptyRedInductionType. *)
(* Proof. *)
(*   intros ??? PRed PProp **; split; now apply (_EmptyRedInduction _ _ _ PRed PProp). *)
(* Defined. *)

Definition nf {l Γ A n} {NA : [Γ ||-Empty A]< l >} : @EmptyRedTm _ _ _ NA n -> term.
Proof.
  intros [? nf]. exact nf.
Defined.

Definition red {l Γ A n} {NA : [Γ ||-Empty A]< l >} (Rn : @EmptyRedTm _ _ _ NA n) : [Γ |- n :⇒*: nf Rn : tEmpty]< l >.
Proof.
  dependent inversion Rn; subst; cbn; tea.
Defined.

End EmptyRedTm.
Arguments EmptyRedTm {_ _ _ _ _ _ _ _ _ _ _}.
Arguments EmptyProp {_ _ _ _ _}.

End EmptyRedTm.

Export EmptyRedTm(EmptyRedTm,Build_EmptyRedTm, EmptyProp).

Notation "[ Γ ||-Empty t : A | RA ]< l >" := (@EmptyRedTm _ _ _ _ _ _ _ _ l Γ A RA t) (at level 0, Γ, l, t, A, RA at level 50).


Module EmptyRedTmEq.
Section EmptyRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} `{TermNe ta}.

  Inductive EmptyPropEq {l} {Γ : context} : term -> term -> Set :=
  (* KM: plugging in the parameter type directly... Is that ok ? *)
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tEmpty]< l > -> EmptyPropEq ne ne'.

  Inductive EmptyRedTmEq {l} {Γ : context} {A: term} {NA : EmptyRedTy l Γ A} : term -> term -> Set :=
  | Build_EmptyRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⇒*: nfL : tEmpty]< l >)
    (redR : [Γ |- u :⇒*: nfR : tEmpty ]< l >)
    (eq : [Γ |- nfL ≅ nfR : tEmpty]< l >)
    (prop : @EmptyPropEq l Γ nfL nfR) : EmptyRedTmEq t u.

End EmptyRedTmEq.
Arguments EmptyRedTmEq {_ _ _ _ _ _ _ _ _ _ _}.
Arguments EmptyPropEq {_ _ _ _}.
End EmptyRedTmEq.

Export EmptyRedTmEq(EmptyRedTmEq,Build_EmptyRedTmEq, EmptyPropEq).

Notation "[ Γ ||-Empty t ≅ u : A | RA ]< l >" := (@EmptyRedTmEq _ _ _ _ _ _ _ _ l Γ A RA t u) (at level 0, Γ, l, t, u, A, RA at level 50).

(** ** Definition of the logical relation *)

(** This simply bundles the different cases for reducibility already defined. *)

Unset Elimination Schemes.

Inductive LR@{i j k} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{TypeNf ta} `{TypeNe ta}  `{RedTerm ta} `{TermNf ta} `{TermNe ta}
  {l : TypeLevel} (rec : forall l', l' << l -> RedRel@{i j})
: RedRel@{j k} :=
  | LRU {wl Γ A} (H : [Γ ||-U<l> A]< wl >) :
      LR rec wl Γ A
      (fun B   => [Γ ||-U≅ B ]< wl >)
      (fun t   => [ rec | Γ ||-U t     : A | H ]< wl >)
      (fun t u => [ rec | Γ ||-U t ≅ u : A | H ]< wl >)
  | LRne {wl Γ A} (neA : [ Γ ||-ne A ]< wl >) :
      LR rec wl Γ A
      (fun B   =>  [ Γ ||-ne A ≅ B     | neA]< wl >)
      (fun t   =>  [ Γ ||-ne t     : A | neA]< wl >)
      (fun t u =>  [ Γ ||-ne t ≅ u : A | neA]< wl >)
  | LRPi {wl : wfLCon} {Γ : context} {A : term}
    (ΠA : PiRedTy@{j} wl Γ A) (ΠAad : PiRedTyAdequate@{j k} (LR rec) ΠA) :
    LR rec wl Γ A
      (fun B   => [ Γ ||-Π A ≅ B     | ΠA ]< wl >)
      (fun t   => [ Γ ||-Π t     : A | ΠA ]< wl >)
      (fun t u => [ Γ ||-Π t ≅ u : A | ΠA ]< wl >)
  | LRNat {wl Γ A} (NA : [Γ ||-Nat A]< wl >) :
    LR rec wl Γ A (NatRedTyEq NA) (NatRedTm NA) (NatRedTmEq NA)
  | LRBool {wl Γ A} (NA : [Γ ||-Bool A]< wl >) :
    LR rec wl Γ A (BoolRedTyEq NA) (BoolRedTm NA) (BoolRedTmEq NA)
  | LREmpty {wl Γ A} (NA : [Γ ||-Empty A]< wl >) :
    LR rec wl Γ A (EmptyRedTyEq NA) (EmptyRedTm NA) (EmptyRedTmEq NA).
  
  (** Removed, as it is provable (!), cf LR_embedding in LRInduction. *)
  (* | LREmb {Γ A l'} (l_ : l' << l) (H : [ rec l' l_ | Γ ||- A]) :
      LR rec Γ A
      (fun B   => [ rec l' l_ | Γ ||- A ≅ B     | H ])
      (fun t   => [ rec l' l_ | Γ ||- t     : A | H ])
      (fun t u => [ rec l' l_ | Γ ||- t ≅ u : A | H ]) *)

Set Elimination Schemes.

(** ** Bundling of the logical relation *)

(** Boilerplate to make the relation look a bit better. *)

Section MoreDefs.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{TypeNf ta} `{TypeNe ta} `{!RedTerm ta} `{TermNf ta} `{TermNe ta}.

  Definition rec0@{i j} (l' : TypeLevel) (h : l' << zero) : RedRel@{i j} :=
    match elim h with
    end.

  Definition LogRel0@{i j k} :=
    LR@{i j k} rec0@{i j}.

  Definition LRbuild0@{i j k} {wl Γ A rEq rTe rTeEq} :
    LogRel0@{i j k} wl Γ A rEq rTe rTeEq -> [ LogRel0@{i j k} | Γ ||- A ]< wl > :=
    fun H => {|
      LRAd.pack := {| LRPack.eqTy := rEq ; LRPack.redTm := rTe ; LRPack.eqTm := rTeEq |} ;
      LRAd.adequate := H |}.

  Definition LogRelRec@{i j k} (l : TypeLevel) : forall l', l' << l -> RedRel@{j k} :=
    match l with
      | zero => rec0@{j k}
      | one => fun _ _ => LogRel0@{i j k}
    end.

  Arguments LogRelRec l l' l_ /.

  Definition rec1 :=
    LogRelRec one.

  Definition LogRel1@{i j k l} :=
    LR@{j k l} rec1@{i j k}.

  Definition LogRel@{i j k l} (l : TypeLevel) :=
    LR@{j k l} (LogRelRec@{i j k} l).

  
  Print LR.
  Record WLogRel@{i j k l} (l : TypeLevel) wl Γ A :=
    { WN : nat ;
      WRed {wl'} (τ : wl' ≤ε wl) (Ninfl : AllInLCon WN wl') :
      [ LogRel@{i j k l} l | Γ ||- A ]< wl' > ;
    }.
  Arguments WN [_ _ _ _] _.
  Arguments WRed [_ _ _ _ _ _] _.

  Record WLogRelEq@{i j k l} (l : TypeLevel) wl Γ A B (wlrA : WLogRel@{i j k l} l wl Γ A) :=
    { WNEq : nat ;
      WRedEq {wl'} (τ : wl' ≤ε wl)
        (Ninfl : AllInLCon wlrA.(WN) wl')
        (Ninfl' : AllInLCon WNEq wl') :
      [ LogRel l | Γ ||- A ≅ B | wlrA.(WRed) τ Ninfl ]< wl' >;
    }.
  Arguments WNEq [_ _ _ _ _] _.
  Arguments WRedEq [_ _ _ _ _ _ _] _.

  
  Record WLogRelTm@{i j k l} (l : TypeLevel) wl Γ t A (wlrA : WLogRel@{i j k l} l wl Γ A) :=
    { WNTm : nat ;
      WRedTm {wl'} (τ : wl' ≤ε wl)
        (Ninfl : AllInLCon wlrA.(WN) wl')
        (Ninfl' : AllInLCon WNTm wl') :
      [ LogRel l | Γ ||- t : A | wlrA.(WRed) τ Ninfl ]< wl' >;
    }.
  Arguments WNTm [_ _ _ _ _] _.
  Arguments WRedTm [_ _ _ _ _ _ _] _.

  Record WLogRelTmEq@{i j k l} (l : TypeLevel) wl Γ t u A (wlrA : WLogRel@{i j k l} l wl Γ A) :=
    { WNTmEq : nat ;
      WRedTmEq {wl'} (τ : wl' ≤ε wl)
        (Ninfl : AllInLCon wlrA.(WN) wl')
        (Ninfl' : AllInLCon WNTmEq wl') :
      [ LogRel l | Γ ||- t ≅ u : A | wlrA.(WRed) τ Ninfl ]< wl' >;
    }.
  Arguments WNTmEq [_ _ _ _ _ _] _.
  Arguments WRedTmEq [_ _ _ _ _ _ _ _] _.
  
  
  Definition LRbuild@{i j k l} {wl Γ l A rEq rTe rTeEq} :
    LR@{j k l} (LogRelRec@{i j k} l) wl Γ A rEq rTe rTeEq -> [ LogRel l | Γ ||- A ]< wl > :=
    fun H => {|
      LRAd.pack := {| LRPack.eqTy := rEq ; LRPack.redTm := rTe ; LRPack.eqTm := rTeEq |} ;
      LRAd.adequate := H |}.

  Definition LRunbuild {wl Γ l A} :
  [ LogRel l | Γ ||- A ]< wl > ->
    ∑ rEq rTe rTeEq , LR (LogRelRec l) wl Γ A rEq rTe rTeEq :=
      fun H => (LRPack.eqTy H; LRPack.redTm H; LRPack.eqTm H; H.(LRAd.adequate)).

  Definition LRU_@{i j k l} {wl l Γ A} (H : [Γ ||-U<l> A]< wl >)
    : [ LogRel@{i j k l} l | Γ ||- A ]< wl > :=
    LRbuild (LRU (LogRelRec l) H).

  Definition LRne_@{i j k l} l {wl Γ A} (neA : [Γ ||-ne A]< wl >)
    : [ LogRel@{i j k l} l | Γ ||- A ]< wl > :=
    LRbuild (LRne (LogRelRec l) neA).

  Definition LRPi_@{i j k l} l {wl Γ A} (ΠA : PiRedTy@{k} wl Γ A)
    (ΠAad : PiRedTyAdequate (LR (LogRelRec@{i j k} l)) ΠA)
    : [ LogRel@{i j k l} l | Γ ||- A ]< wl > :=
    LRbuild (LRPi (LogRelRec l) ΠA ΠAad).

  Definition LRNat_@{i j k l} l {wl Γ A} (NA : [Γ ||-Nat A]< wl >) 
    : [LogRel@{i j k l} l | Γ ||- A]< wl > :=
    LRbuild (LRNat (LogRelRec l) NA).

  Definition LRBool_@{i j k l} l {wl Γ A} (NA : [Γ ||-Bool A]< wl >) 
    : [LogRel@{i j k l} l | Γ ||- A]< wl > :=
    LRbuild (LRBool (LogRelRec l) NA).

  Definition LREmpty_@{i j k l} l {wl Γ A} (NA : [Γ ||-Empty A]< wl >) 
    : [LogRel@{i j k l} l | Γ ||- A]< wl > :=
    LRbuild (LREmpty (LogRelRec l) NA).

  

End MoreDefs.
Arguments WN [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WRed [ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WNEq [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WRedEq [ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WNTm [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WRedTm [ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WNTmEq [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
Arguments WRedTmEq [ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] _.
(** To be explicit with universe levels use the rhs, e.g
   [ LogRel@{i j k l} l | Γ ||- A] or [ LogRel0@{i j k} ||- Γ ||- A ≅ B | RA ]
 *)
Notation "[ Γ ||-< l > A ]< wl >" := [ LogRel l | Γ ||- A ]< wl >.
Notation "[ Γ ||-< l > A ≅ B | RA ]< wl >" := [ LogRel l | Γ ||- A ≅ B | RA ]< wl >.
Notation "[ Γ ||-< l > t : A | RA ]< wl >" := [ LogRel l | Γ ||- t : A | RA ]< wl >.
Notation "[ Γ ||-< l > t ≅ u : A | RA ]< wl >" := [ LogRel l | Γ ||- t ≅ u : A | RA ]< wl >.

Notation "W[ Γ ||-< l > A ]< wl >" := (WLogRel l wl Γ A).
Notation "W[ Γ ||-< l > A ≅ B | RA ]< wl >" := (WLogRelEq l wl Γ A B RA).
Notation "W[ Γ ||-< l > t : A | RA ]< wl >" := (WLogRelTm l wl Γ t A RA).
Notation "W[ Γ ||-< l > t ≅ u : A | RA ]< wl >" := (WLogRelTmEq l wl Γ t u A RA).

(** ** Rebundling reducibility of product types *)

(** The definition of reducibility of product types in the logical relation, which separates
the "adequacy" part is not nice to work with. Here we relate it to the more natural one,
which lets us later on define an induction principle that does not show the separation at all. *)

Module PiRedTyPack.
Section PiRedTyPack.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{TypeNf ta} `{TypeNe ta} `{!RedTerm ta} `{TermNf ta} `{TermNe ta}.


  Record PiRedTyPack@{i j k l} {wl : wfLCon} {Γ : context} {A : term}
    {l : TypeLevel} 
    : Type@{l} := {
    dom : term ;
    cod : term ;
    red : [Γ |- A :⇒*: tProd dom cod]< wl >;
    domTy : [Γ |- dom]< wl >;
    codTy : [Γ ,, dom |- cod]< wl > ;
    eq : [Γ |- tProd dom cod ≅ tProd dom cod]< wl > ;
    domN : nat ;
    domRed {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
      (Ninfl : AllInLCon domN wl') :
      [ |- Δ ]< wl' > -> [ LogRel@{i j k l} l | Δ ||- dom⟨ρ⟩ ]< wl' > ;
    codomN {Δ a wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
      (Ninfl : AllInLCon domN wl')
      (h : [ |- Δ ]< wl' >)
      (ha : [ (domRed ρ τ Ninfl h) |  Δ ||- a : dom⟨ρ⟩]< wl' >) :
      nat ;
(*    codomN_Ltrans {Δ a l' l''}
      (ρ : Δ ≤ Γ) (τ : l' ≤ε wl) (τ' : l'' ≤ε wl)
      (Ninfl : AllInLCon domN l')
      (Ninfl' : AllInLCon domN l'')
      (h : [ |- Δ ]< l' >)
      (h' : [ |- Δ ]< l'' >)
      (ha : [ domRed ρ τ Ninfl h | Δ ||- a : dom⟨ρ⟩]< l' >)
      (ha' : [ domRed ρ τ' Ninfl' h' | Δ ||- a : dom⟨ρ⟩]< l'' >):
      l'' ≤ε l' -> codomN ρ τ' Ninfl' h' ha' <=  codomN ρ τ Ninfl h ha ;*)
    codRed {Δ a wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
      (Ninfl : AllInLCon domN wl')
      (h : [ |- Δ ]< wl' >)
      (ha : [ (domRed ρ τ Ninfl h) |  Δ ||- a : dom⟨ρ⟩]< wl' >)
      {wl''} (τ' : wl'' ≤ε wl')
      (Minfl : AllInLCon (codomN ρ τ Ninfl h ha) wl'') :
        [ LogRel@{i j k l} l | Δ ||- cod[a .: (ρ >> tRel)]]< wl''> ; 
    codExt {Δ a b wl'}
      (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl) 
      (Ninfl : AllInLCon domN wl')
      (h :  [ |- Δ ]< wl' >)
      (ha : [ (domRed ρ τ Ninfl h) | Δ ||- a : dom⟨ρ⟩ ]< wl' >) :
      [ (domRed ρ τ Ninfl h) | Δ ||- b : dom⟨ρ⟩]< wl' > ->
      [ (domRed ρ τ Ninfl h) | Δ ||- a ≅ b : dom⟨ρ⟩]< wl' > ->
      forall {wl''} (τ' : wl'' ≤ε wl')
             (Minfl : AllInLCon (codomN ρ τ Ninfl h ha) wl''),
        [ (codRed ρ τ Ninfl h ha τ' Minfl) | Δ ||- (cod[a .: (ρ >> tRel)]) ≅ (cod[b .: (ρ >> tRel)]) ]< wl'' >    }.

  Arguments PiRedTyPack : clear implicits.

  Definition pack@{i j k l} {wl Γ A l} (ΠA : PiRedTy@{k} wl Γ A)
    (ΠAad : PiRedTyAdequate (LogRel@{i j k l} l) ΠA) 
    : PiRedTyPack@{i j k l} wl Γ A l.
  Proof.
    destruct ΠA as [dom cod]; destruct ΠAad; cbn in *.
    unshelve refine (Build_PiRedTyPack wl Γ A l dom cod _ _ _ _ domN0 _ _ _ _).
    1:intros; econstructor ; now unshelve apply domAd.
    2: now intros ; econstructor ; eapply codAd.
    all: eassumption.
  Defined.
  
  Definition toPiRedTy@{i j k l} {wl Γ A l} (ΠA : PiRedTyPack@{i j k l} wl Γ A l) :
    PiRedTy@{k} wl Γ A.
  Proof.
    destruct ΠA as [dom cod ????? domRed codomN codRed codExt].
    unshelve econstructor; [exact dom|exact cod|..].
    1,5-8: assumption.
    * intros; now eapply domRed.
    * intros; now eapply codomN.
    * intros; now eapply codRed.
    * intros; now eapply codExt.
  Defined.
  
  Definition toPiRedTyAd@{i j k l} {wl Γ A l} (ΠA : PiRedTyPack@{i j k l} wl Γ A l) :
    PiRedTyAdequate (LogRel@{i j k l} l) (toPiRedTy ΠA).
  Proof.
    destruct ΠA as [dom cod ????? domRed codomN codRed ?].
    unshelve econstructor; cbn; intros; [eapply domRed|eapply codRed].
  Defined.  

  Lemma pack_eta @{i j k l} {wl Γ A l} (ΠA : PiRedTyPack@{i j k l} wl Γ A l) :
    pack _ (toPiRedTyAd ΠA) = ΠA.
  Proof. destruct ΠA; reflexivity. Qed.

  Lemma pack_beta @{i j k l} {wl Γ A l} (ΠA : PiRedTy@{k} wl Γ A)
    (ΠAad : PiRedTyAdequate (LogRel@{i j k l} l) ΠA)  :
    toPiRedTy (pack _ ΠAad) = ΠA.
  Proof. destruct ΠA; destruct ΠAad; reflexivity. Qed.

  Lemma pack_beta_ad @{i j k l} {wl Γ A l} (ΠA : PiRedTy@{k} wl Γ A)
    (ΠAad : PiRedTyAdequate (LogRel@{i j k l} l) ΠA)  :
    toPiRedTyAd (pack _ ΠAad) = ΠAad.
  Proof. destruct ΠA; destruct ΠAad; reflexivity. Qed.

  Definition LRPi'@{i j k l} {l wl Γ A} (ΠA : PiRedTyPack@{i j k l} wl Γ A l)
    : [ LogRel@{i j k l} l | Γ ||- A ]< wl > :=
    LRbuild (LRPi (LogRelRec l) _ (toPiRedTyAd ΠA)).

  Definition prod@{i j k l} {wl l Γ A} (ΠA : PiRedTyPack@{i j k l} wl Γ A l) : term :=
    tProd (dom ΠA) (cod ΠA).

  Lemma whne_noΠ `{!RedTypeProperties} {wl Γ A} : [Γ ||-Πd A]< wl > -> whne A -> False.
  Proof.
    intros [?? r] h.
    pose proof (UntypedReduction.red_whne _ _ (redtywf_red r) h).
    subst; inversion h.
  Qed.

End PiRedTyPack.

Arguments PiRedTyPack : clear implicits.
Arguments PiRedTyPack {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _.

End PiRedTyPack.

Export PiRedTyPack(PiRedTyPack,Build_PiRedTyPack, LRPi').
Notation "[ Γ ||-Π< l > A ]< wl >" := (PiRedTyPack wl Γ A l) (at level 0, wl, Γ, l, A at level 50).

Section LogRelRecFoldLemmas.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{TypeNf ta} `{TypeNe ta} `{!RedTerm ta} `{TermNf ta} `{TermNe ta}.

  Lemma RedTyRecFwd {wl l Γ A t} (h : [Γ ||-U<l> A]< wl >) : 
    [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t]< wl > ->
    [LogRel (URedTy.level h) | Γ ||- t ]< wl >.
  Proof.
    destruct h as [? lt]; cbn. 
    pattern level, l , lt; induction lt.
    cbn. easy. 
  Defined.

  Lemma RedTyRecBwd {wl l Γ A t} (h : [Γ ||-U<l> A]< wl >) : 
    [LogRel (URedTy.level h) | Γ ||- t ]< wl > ->
    [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t]< wl >.
  Proof.
    destruct h as [? lt]; cbn.
    pattern level, l , lt; induction lt.
    cbn. easy. 
  Defined.

  (* This is a duplicate of the above, no ? *)
  Lemma LogRelRec_unfold {wl Γ l A t eqTy redTm eqTm} (h: [Γ ||-U<l> A]< wl >) :
    LogRelRec l (URedTy.level h) (URedTy.lt h) wl Γ t eqTy redTm eqTm <~>
    LogRel (URedTy.level h) wl Γ t eqTy redTm eqTm.
  Proof.
    destruct l; [destruct (elim (URedTy.lt h))|].
    destruct h; inversion lt; subst; cbn; now split.
  Qed.


  Lemma TyEqRecFwd {wl l Γ A t u} (h : [Γ ||-U<l> A]< wl >) 
    (lr : [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t]< wl >) :
    [lr | Γ ||- t ≅ u]< wl > <~> [RedTyRecFwd h lr | Γ ||- t ≅ u]< wl >.
  Proof.
    unfold RedTyRecFwd.
    destruct h as [? lt]; cbn in *.
    induction lt; cbn; split; easy.
  Qed.

  Lemma TyEqRecBwd {wl l Γ A t u} (h : [Γ ||-U<l> A]< wl >) 
    (lr : [LogRel (URedTy.level h) | Γ ||- t ]< wl >) :
    [lr | Γ ||- t ≅ u]< wl > <~> [RedTyRecBwd h lr | Γ ||- t ≅ u]< wl >.
  Proof.
    unfold RedTyRecBwd.
    destruct h as [? lt]; cbn in *.
    induction lt; cbn; split; easy.
  Qed.

End LogRelRecFoldLemmas.

Section NatPropProperties.
  Context `{GenericTypingProperties}.
  Lemma NatProp_whnf {wl Γ A t} {NA : [Γ ||-Nat A]< wl >} : NatProp NA t -> whnf t.
  Proof.  intros [ | | ? []]; now (econstructor; eapply tm_ne_whne). Qed.

  Lemma NatPropEq_whnf {wl Γ A t u} {NA : [Γ ||-Nat A]< wl >} : NatPropEq NA t u -> whnf t × whnf u.
  Proof.  intros [ | | ? ? []]; split; now (econstructor; eapply tm_ne_whne). Qed.

End NatPropProperties.


Section BoolPropProperties.
  Context `{GenericTypingProperties}.
  Lemma BoolProp_whnf {wl Γ A t} {NA : [Γ ||-Bool A]< wl >} : BoolProp NA t -> whnf t.
  Proof.  intros [ | | ? []]; now (econstructor; eapply tm_ne_whne). Qed.

  Lemma BoolPropEq_whnf {wl Γ A t u} {NA : [Γ ||-Bool A]< wl >} : BoolPropEq NA t u -> whnf t × whnf u.
  Proof.  intros [ | | ? ? []]; split; now (econstructor; eapply tm_ne_whne). Qed.

End BoolPropProperties.

Section EmptyPropProperties.
  Context `{GenericTypingProperties}.
  Lemma EmptyProp_whnf {wl Γ A t} {NA : [Γ ||-Empty A]< wl >} : @EmptyProp _ _ _ _ wl Γ t -> whnf t.
  Proof.  intros [ ? []]; now (econstructor; eapply tm_ne_whne). Qed.

  Lemma EmptyPropEq_whnf {wl Γ A t u} {NA : [Γ ||-Empty A]< wl >} : @EmptyPropEq _ _ _ wl Γ t u -> whnf t × whnf u.
  Proof.  intros [ ? ? []]; split; now (econstructor; eapply tm_ne_whne). Qed.

End EmptyPropProperties.

(* A&Y: We prove the hand-crafted induction principles here: *)

Lemma EmptyRedInduction :
  forall {ta : tag} {H : WfType ta} {H0 : RedType ta} {H1 : Typing ta}
    {H2 : ConvNeuConv ta} {H3 : ConvTerm ta} {H4 : RedTerm ta} 
    {H5 : TermNe ta} (wl : wfLCon) (Γ : context) (A : term) (NA : [Γ ||-Empty A]< wl >)
    (P : forall t : term, [Γ ||-Empty t : A | NA]< wl > -> Type)
    (P0 : forall t : term, EmptyProp Γ t -> Type),
    (forall (t nf : term) (red : [Γ |-[ ta ] t :⇒*: nf : tEmpty]< wl >)
       (eq : [Γ |-[ ta ] nf ≅ nf : tEmpty]< wl >) (prop : EmptyProp Γ nf),
        P0 nf prop -> P t (Build_EmptyRedTm nf red eq prop)) ->
    (forall (ne : term) (r : [Γ ||-NeNf ne : tEmpty]< wl >), P0 ne (EmptyRedTm.neR r)) ->
    (forall (t : term) (n : [Γ ||-Empty t : A | NA]< wl >), P t n)
      × (forall (t : term) (n : EmptyProp Γ t), P0 t n).
Proof.
  intros. split.
  - intros. induction n.
    eapply X. destruct prop. eapply X0.
  - intros. induction n. eapply X0.
Qed.


Lemma EmptyRedEqInduction :
  forall {ta : tag} {H0 : WfType ta} {H2 : RedType ta} {H3 : Typing ta}
    {H4 : ConvNeuConv ta} {H5 : ConvTerm ta} {H6 : RedTerm ta} 
    {H7 : TermNe ta} (wl : wfLCon) (Γ : context) (A : term) (NA : [Γ ||-Empty A]< wl >)
    (P : forall t t0 : term, [Γ ||-Empty t ≅ t0 : A | NA]< wl > -> Type)
    (P0 : forall t t0 : term, EmptyPropEq Γ t t0 -> Type),
    (forall (t u nfL nfR : term) (redL : [Γ |-[ ta ] t :⇒*: nfL : tEmpty]< wl >)
       (redR : [Γ |-[ ta ] u :⇒*: nfR : tEmpty]< wl >) (eq : [Γ |-[ ta ] nfL ≅ nfR : tEmpty]< wl >)
       (prop : EmptyPropEq Γ nfL nfR),
        P0 nfL nfR prop -> P t u (Build_EmptyRedTmEq nfL nfR redL redR eq prop)) ->
    (forall (ne ne' : term) (r : [Γ ||-NeNf ne ≅ ne' : tEmpty]< wl >),
        P0 ne ne' (EmptyRedTmEq.neReq r)) ->
    (forall (t t0 : term) (n : [Γ ||-Empty t ≅ t0 : A | NA]< wl >), P t t0 n)
      × (forall (t t0 : term) (n : EmptyPropEq Γ t t0), P0 t t0 n).
Proof.
  intros.
  split.
  - intros t t0 n. induction n.
    eapply X; eauto. destruct prop; eauto.
  - intros. induction n. eapply X0.
Qed.
