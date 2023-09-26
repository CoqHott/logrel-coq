(** * LogRel.LogicalRelation: Definition of the logical relation *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping.

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
  context               ->
  term                  ->
  (term -> Type@{i})         ->
  (term -> Type@{i})         ->
  (term -> term -> Type@{i}) ->
  Type@{j}.

(** An LRPack contains the data corresponding to the codomain of RedRel seen as a functional relation. *)

Module LRPack.

  Record LRPack@{i} {Γ : context} {A : term} :=
  {
    eqTy : term -> Type@{i};
    redTm : term -> Type@{i};
    eqTm :  term -> term -> Type@{i};
  }.

  Arguments LRPack : clear implicits.

End LRPack.

Export LRPack(LRPack,Build_LRPack).

Notation "[ P | Γ ||- A ≅ B ]" := (@LRPack.eqTy Γ A P B).
Notation "[ P | Γ ||- t : A ]" := (@LRPack.redTm Γ A P t).
Notation "[ P | Γ ||- t ≅ u : A ]" := (@LRPack.eqTm Γ A P t u).

(** An LRPack is adequate wrt. a RedRel when its three unpacked components are. *)
Definition LRPackAdequate@{i j} {Γ : context} {A : term}
  (R : RedRel@{i j}) (P : LRPack@{i} Γ A) : Type@{j} :=
  R Γ A P.(LRPack.eqTy) P.(LRPack.redTm) P.(LRPack.eqTm).

Arguments LRPackAdequate _ _ /.

Module LRAd.
  
  Record > LRAdequate@{i j} {Γ : context} {A : term} {R : RedRel@{i j}} : Type :=
  {
    pack :> LRPack@{i} Γ A ;
    adequate :> LRPackAdequate@{i j} R pack
  }.

  Arguments LRAdequate : clear implicits.
  Arguments Build_LRAdequate {_ _ _ _}.

End LRAd.

Export LRAd(LRAdequate,Build_LRAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion LRAd.pack : LRAdequate >-> LRPack.
Coercion LRAd.adequate : LRAdequate >-> LRPackAdequate.

(* TODO : update these for LRAdequate *)

Notation "[ R | Γ ||- A ]"              := (@LRAdequate Γ A R).
Notation "[ R | Γ ||- A ≅ B | RA ]"     := (RA.(@LRAd.pack Γ A R).(LRPack.eqTy) B).
Notation "[ R | Γ ||- t : A | RA ]"     := (RA.(@LRAd.pack Γ A R).(LRPack.redTm) t).
Notation "[ R | Γ ||- t ≅ u : A | RA ]" := (RA.(@LRAd.pack Γ A R).(LRPack.eqTm) t u).

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
    `{WfType ta} `{ConvNeuConv ta} `{RedType ta}
    {Γ : context} {A : term}
  : Set := {
    ty : term;
    red : [ Γ |- A :⤳*: ty];
    eq : [ Γ |- ty ~ ty : U] ;
  }.

  Arguments neRedTy {_ _ _ _}.

End neRedTy.

Export neRedTy(neRedTy, Build_neRedTy).
Notation "[ Γ ||-ne A ]" := (neRedTy Γ A).

Module neRedTyEq.

  Record neRedTyEq `{ta : tag}
    `{WfType ta} `{ConvNeuConv ta} `{RedType ta}
    {Γ : context} {A B : term} {neA : [ Γ ||-ne A ]}
  : Set := {
    ty   : term;
    red  : [ Γ |- B :⤳*: ty];
    eq  : [ Γ |- neA.(neRedTy.ty) ~ ty : U];
  }.

  Arguments neRedTyEq {_ _ _ _}.

End neRedTyEq.

Export neRedTyEq(neRedTyEq,Build_neRedTyEq).
Notation "[ Γ ||-ne A ≅ B | R ]" := (neRedTyEq Γ A B R).

Module neRedTm.

  Record neRedTm `{ta : tag}
    `{WfType ta} `{RedType ta}
    `{Typing ta} `{ConvNeuConv ta} `{ConvType ta} `{RedTerm ta}
    {Γ : context} {t A : term} {R : [ Γ ||-ne A ]}
  : Set := {
    te  : term;
    red  : [ Γ |- t :⤳*: te : R.(neRedTy.ty)];
    eq : [Γ |- te ~ te : R.(neRedTy.ty)] ;
  }.

  Arguments neRedTm {_ _ _ _ _ _ _}.

End neRedTm.

Export neRedTm(neRedTm, Build_neRedTm).

Notation "[ Γ ||-ne t : A | B ]" := (neRedTm Γ t A B).

Module neRedTmEq.

  Record neRedTmEq `{ta : tag}
    `{WfType ta} `{RedType ta}
    `{Typing ta} `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t u A : term} {R : [ Γ ||-ne A ]}
  : Set := {
    termL     : term;
    termR     : term;
    redL      : [ Γ |- t :⤳*: termL : R.(neRedTy.ty) ];
    redR      : [ Γ |- u :⤳*: termR : R.(neRedTy.ty) ];
    eq : [ Γ |- termL ~ termR : R.(neRedTy.ty)] ;
  }.

  Arguments neRedTmEq {_ _ _ _ _ _ _ _}.

End neRedTmEq.

Export neRedTmEq(neRedTmEq, Build_neRedTmEq).
Notation "[ Γ ||-ne t ≅ u : A | R ] " := (neRedTmEq Γ t u A R).

(** ** Reducibility of the universe *)

Module URedTy.

  Record URedTy `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
    {l} {Γ : context} {A : term}
  : Set := {
    level  : TypeLevel;
    lt  : level << l;
    wfCtx : [|- Γ] ;
    red : [ Γ |- A  :⤳*: U ]
  }.

  Arguments URedTy {_ _ _ _}.

End URedTy.

Export URedTy(URedTy,Build_URedTy).


Notation "[ Γ ||-U< l > A ]" := (URedTy l Γ A) (at level 0, Γ, l, A at level 50).

Module URedTyEq.

  Record URedTyEq `{ta : tag} `{!WfType ta} `{!RedType ta} 
    {Γ : context} {B : term} : Set := {
    red : [Γ |- B :⤳*: U]
  }.

  Arguments URedTyEq : clear implicits.
  Arguments URedTyEq {_ _ _}.

End URedTyEq.

Export URedTyEq(URedTyEq,Build_URedTyEq).

Notation "[ Γ ||-U≅ B ]" := (URedTyEq Γ B).

Module URedTm.

  Record URedTm@{i j} `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {t A : term} {R : [Γ ||-U<l> A]}
  : Type@{j} := {
    te : term;
    red : [ Γ |- t :⤳*: te : U ];
    type : isType te;
    eqr : [Γ |- te ≅ te : U];
    rel : [rec R.(URedTy.lt) | Γ ||- t ] ;
  }.

  Arguments URedTm {_ _ _ _ _ _ _ _} rec.

  Record URedTmEq@{i j} `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {t u A : term} {R : [Γ ||-U<l> A]}
  : Type@{j} := {
      redL : URedTm (@rec) Γ t A R ;
      redR : URedTm (@rec) Γ u A R ;
      eq   : [ Γ |- redL.(te) ≅ redR.(te) : U ];
      relL    : [ rec R.(URedTy.lt) | Γ ||- t ] ;
      relR    : [ rec R.(URedTy.lt) | Γ ||- u ] ;
      relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u | relL ] ;
  }.

  Arguments URedTmEq {_ _ _ _ _ _ _ _} rec.

End URedTm.

Export URedTm(URedTm,Build_URedTm,URedTmEq,Build_URedTmEq).
Notation "[ R | Γ ||-U t : A | l ]" := (URedTm R Γ t A l) (at level 0, R, Γ, t, A, l at level 50).
Notation "[ R | Γ ||-U t ≅ u : A | l ]" := (URedTmEq R Γ t u A l) (at level 0, R, Γ, t, u, A, l at level 50).

(** ** Reducibility of a polynomial A,, B  *)

Module PolyRedPack.

  (* A polynomial is a pair (shp, pos) of a type of shapes [Γ |- shp] and
    a dependent type of positions [Γ |- pos] *)
  (* This should be used as a common entry for Π, Σ, W and M types *)

  Record PolyRedPack@{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta}
    {Γ : context} {shp pos : term}
  : Type (* @ max(Set, i+1) *) := {
    shpTy : [Γ |- shp];
    posTy : [Γ ,, shp |- pos];
    shpRed {Δ} (ρ : Δ ≤ Γ) : [ |- Δ ] -> LRPack@{i} Δ shp⟨ρ⟩ ;
    posRed {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
        [ (shpRed ρ h) |  Δ ||- a : shp⟨ρ⟩] ->
        LRPack@{i} Δ (pos[a .: (ρ >> tRel)]) ;
    posExt
      {Δ a b}
      (ρ : Δ ≤ Γ)
      (h :  [ |- Δ ])
      (ha : [ (shpRed ρ h) | Δ ||- a : shp⟨ρ⟩ ]) :
      [ (shpRed ρ h) | Δ ||- b : shp⟨ρ⟩] ->
      [ (shpRed ρ h) | Δ ||- a ≅ b : shp⟨ρ⟩] ->
      [ (posRed ρ h ha) | Δ ||- (pos[a .: (ρ >> tRel)]) ≅ (pos[b .: (ρ >> tRel)]) ]
  }.

  Arguments PolyRedPack {_ _ _ _}.

  (** We separate the recursive "data", ie the fact that we have reducibility data (an LRPack)
  for the domain and codomain, and the fact that these are in the graph of the logical relation.
  This is crucial for Coq to accept the definition, because it makes the nesting simple enough
  to be accepted. We later on show an induction principle that does not have this separation to
  make reasoning easier. *)
  Record PolyRedPackAdequate@{i j} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} {shp pos : term}
    {Γ : context} {R : RedRel@{i j}}  {PA : PolyRedPack@{i} Γ shp pos}
  : Type@{j} := {
    shpAd {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) : LRPackAdequate@{i j} R (PA.(shpRed) ρ h);
    posAd {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ PA.(shpRed) ρ h | Δ ||- a : shp⟨ρ⟩ ])
      : LRPackAdequate@{i j} R (PA.(posRed) ρ h ha);
  }.

  Arguments PolyRedPackAdequate {_ _ _ _ _ _ _}.

End PolyRedPack.

Export PolyRedPack(PolyRedPack, Build_PolyRedPack, PolyRedPackAdequate, Build_PolyRedPackAdequate).

Module PolyRedEq.

  Record PolyRedEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} 
    {Γ : context} {shp pos: term} {PA : PolyRedPack Γ shp pos} {shp' pos' : term}
  : Type := {
    shpRed {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ PA.(PolyRedPack.shpRed) ρ h | Δ ||- shp⟨ρ⟩ ≅ shp'⟨ρ⟩ ];
    posRed {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ PA.(PolyRedPack.shpRed) ρ h | Δ ||- a : shp⟨ρ⟩]) :
      [ PA.(PolyRedPack.posRed) ρ h ha | Δ ||- pos[a .: (ρ >> tRel)] ≅ pos'[a .: (ρ >> tRel)] ];
  }.

  Arguments PolyRedEq {_ _ _ _ _ _ _}.

End PolyRedEq.

Export PolyRedEq(PolyRedEq, Build_PolyRedEq).
(* Nothing for reducibility of terms and reducible conversion of terms  *)

Module ParamRedTyPack.

  Record ParamRedTyPack@{i} {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A : term}
  : Type (* @ max(Set, i+1) *) := {
    dom : term ;
    cod : term ;
    outTy := T dom cod ;
    red : [Γ |- A :⤳*: T dom cod];
    eqdom : [Γ |- dom ≅ dom];
    eq : [Γ |- T dom cod ≅ T dom cod];
    polyRed : PolyRedPack@{i} Γ dom cod
  }.

  Arguments ParamRedTyPack {_ _ _ _ _ _}.

End ParamRedTyPack.

Export ParamRedTyPack(ParamRedTyPack, Build_ParamRedTyPack, outTy).
Coercion ParamRedTyPack.polyRed : ParamRedTyPack >-> PolyRedPack.
Arguments ParamRedTyPack.outTy /.

Module ParamRedTyEq.

  Record ParamRedTyEq {T : term -> term -> term}
    `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} {ΠA : ParamRedTyPack (T:=T) Γ A}
  : Type := {
    dom : term;
    cod : term;
    red : [Γ |- B :⤳*: T dom cod ];
    eqdom : [Γ |- ΠA.(ParamRedTyPack.dom) ≅ dom];
    eq  : [Γ |- T ΠA.(ParamRedTyPack.dom) ΠA.(ParamRedTyPack.cod) ≅ T dom cod ];
    polyRed : PolyRedEq ΠA dom cod
  }.

  Arguments ParamRedTyEq {_ _ _ _ _ _}.

End ParamRedTyEq.

Export ParamRedTyEq(ParamRedTyEq,Build_ParamRedTyEq).
Coercion ParamRedTyEq.polyRed : ParamRedTyEq >-> PolyRedEq.

(** ** Reducibility of product types *)

Definition PiRedTy `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} := 
  ParamRedTyPack (T:=tProd).

Definition PiRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A : term} (R : RedRel@{i j}) (ΠA : PiRedTy@{i} Γ A)
  : Type@{j} := PolyRedPackAdequate R ΠA.

(* keep ? *)
Module PiRedTy := ParamRedTyPack.
Notation "[ Γ ||-Πd A ]" := (PiRedTy Γ A).
  
Definition PiRedTyEq `{ta : tag} 
  `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
  {Γ : context} {A : term} (ΠA : PiRedTy Γ A) (B : term) :=
  ParamRedTyEq (T:=tProd) Γ A B ΠA.

(* keep ?*)
Module PiRedTyEq := ParamRedTyEq.
Notation "[ Γ ||-Π A ≅ B | ΠA ]" := (PiRedTyEq (Γ:=Γ) (A:=A) ΠA B).

Inductive isLRFun `{ta : tag} `{WfContext ta}
  `{WfType ta} `{ConvType ta} `{RedType ta} `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta}
  {Γ : context} {A : term} (ΠA : PiRedTy Γ A) : term -> Type :=
| LamLRFun : forall A' t : term,
  (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (domRed:= ΠA.(PolyRedPack.shpRed) ρ h),
      [domRed | Δ ||- (PiRedTy.dom ΠA)⟨ρ⟩ ≅ A'⟨ρ⟩]) ->
  (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
    (ha : [ ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ]),
      [ΠA.(PolyRedPack.posRed) ρ h ha | Δ ||- t[a .: (ρ >> tRel)] : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]]) ->
  isLRFun ΠA (tLambda A' t)
| NeLRFun : forall f : term, [Γ |- f ~ f : tProd (PiRedTy.dom ΠA) (PiRedTy.cod ΠA)] -> isLRFun ΠA f.

Module PiRedTm.

  Record PiRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t A : term} {ΠA : PiRedTy Γ A}
  : Type := {
    nf : term;
    red : [ Γ |- t :⤳*: nf : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ];
    isfun : isLRFun ΠA nf;
    refl : [ Γ |- nf ≅ nf : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ];
    app {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      : [ΠA.(PolyRedPack.posRed) ρ h ha | Δ ||- tApp nf⟨ρ⟩ a : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]] ;
    eq {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (domRed:= ΠA.(PolyRedPack.shpRed) ρ h)
      (ha : [ domRed | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      (hb : [ domRed | Δ ||- b : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      (eq : [ domRed | Δ ||- a ≅ b : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      : [ ΠA.(PolyRedPack.posRed) ρ h ha | Δ ||- tApp nf⟨ρ⟩ a ≅ tApp nf⟨ρ⟩ b : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)] ]
  }.

  Arguments PiRedTm {_ _ _ _ _ _ _ _ _}.

End PiRedTm.

Export PiRedTm(PiRedTm,Build_PiRedTm).
Notation "[ Γ ||-Π t : A | ΠA ]" := (PiRedTm Γ t A ΠA).

Module PiRedTmEq.

  Record PiRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t u A : term} {ΠA : PiRedTy Γ A}
  : Type := {
    redL : [ Γ ||-Π t : A | ΠA ] ;
    redR : [ Γ ||-Π u : A | ΠA ] ;
    eq : [ Γ |- redL.(PiRedTm.nf) ≅ redR.(PiRedTm.nf) : tProd ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ];
    eqApp {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ] )
      : [ ΠA.(PolyRedPack.posRed) ρ h ha | Δ ||-
          tApp redL.(PiRedTm.nf)⟨ρ⟩ a ≅ tApp redR.(PiRedTm.nf)⟨ρ⟩ a : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]]
  }.

  Arguments PiRedTmEq {_ _ _ _ _ _ _ _ _}.

End PiRedTmEq.

Export PiRedTmEq(PiRedTmEq,Build_PiRedTmEq).

Notation "[ Γ ||-Π t ≅ u : A | ΠA ]" := (PiRedTmEq Γ t u A ΠA).

(** ** Reducibility of dependent sum types *)

Definition SigRedTy `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} := 
  ParamRedTyPack (T:=tSig).

Definition SigRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A : term} (R : RedRel@{i j}) (ΣA : SigRedTy@{i} Γ A)
  : Type@{j} := PolyRedPackAdequate R ΣA.
  
Definition SigRedTyEq `{ta : tag} 
  `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
  {Γ : context} {A : term} (ΠA : SigRedTy Γ A) (B : term) :=
  ParamRedTyEq (T:=tSig) Γ A B ΠA.

Module SigRedTm.

  Record SigRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A : term} {ΣA : SigRedTy Γ A} {t : term}
  : Type := {
    nf : term;
    red : [ Γ |- t :⤳*: nf : ΣA.(outTy) ];
    isfun : isWfPair Γ ΣA.(PiRedTy.dom) ΣA.(PiRedTy.cod) nf;
    refl : [ Γ |- nf ≅ nf : ΣA.(outTy) ];
    fstRed {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- tFst nf⟨ρ⟩ : ΣA.(ParamRedTyPack.dom)⟨ρ⟩] ;
    sndRed  {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ΣA.(PolyRedPack.posRed) ρ h (fstRed ρ h) | Δ ||- tSnd nf⟨ρ⟩ : _] ;
  }.

  Arguments SigRedTm {_ _ _ _ _ _ _ _ _ _ _}.

End SigRedTm.

Export SigRedTm(SigRedTm,Build_SigRedTm).
Notation "[ Γ ||-Σ t : A | ΣA ]" := (SigRedTm (Γ:=Γ) (A:=A) ΣA t) (at level 0, Γ, t, A, ΣA at level 50).

Module SigRedTmEq.

  Record SigRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A : term} {ΣA : SigRedTy Γ A} {t u : term}
  : Type := {
    redL : [ Γ ||-Σ t : A | ΣA ] ;
    redR : [ Γ ||-Σ u : A | ΣA ] ;
    eq : [ Γ |- redL.(SigRedTm.nf) ≅ redR.(SigRedTm.nf) : ΣA.(outTy) ];
    eqFst {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- tFst redL.(SigRedTm.nf)⟨ρ⟩ ≅ tFst redR.(SigRedTm.nf)⟨ρ⟩ : ΣA.(ParamRedTyPack.dom)⟨ρ⟩] ;
    eqSnd {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (redfstL := redL.(SigRedTm.fstRed) ρ h) :
      [ΣA.(PolyRedPack.posRed) ρ h redfstL | Δ ||- tSnd redL.(SigRedTm.nf)⟨ρ⟩ ≅ tSnd redR.(SigRedTm.nf)⟨ρ⟩ : _] ;
  }.

  Arguments SigRedTmEq {_ _ _ _ _ _ _ _ _ _ _}.

End SigRedTmEq.

Export SigRedTmEq(SigRedTmEq,Build_SigRedTmEq).

Notation "[ Γ ||-Σ t ≅ u : A | ΣA ]" := (SigRedTmEq (Γ:=Γ) (A:=A) ΣA t u) (at level 0, Γ, t, u, A, ΣA at level 50).



(** ** Reducibility of neutrals at an arbitrary type *)

Module NeNf.
  Record RedTm `{ta : tag} `{Typing ta} `{ConvNeuConv ta} {Γ k A} : Set :=
    {
      ty : [Γ |- k : A] ;
      refl : [Γ |- k ~ k : A]
    }.
  Arguments RedTm {_ _ _}.

  Record RedTmEq `{ta : tag} `{ConvNeuConv ta} {Γ k l A} : Set :=
    {
      conv : [Γ |- k ~ l : A]
    }.

  Arguments RedTmEq {_ _}.
End NeNf.

Notation "[ Γ ||-NeNf k : A ]" := (NeNf.RedTm Γ k A) (at level 0, Γ, k, A at level 50).
Notation "[ Γ ||-NeNf k ≅ l : A ]" := (NeNf.RedTmEq Γ k l A) (at level 0, Γ, k, l, A at level 50).

(** ** Reducibility of natural number type *)
Module NatRedTy.

  Record NatRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A : term}
  : Set := 
  {
    red : [Γ |- A :⤳*: tNat]
  }.

  Arguments NatRedTy {_ _ _}.
End NatRedTy.

Export NatRedTy(NatRedTy, Build_NatRedTy).
Notation "[ Γ ||-Nat A ]" := (NatRedTy Γ A) (at level 0, Γ, A at level 50).

Module NatRedTyEq.

  Record NatRedTyEq `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A : term} {NA : NatRedTy Γ A} {B : term}
  : Set := {
    red : [Γ |- B :⤳*: tNat];
  }.

  Arguments NatRedTyEq {_ _ _ _ _}.

End NatRedTyEq.

Export NatRedTyEq(NatRedTyEq,Build_NatRedTyEq).

Notation "[ Γ ||-Nat A ≅ B | RA ]" := (@NatRedTyEq _ _ _ Γ A RA B) (at level 0, Γ, A, B, RA at level 50).

Module NatRedTm.
Section NatRedTm.
  Context `{ta : tag} `{WfType ta} 
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Inductive NatRedTm {Γ : context} {A: term} {NA : NatRedTy Γ A} : term -> Set :=
  | Build_NatRedTm {t}
    (nf : term)
    (red : [Γ |- t :⤳*: nf : tNat ])
    (eq : [Γ |- nf ≅ nf : tNat])
    (prop : NatProp nf) : NatRedTm t

  with NatProp {Γ : context} {A: term} {NA : NatRedTy Γ A} : term -> Set :=
  | zeroR  : NatProp tZero
  | succR {n} :
    NatRedTm n ->
    NatProp (tSucc n)
  | neR {ne} : [Γ ||-NeNf ne : tNat] -> NatProp ne.


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
  intros ??? PRed PProp **; split; now apply (_NatRedInduction _ _ _ PRed PProp).
Defined.

Definition nf {Γ A n} {NA : [Γ ||-Nat A]} : @NatRedTm _ _ NA n -> term.
Proof.
  intros [? nf]. exact nf.
Defined.

Definition red {Γ A n} {NA : [Γ ||-Nat A]} (Rn : @NatRedTm _ _ NA n) : [Γ |- n :⤳*: nf Rn : tNat].
Proof.
  dependent inversion Rn; subst; cbn; tea.
Defined.

End NatRedTm.
Arguments NatRedTm {_ _ _ _ _ _ _ _ _}.
Arguments NatProp {_ _ _ _ _ _ _ _ _}.

End NatRedTm.

Export NatRedTm(NatRedTm,Build_NatRedTm, NatProp, NatRedInduction).

Notation "[ Γ ||-Nat t : A | RA ]" := (@NatRedTm _ _ _ _ _ _ _ Γ A RA t) (at level 0, Γ, t, A, RA at level 50).


Module NatRedTmEq.
Section NatRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Inductive NatRedTmEq {Γ : context} {A: term} {NA : NatRedTy Γ A} : term -> term -> Set :=
  | Build_NatRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⤳*: nfL : tNat])
    (redR : [Γ |- u :⤳*: nfR : tNat ])
    (eq : [Γ |- nfL ≅ nfR : tNat])
    (prop : NatPropEq nfL nfR) : NatRedTmEq t u

  with NatPropEq {Γ : context} {A: term} {NA : NatRedTy Γ A} : term -> term -> Set :=
  | zeroReq :
    NatPropEq tZero tZero
  | succReq {n n'} :
    NatRedTmEq n n' ->
    NatPropEq (tSucc n) (tSucc n')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tNat] -> NatPropEq ne ne'.

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
  intros ??? PRedEq PPropEq **; split; now apply (_NatRedEqInduction _ _ _ PRedEq PPropEq).
Defined.

End NatRedTmEq.
Arguments NatRedTmEq {_ _ _ _ _ _ _ _ _}.
Arguments NatPropEq {_ _ _ _ _ _ _ _ _}.
End NatRedTmEq.

Export NatRedTmEq(NatRedTmEq,Build_NatRedTmEq, NatPropEq, NatRedEqInduction).

Notation "[ Γ ||-Nat t ≅ u : A | RA ]" := (@NatRedTmEq _ _ _ _ _ _ _ Γ A RA t u) (at level 0, Γ, t, u, A, RA at level 50).

(** ** Reducibility of empty type *)
Module EmptyRedTy.

  Record EmptyRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A : term}
  : Set := 
  {
    red : [Γ |- A :⤳*: tEmpty]
  }.

  Arguments EmptyRedTy {_ _ _}.
End EmptyRedTy.

Export EmptyRedTy(EmptyRedTy, Build_EmptyRedTy).
Notation "[ Γ ||-Empty A ]" := (EmptyRedTy Γ A) (at level 0, Γ, A at level 50).

Module EmptyRedTyEq.

  Record EmptyRedTyEq `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A : term} {NA : EmptyRedTy Γ A} {B : term}
  : Set := {
    red : [Γ |- B :⤳*: tEmpty];
  }.

  Arguments EmptyRedTyEq {_ _ _ _ _}.

End EmptyRedTyEq.

Export EmptyRedTyEq(EmptyRedTyEq,Build_EmptyRedTyEq).

Notation "[ Γ ||-Empty A ≅ B | RA ]" := (@EmptyRedTyEq _ _ _ Γ A RA B) (at level 0, Γ, A, B, RA at level 50).

Module EmptyRedTm.
Section EmptyRedTm.
  Context `{ta : tag} `{WfType ta} 
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Inductive EmptyProp {Γ : context} : term -> Set :=
  | neR {ne} : [Γ ||-NeNf ne : tEmpty] -> EmptyProp ne.

  Inductive EmptyRedTm {Γ : context} {A: term} {NA : EmptyRedTy Γ A} : term -> Set :=
  | Build_EmptyRedTm {t}
    (nf : term)
    (red : [Γ |- t :⤳*: nf : tEmpty ])
    (eq : [Γ |- nf ≅ nf : tEmpty])
    (prop : @EmptyProp Γ nf) : EmptyRedTm t.

Definition nf {Γ A n} {NA : [Γ ||-Empty A]} : @EmptyRedTm _ _ NA n -> term.
Proof.
  intros [? nf]. exact nf.
Defined.

Definition red {Γ A n} {NA : [Γ ||-Empty A]} (Rn : @EmptyRedTm _ _ NA n) : [Γ |- n :⤳*: nf Rn : tEmpty].
Proof.
  dependent inversion Rn; subst; cbn; tea.
Defined.

End EmptyRedTm.
Arguments EmptyRedTm {_ _ _ _ _ _ _ _ _}.
Arguments EmptyProp {_ _ _}.

End EmptyRedTm.

Export EmptyRedTm(EmptyRedTm,Build_EmptyRedTm, EmptyProp).

Notation "[ Γ ||-Empty t : A | RA ]" := (@EmptyRedTm _ _ _ _ _ _ _ Γ A RA t) (at level 0, Γ, t, A, RA at level 50).


Module EmptyRedTmEq.
Section EmptyRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Inductive EmptyPropEq {Γ : context} : term -> term -> Set :=
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tEmpty] -> EmptyPropEq ne ne'.

  Inductive EmptyRedTmEq {Γ : context} {A: term} {NA : EmptyRedTy Γ A} : term -> term -> Set :=
  | Build_EmptyRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⤳*: nfL : tEmpty])
    (redR : [Γ |- u :⤳*: nfR : tEmpty ])
    (eq : [Γ |- nfL ≅ nfR : tEmpty])
    (prop : @EmptyPropEq Γ nfL nfR) : EmptyRedTmEq t u.

End EmptyRedTmEq.
Arguments EmptyRedTmEq {_ _ _ _ _ _ _ _ _}.
Arguments EmptyPropEq {_ _}.
End EmptyRedTmEq.

Export EmptyRedTmEq(EmptyRedTmEq,Build_EmptyRedTmEq, EmptyPropEq).

Notation "[ Γ ||-Empty t ≅ u : A | RA ]" := (@EmptyRedTmEq _ _ _ _ _ _ _ Γ A RA t u) (at level 0, Γ, t, u, A, RA at level 50).


(** ** Logical relation for Identity types *)

Module IdRedTyPack.
  
  Record IdRedTyPack@{i} `{ta : tag} `{WfContext ta} `{WfType ta} `{RedType ta} `{ConvType ta}
    {Γ : context} {A : term}
  : Type := 
  {
    ty : term ;
    lhs : term ;
    rhs : term ;
    outTy := tId ty lhs rhs ;
    red : [Γ |- A :⤳*: outTy] ;
    eq : [Γ |- outTy ≅ outTy] ;
    tyRed : LRPack@{i} Γ ty ;
    lhsRed : [ tyRed | Γ ||- lhs : _ ] ;
    rhsRed : [ tyRed | Γ ||- rhs : _ ] ;
    (* Bake in PER property for reducible conversion at ty  to cut dependency cycles *)
    lhsRedRefl : [ tyRed | Γ ||- lhs ≅ lhs : _ ] ;
    rhsRedRefl : [ tyRed | Γ ||- rhs ≅ rhs : _ ] ;
    tyPER : PER (fun t u => [tyRed | _ ||- t ≅ u : _]) ;
    tyKripke : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), LRPack@{i} Δ ty⟨ρ⟩ ;
    tyKripkeEq : forall {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [|-Δ]) (wfΞ : [|-Ξ]) B,
      ρ' =1 ρ'' ∘w ρ -> [tyKripke ρ wfΔ | _ ||- _ ≅ B] -> [tyKripke ρ' wfΞ | _ ||- _ ≅ B⟨ρ''⟩];
    tyKripkeTm : forall {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [|-Δ]) (wfΞ : [|-Ξ]) t,
      ρ' =1 ρ'' ∘w ρ -> [tyKripke ρ wfΔ | _ ||- t : _] -> [tyKripke ρ' wfΞ | _ ||- t⟨ρ''⟩ : _];
    tyKripkeTmEq : forall {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [|-Δ]) (wfΞ : [|-Ξ]) t u,
      ρ' =1 ρ'' ∘w ρ -> [tyKripke ρ wfΔ | _ ||- t ≅ u : _] -> [tyKripke ρ' wfΞ | _ ||- t⟨ρ''⟩ ≅ u⟨ρ''⟩ : _];
  }.

  Record IdRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{RedType ta} `{ConvType ta}
    {Γ : context} {A : term} {R : RedRel@{i j}} {IA : IdRedTyPack@{i} (Γ:=Γ) (A:=A)} := 
    {
      tyAd : LRPackAdequate@{i j} R IA.(tyRed) ;
      tyKripkeAd : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), LRPackAdequate@{i j} R (IA.(tyKripke) ρ wfΔ) ;
    }.

  Arguments IdRedTyPack {_ _ _ _ _}.
  Arguments IdRedTyAdequate {_ _ _ _ _ _ _}.
  
End IdRedTyPack.

Export IdRedTyPack(IdRedTyPack, Build_IdRedTyPack, IdRedTyAdequate, Build_IdRedTyAdequate).
Set Printing Universes.

Module IdRedTyEq.

  Record IdRedTyEq@{i} `{ta : tag} `{WfContext ta} `{WfType ta} `{RedType ta} `{ConvType ta} `{ConvTerm ta}
    {Γ : context} {A : term} {IA : IdRedTyPack@{i} Γ A} {B : term}
  : Type := {
    ty : term ;
    lhs : term ;
    rhs : term ;
    outTy := tId ty lhs rhs ;
    red : [Γ |- B :⤳*: outTy];
    eq : [Γ |- IA.(IdRedTyPack.outTy) ≅ outTy] ;
    tyRed0 := IA.(IdRedTyPack.tyRed) ;
    tyRed : [ tyRed0 | _ ||- _ ≅ ty ] ;
    (* lhsConv : [ Γ |- IA.(IdRedTyPack.lhs) ≅ lhs : IA.(IdRedTyPack.ty) ] ;
    rhsConv : [ Γ |- IA.(IdRedTyPack.rhs) ≅ rhs : IA.(IdRedTyPack.ty) ] ; *)
    lhsRed : [ tyRed0 | _ ||- IA.(IdRedTyPack.lhs) ≅ lhs : _ ] ;
    rhsRed : [ tyRed0 | _ ||- IA.(IdRedTyPack.rhs) ≅ rhs : _ ] ;
  }.
  
  Arguments IdRedTyEq {_ _ _ _ _ _ _ _}.

End IdRedTyEq.

Export IdRedTyEq(IdRedTyEq,Build_IdRedTyEq).

Module IdRedTm.
Section IdRedTm.
  Universe i.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} 
    `{RedType ta} `{Typing ta} `{ConvType ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context} {A: term} {IA : IdRedTyPack@{i} Γ A}.

  Inductive IdProp : term ->  Type:=
  | reflR {A x} : 
    [Γ |- A] ->
    [Γ |- x : A] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- _ ≅ A] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.lhs) ≅ x : _ ] ->
    (* Should the index only be conversion ? *)
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.rhs) ≅ x : _ ] ->
    IdProp (tRefl A x)
  | neR {ne} : [Γ ||-NeNf ne : IA.(IdRedTyPack.outTy)] -> IdProp ne.

  Record IdRedTm  {t : term} : Type :=
    Build_IdRedTm {
      nf : term ;
      red : [Γ |- t :⤳*: nf : IA.(IdRedTyPack.outTy) ] ;
      eq : [Γ |- nf ≅ nf : IA.(IdRedTyPack.outTy)] ;
      prop : IdProp nf ;
  }. 

End IdRedTm.
Arguments IdRedTm {_ _ _ _ _ _ _ _ _ _ _}.
Arguments IdProp {_ _ _ _ _ _ _ _ _}.

End IdRedTm.

Export IdRedTm(IdRedTm,Build_IdRedTm, IdProp).


Module IdRedTmEq.
Section IdRedTmEq.
  Universe i.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context} {A: term} {IA : IdRedTyPack@{i} Γ A}.
  
  Inductive IdPropEq : term -> term -> Type :=
  | reflReq {A A' x x'} : 
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- x : A] ->
    [Γ |- x' : A'] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- _ ≅ A] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- _ ≅ A'] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.lhs) ≅ x : _ ] -> 
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.lhs) ≅ x' : _ ] -> 
    (* Should the indices only be conversion ? *)
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.rhs) ≅ x : _ ] ->
    [IA.(IdRedTyPack.tyRed) | _ ||- IA.(IdRedTyPack.rhs) ≅ x' : _ ] ->
    IdPropEq (tRefl A x) (tRefl A' x')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : IA.(IdRedTyPack.outTy)] -> IdPropEq ne ne'.

  Record IdRedTmEq  {t u : term} : Type :=
    Build_IdRedTmEq {
      nfL : term ;
      nfR : term ;
      redL : [Γ |- t :⤳*: nfL : IA.(IdRedTyPack.outTy) ] ;
      redR : [Γ |- u :⤳*: nfR : IA.(IdRedTyPack.outTy) ] ;
      eq : [Γ |- nfL ≅ nfR : IA.(IdRedTyPack.outTy)] ;
      prop : IdPropEq nfL nfR ;
  }. 

End IdRedTmEq.
Arguments IdRedTmEq {_ _ _ _ _ _ _ _ _ _ _}.
Arguments IdPropEq {_ _ _ _ _ _ _ _ _}.
End IdRedTmEq.

Export IdRedTmEq(IdRedTmEq,Build_IdRedTmEq, IdPropEq).


(** ** Definition of the logical relation *)

(** This simply bundles the different cases for reducibility already defined. *)

Unset Elimination Schemes.

Inductive LR@{i j k} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta}
  {l : TypeLevel} (rec : forall l', l' << l -> RedRel@{i j})
: RedRel@{j k} :=
  | LRU {Γ A} (H : [Γ ||-U<l> A]) :
      LR rec Γ A
      (fun B   => [Γ ||-U≅ B ])
      (fun t   => [ rec | Γ ||-U t     : A | H ])
      (fun t u => [ rec | Γ ||-U t ≅ u : A | H ])
  | LRne {Γ A} (neA : [ Γ ||-ne A ]) :
      LR rec Γ A
      (fun B   =>  [ Γ ||-ne A ≅ B     | neA])
      (fun t   =>  [ Γ ||-ne t     : A | neA])
      (fun t u =>  [ Γ ||-ne t ≅ u : A | neA])
  | LRPi {Γ : context} {A : term} (ΠA : PiRedTy@{j} Γ A) (ΠAad : PiRedTyAdequate@{j k} (LR rec) ΠA) :
    LR rec Γ A
      (fun B   => [ Γ ||-Π A ≅ B     | ΠA ])
      (fun t   => [ Γ ||-Π t     : A | ΠA ])
      (fun t u => [ Γ ||-Π t ≅ u : A | ΠA ])
  | LRNat {Γ A} (NA : [Γ ||-Nat A]) :
    LR rec Γ A (NatRedTyEq NA) (NatRedTm NA) (NatRedTmEq NA)
  | LREmpty {Γ A} (NA : [Γ ||-Empty A]) :
    LR rec Γ A (EmptyRedTyEq NA) (EmptyRedTm NA) (EmptyRedTmEq NA)
  | LRSig {Γ : context} {A : term} (ΣA : SigRedTy@{j} Γ A) (ΣAad : SigRedTyAdequate@{j k} (LR rec) ΣA) :
    LR rec Γ A (SigRedTyEq ΣA) (SigRedTm ΣA) (SigRedTmEq ΣA)
  | LRId {Γ A} (IA : IdRedTyPack@{j} Γ A) (IAad : IdRedTyAdequate@{j k} (LR rec) IA) :
    LR rec Γ A (IdRedTyEq IA) (IdRedTm IA) (IdRedTmEq IA)
  .
  
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
    `{!RedType ta} `{!RedTerm ta}.

  Definition rec0@{i j} (l' : TypeLevel) (h : l' << zero) : RedRel@{i j} :=
    match elim h with
    end.

  Definition LogRel0@{i j k} :=
    LR@{i j k} rec0@{i j}.

  Definition LRbuild0@{i j k} {Γ A rEq rTe rTeEq} :
    LogRel0@{i j k} Γ A rEq rTe rTeEq -> [ LogRel0@{i j k} | Γ ||- A ] :=
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

  Definition LRbuild@{i j k l} {Γ l A rEq rTe rTeEq} :
    LR@{j k l} (LogRelRec@{i j k} l) Γ A rEq rTe rTeEq -> [ LogRel l | Γ ||- A ] :=
    fun H => {|
      LRAd.pack := {| LRPack.eqTy := rEq ; LRPack.redTm := rTe ; LRPack.eqTm := rTeEq |} ;
      LRAd.adequate := H |}.

  Definition LRunbuild {Γ l A} :
  [ LogRel l | Γ ||- A ] ->
    ∑ rEq rTe rTeEq , LR (LogRelRec l) Γ A rEq rTe rTeEq :=
      fun H => (LRPack.eqTy H; LRPack.redTm H; LRPack.eqTm H; H.(LRAd.adequate)).

  Definition LRU_@{i j k l} {l Γ A} (H : [Γ ||-U<l> A])
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRU (LogRelRec l) H).

  Definition LRne_@{i j k l} l {Γ A} (neA : [Γ ||-ne A])
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRne (LogRelRec l) neA).

  Definition LRPi_@{i j k l} l {Γ A} (ΠA : PiRedTy@{k} Γ A)
    (ΠAad : PiRedTyAdequate (LR (LogRelRec@{i j k} l)) ΠA)
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRPi (LogRelRec l) ΠA ΠAad).

  Definition LRNat_@{i j k l} l {Γ A} (NA : [Γ ||-Nat A]) 
    : [LogRel@{i j k l} l | Γ ||- A] :=
    LRbuild (LRNat (LogRelRec l) NA).

  Definition LREmpty_@{i j k l} l {Γ A} (NA : [Γ ||-Empty A]) 
    : [LogRel@{i j k l} l | Γ ||- A] :=
    LRbuild (LREmpty (LogRelRec l) NA).

  Definition LRId_@{i j k l} l {Γ A} (IA : IdRedTyPack@{k} Γ A) 
    (IAad : IdRedTyAdequate (LR (LogRelRec@{i j k} l)) IA)
    : [LogRel@{i j k l} l | Γ ||- A] :=
    LRbuild (LRId (LogRelRec l) IA IAad).

End MoreDefs.
  
(** To be explicit with universe levels use the rhs, e.g
   [ LogRel@{i j k l} l | Γ ||- A] or [ LogRel0@{i j k} ||- Γ ||- A ≅ B | RA ]
 *)
Notation "[ Γ ||-< l > A ]" := [ LogRel l | Γ ||- A ].
Notation "[ Γ ||-< l > A ≅ B | RA ]" := [ LogRel l | Γ ||- A ≅ B | RA ].
Notation "[ Γ ||-< l > t : A | RA ]" := [ LogRel l | Γ ||- t : A | RA ].
Notation "[ Γ ||-< l > t ≅ u : A | RA ]" := [ LogRel l | Γ ||- t ≅ u : A | RA ].

Lemma instKripke `{GenericTypingProperties} {Γ A l} (wfΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]) : [Γ ||-<l> A].
Proof.
  specialize (h Γ wk_id wfΓ); now rewrite wk_id_ren_on in h.
Qed.

(** ** Rebundling reducibility of Polynomial *)

(** The definition of reducibility of product types in the logical relation, which separates
the "adequacy" part is not nice to work with. Here we relate it to the more natural one,
which lets us later on define an induction principle that does not show the separation at all. *)

Module PolyRed.

Section PolyRed.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}
    {Γ : context} {l : TypeLevel} {shp pos : term}.

  Record PolyRed@{i j k l} : Type@{l} :=
    {
      shpTy : [Γ |- shp] ;
      posTy : [Γ,, shp |- pos] ;
      shpRed {Δ} (ρ : Δ ≤ Γ) : [ |- Δ ] -> [ LogRel@{i j k l} l | Δ ||- shp⟨ρ⟩ ] ;
      posRed {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
          [ (shpRed ρ h) |  Δ ||- a : shp⟨ρ⟩] ->
          [ LogRel@{i j k l} l | Δ ||- pos[a .: (ρ >> tRel)]] ;
      posExt
        {Δ a b}
        (ρ : Δ ≤ Γ)
        (h :  [ |- Δ ])
        (ha : [ (shpRed ρ h) | Δ ||- a : shp⟨ρ⟩ ]) :
        [ (shpRed ρ h) | Δ ||- b : shp⟨ρ⟩] ->
        [ (shpRed ρ h) | Δ ||- a ≅ b : shp⟨ρ⟩] ->
        [ (posRed ρ h ha) | Δ ||- (pos[a .: (ρ >> tRel)]) ≅ (pos[b .: (ρ >> tRel)]) ]
    }.
  
  Definition from@{i j k l} {PA : PolyRedPack@{k} Γ shp pos} 
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : PolyRed@{i j k l}.
  Proof.
    unshelve econstructor; intros.
    - econstructor; now unshelve eapply PolyRedPack.shpAd.
    - econstructor; unshelve eapply PolyRedPack.posAd; cycle 1; tea.
    - now eapply PolyRedPack.shpTy.
    - now eapply PolyRedPack.posTy.
    - now eapply PolyRedPack.posExt.
  Defined.
  
  Definition toPack@{i j k l} (PA : PolyRed@{i j k l}) : PolyRedPack@{k} Γ shp pos.
  Proof.
    unshelve econstructor.
    - now eapply shpRed.
    - intros; now eapply posRed.
    - now eapply shpTy. 
    - now eapply posTy.
    - intros; now eapply posExt.
  Defined. 

  Definition toAd@{i j k l} (PA : PolyRed@{i j k l}) : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) (toPack PA).
  Proof.
    unshelve econstructor; intros.
    - eapply LRAd.adequate; eapply posRed.
    - eapply LRAd.adequate; eapply shpRed.
  Defined.

  Lemma eta@{i j k l} (PA : PolyRed@{i j k l}) : from (toAd PA) = PA.
  Proof. destruct PA; reflexivity. Qed.

  Lemma beta_pack@{i j k l} {PA : PolyRedPack@{k} Γ shp pos} 
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toPack (from PAad) = PA.
  Proof. destruct PA, PAad; reflexivity. Qed.

  Lemma beta_ad@{i j k l} {PA : PolyRedPack@{k} Γ shp pos} 
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toAd (from PAad) = PAad.
  Proof. destruct PA, PAad; reflexivity. Qed.

End PolyRed.

Arguments PolyRed : clear implicits.
Arguments PolyRed {_ _ _ _ _ _ _ _ _} _ _ _.

End PolyRed.

Export PolyRed(PolyRed,Build_PolyRed).
Coercion PolyRed.toPack : PolyRed >-> PolyRedPack.

Module ParamRedTy.
Section ParamRedTy.
  Context {T : term -> term -> term} `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}
    {Γ : context} {l : TypeLevel} {A : term}.

  Record ParamRedTy@{i j k l} : Type@{l} :=
    {
      dom : term ;
      cod : term ;
      red : [Γ |- A :⤳*: T dom cod] ;
      eqdom : [Γ |- dom ≅ dom];
      outTy := T dom cod ;
      eq : [Γ |- T dom cod ≅ T dom cod] ;
      polyRed :> PolyRed@{i j k l} Γ l dom cod
    }.

  Definition from@{i j k l} {PA : ParamRedTyPack@{k} (T:=T) Γ A}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA) :
    ParamRedTy@{i j k l}.
  Proof.
    exists (ParamRedTyPack.dom PA) (ParamRedTyPack.cod PA).
    - eapply ParamRedTyPack.red.
    - eapply ParamRedTyPack.eqdom.
    - eapply ParamRedTyPack.eq.
    - now eapply PolyRed.from.
  Defined.

  Definition toPack@{i j k l} (PA : ParamRedTy@{i j k l}) :
    ParamRedTyPack@{k} (T:=T) Γ A. 
  Proof.
    exists (dom PA) (cod PA).
    - now eapply red.
    - apply eqdom.
    - now eapply eq.
    - exact (PolyRed.toPack PA).
  Defined.

  Definition toAd@{i j k l} (PA : ParamRedTy@{i j k l}) :  
    PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) (toPack PA) :=
    PolyRed.toAd PA.

  Lemma eta@{i j k l} (PA : ParamRedTy@{i j k l}) : from (toAd PA) = PA.
  Proof. destruct PA; reflexivity. Qed.

  Lemma beta_pack@{i j k l} {PA : ParamRedTyPack@{k} (T:=T) Γ A}
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toPack (from PAad) = PA.
  Proof. destruct PA, PAad; reflexivity. Qed.

  Lemma beta_ad@{i j k l} {PA : ParamRedTyPack@{k} (T:=T) Γ A} 
    (PAad : PolyRedPackAdequate@{k l} (LogRel@{i j k l} l) PA)
    : toAd (from PAad) = PAad.
  Proof. destruct PA, PAad; reflexivity. Qed.
End ParamRedTy.

Arguments ParamRedTy : clear implicits.
Arguments ParamRedTy _ {_ _ _ _ _ _ _ _ _}.

End ParamRedTy.

(** ** Rebundling reducibility of product and sigma types *)

Export ParamRedTy(ParamRedTy, Build_ParamRedTy, outTy).
Module PiRedTyPack := ParamRedTy.
Coercion ParamRedTy.polyRed : ParamRedTy >-> PolyRed.
Coercion ParamRedTy.toPack : ParamRedTy >-> ParamRedTyPack.
Notation "[ Γ ||-Π< l > A ]" := (ParamRedTy tProd Γ l A) (at level 0, Γ, l, A at level 50).
Notation "[ Γ ||-Σ< l > A ]" := (ParamRedTy tSig Γ l A) (at level 0, Γ, l, A at level 50).

Section EvenMoreDefs.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.
  
  Definition LRPi'@{i j k l} {l Γ A} (ΠA : ParamRedTy@{i j k l} tProd Γ l A)
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRPi (LogRelRec l) _ (ParamRedTy.toAd ΠA)).

  Definition LRSig' @{i j k l} {l Γ A} (ΠA : ParamRedTy@{i j k l} tSig Γ l A)
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRSig (LogRelRec l) _ (ParamRedTy.toAd ΠA)).

End EvenMoreDefs.


(** ** Folding and unfolding lemmas of the logical relation wrt levels *)

Section LogRelRecFoldLemmas.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Lemma RedTyRecFwd {l Γ A t} (h : [Γ ||-U<l> A]) : 
    [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t] ->
    [LogRel (URedTy.level h) | Γ ||- t ].
  Proof.
    destruct h as [? lt]; cbn. 
    pattern level, l , lt; induction lt.
    cbn. easy. 
  Defined.

  Lemma RedTyRecBwd {l Γ A t} (h : [Γ ||-U<l> A]) : 
    [LogRel (URedTy.level h) | Γ ||- t ] ->
    [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t].
  Proof.
    destruct h as [? lt]; cbn.
    pattern level, l , lt; induction lt.
    cbn. easy. 
  Defined.

  (* This is a duplicate of the above, no ? *)
  Lemma LogRelRec_unfold {Γ l A t eqTy redTm eqTm} (h: [Γ ||-U<l> A]) :
    LogRelRec l (URedTy.level h) (URedTy.lt h) Γ t eqTy redTm eqTm <~>
    LogRel (URedTy.level h) Γ t eqTy redTm eqTm.
  Proof.
    destruct l; [destruct (elim (URedTy.lt h))|].
    destruct h; inversion lt; subst; cbn; now split.
  Qed.


  Lemma TyEqRecFwd {l Γ A t u} (h : [Γ ||-U<l> A]) 
    (lr : [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t]) :
    [lr | Γ ||- t ≅ u] <~> [RedTyRecFwd h lr | Γ ||- t ≅ u].
  Proof.
    unfold RedTyRecFwd.
    destruct h as [? lt]; cbn in *.
    induction lt; cbn; split; easy.
  Qed.

  Lemma TyEqRecBwd {l Γ A t u} (h : [Γ ||-U<l> A]) 
    (lr : [LogRel (URedTy.level h) | Γ ||- t ]) :
    [lr | Γ ||- t ≅ u] <~> [RedTyRecBwd h lr | Γ ||- t ≅ u].
  Proof.
    unfold RedTyRecBwd.
    destruct h as [? lt]; cbn in *.
    induction lt; cbn; split; easy.
  Qed.

End LogRelRecFoldLemmas.


(** ** Properties of reducibility at Nat and Empty *)

Section NatPropProperties.
  Context `{GenericTypingProperties}.
  Lemma NatProp_whnf {Γ A t} {NA : [Γ ||-Nat A]} : NatProp NA t -> whnf t.
  Proof.  intros [ | | ? []]; now (econstructor; eapply convneu_whne). Qed.

  Lemma NatPropEq_whnf {Γ A t u} {NA : [Γ ||-Nat A]} : NatPropEq NA t u -> whnf t × whnf u.
  Proof.  intros [ | | ? ? []]; split; econstructor; eapply convneu_whne; first [eassumption|symmetry; eassumption]. Qed.

End NatPropProperties.

Section EmptyPropProperties.
  Context `{GenericTypingProperties}.
  Lemma EmptyProp_whnf {Γ A t} {NA : [Γ ||-Empty A]} : @EmptyProp _ _ _ Γ t -> whnf t.
  Proof.  intros [ ? []]; now (econstructor; eapply convneu_whne). Qed.

  Lemma EmptyPropEq_whnf {Γ A t u} {NA : [Γ ||-Empty A]} : @EmptyPropEq _ _ Γ t u -> whnf t × whnf u.
  Proof.  intros [ ? ? []]; split; econstructor; eapply convneu_whne; first [eassumption|symmetry; eassumption]. Qed.

End EmptyPropProperties.

(* A&Y: We prove the hand-crafted induction principles here: *)

Lemma EmptyRedInduction :
  forall {ta : tag} {H : WfType ta} {H0 : RedType ta} {H1 : Typing ta}
    {H2 : ConvNeuConv ta} {H3 : ConvTerm ta} {H4 : RedTerm ta} 
    (Γ : context) (A : term) (NA : [Γ ||-Empty A])
    (P : forall t : term, [Γ ||-Empty t : A | NA] -> Type)
    (P0 : forall t : term, EmptyProp Γ t -> Type),
    (forall (t nf : term) (red : [Γ |-[ ta ] t :⤳*: nf : tEmpty])
       (eq : [Γ |-[ ta ] nf ≅ nf : tEmpty]) (prop : EmptyProp Γ nf),
        P0 nf prop -> P t (Build_EmptyRedTm nf red eq prop)) ->
    (forall (ne : term) (r : [Γ ||-NeNf ne : tEmpty]), P0 ne (EmptyRedTm.neR r)) ->
    (forall (t : term) (n : [Γ ||-Empty t : A | NA]), P t n)
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
    (Γ : context) (A : term) (NA : [Γ ||-Empty A])
    (P : forall t t0 : term, [Γ ||-Empty t ≅ t0 : A | NA] -> Type)
    (P0 : forall t t0 : term, EmptyPropEq Γ t t0 -> Type),
    (forall (t u nfL nfR : term) (redL : [Γ |-[ ta ] t :⤳*: nfL : tEmpty])
       (redR : [Γ |-[ ta ] u :⤳*: nfR : tEmpty]) (eq : [Γ |-[ ta ] nfL ≅ nfR : tEmpty])
       (prop : EmptyPropEq Γ nfL nfR),
        P0 nfL nfR prop -> P t u (Build_EmptyRedTmEq nfL nfR redL redR eq prop)) ->
    (forall (ne ne' : term) (r : [Γ ||-NeNf ne ≅ ne' : tEmpty]),
        P0 ne ne' (EmptyRedTmEq.neReq r)) ->
    (forall (t t0 : term) (n : [Γ ||-Empty t ≅ t0 : A | NA]), P t t0 n)
      × (forall (t t0 : term) (n : EmptyPropEq Γ t t0), P0 t t0 n).
Proof.
  intros.
  split.
  - intros t t0 n. induction n.
    eapply X; eauto. destruct prop; eauto.
  - intros. induction n. eapply X0.
Qed.

Module IdRedTy.
Section IdRedTy.
  
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Record IdRedTy@{i j k l} {Γ : context} {l} {A : term} : Type := 
  {
    ty : term ;
    lhs : term ;
    rhs : term ;
    outTy := tId ty lhs rhs ;
    red : [Γ |- A :⤳*: outTy] ;
    eq : [Γ |- outTy ≅ outTy] ;
    tyRed : [ LogRel@{i j k l} l | Γ ||- ty ] ;
    lhsRed : [ tyRed | Γ ||- lhs : _ ] ;
    rhsRed : [ tyRed | Γ ||- rhs : _ ] ;
    lhsRedRefl : [ tyRed | Γ ||- lhs ≅ lhs : _ ] ;
    rhsRedRefl : [ tyRed | Γ ||- rhs ≅ rhs : _ ] ;
    tyPER : PER (fun t u => [tyRed | _ ||- t ≅ u : _]) ;
    tyKripke : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [ LogRel@{i j k l} l | Δ ||- ty⟨ρ⟩ ] ;
    tyKripkeEq : forall {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [|-Δ]) (wfΞ : [|-Ξ]) B,
      ρ' =1 ρ'' ∘w ρ -> [tyKripke ρ wfΔ | _ ||- _ ≅ B] -> [tyKripke ρ' wfΞ | _ ||- _ ≅ B⟨ρ''⟩];
    tyKripkeTm : forall {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [|-Δ]) (wfΞ : [|-Ξ]) t,
      ρ' =1 ρ'' ∘w ρ -> [tyKripke ρ wfΔ | _ ||- t : _] -> [tyKripke ρ' wfΞ | _ ||- t⟨ρ''⟩ : _];
    tyKripkeTmEq : forall {Δ Ξ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Γ) (ρ'' : Ξ ≤ Δ) (wfΔ : [|-Δ]) (wfΞ : [|-Ξ]) t u,
      ρ' =1 ρ'' ∘w ρ -> [tyKripke ρ wfΔ | _ ||- t ≅ u : _] -> [tyKripke ρ' wfΞ | _ ||- t⟨ρ''⟩ ≅ u⟨ρ''⟩ : _];
 }.


  Definition from@{i j k l} {Γ l A} {IA : IdRedTyPack@{k} Γ A} (IAad : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) IA) 
    : @IdRedTy@{i j k l} Γ l A.
  Proof.
    unshelve econstructor; try exact IA.(IdRedTyPack.red).
    - econstructor; apply IAad.
    - intros; econstructor; now unshelve eapply IAad.
    - exact IA.(IdRedTyPack.eq).
    - exact IA.(IdRedTyPack.lhsRed).
    - exact IA.(IdRedTyPack.rhsRed).
    - exact IA.(IdRedTyPack.lhsRedRefl).
    - exact IA.(IdRedTyPack.rhsRedRefl).
    - exact IA.(IdRedTyPack.tyPER).
    - intros; now eapply IA.(IdRedTyPack.tyKripkeEq).
    - intros; now eapply IA.(IdRedTyPack.tyKripkeTm).
    - intros; now eapply IA.(IdRedTyPack.tyKripkeTmEq).
  Defined.

  Definition toPack@{i j k l} {Γ l A} (IA : @IdRedTy@{i j k l} Γ l A) : IdRedTyPack@{k} Γ A.
  Proof. 
    unshelve econstructor; try exact IA.(IdRedTy.red).
    - apply IA.(tyRed).
    - intros; now apply IA.(tyKripke).
    - exact IA.(eq).
    - exact IA.(lhsRed).
    - exact IA.(rhsRed).
    - exact IA.(IdRedTy.lhsRedRefl).
    - exact IA.(IdRedTy.rhsRedRefl).
    - exact IA.(IdRedTy.tyPER).
    - intros; now eapply IA.(IdRedTy.tyKripkeEq).
    - intros; now eapply IA.(IdRedTy.tyKripkeTm).
    - intros; now eapply IA.(IdRedTy.tyKripkeTmEq).
  Defined.
  
  Definition to@{i j k l} {Γ l A} (IA : @IdRedTy@{i j k l} Γ l A) : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) (toPack IA).
  Proof. 
    econstructor; [apply IA.(tyRed)| intros; now apply IA.(tyKripke)]. 
  Defined.

  Lemma beta_pack@{i j k l} {Γ l A} {IA : IdRedTyPack@{k} Γ A} (IAad : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) IA) :
    toPack (from IAad) = IA.
  Proof. reflexivity. Qed.
  
  Lemma beta_ad@{i j k l} {Γ l A} {IA : IdRedTyPack@{k} Γ A} (IAad : IdRedTyAdequate@{k l} (LogRel@{i j k l} l) IA) :
    to (from IAad) = IAad.
  Proof. reflexivity. Qed.

  Lemma eta@{i j k l} {Γ l A} (IA : @IdRedTy@{i j k l} Γ l A) : from  (to IA) = IA. 
  Proof. reflexivity. Qed.

  Definition IdRedTyEq {Γ l A} (IA : @IdRedTy Γ l A) := IdRedTyEq (toPack IA).
  Definition IdRedTm {Γ l A} (IA : @IdRedTy Γ l A) := IdRedTm (toPack IA).
  Definition IdProp {Γ l A} (IA : @IdRedTy Γ l A) := IdProp (toPack IA).
  Definition IdRedTmEq {Γ l A} (IA : @IdRedTy Γ l A) := IdRedTmEq (toPack IA).
  Definition IdPropEq {Γ l A} (IA : @IdRedTy Γ l A) := IdPropEq (toPack IA).

  Definition LRId'@{i j k l} {l Γ A} (IA : @IdRedTy@{i j k l} Γ l A)
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRId (LogRelRec l) _ (to IA)).
End IdRedTy.

Arguments IdRedTy {_ _ _ _ _ _ _ _ _}.
End IdRedTy.

Export IdRedTy(IdRedTy, Build_IdRedTy,IdRedTyEq,IdRedTm,IdProp,IdRedTmEq,IdPropEq,LRId').

Ltac unfold_id_outTy := 
  change (IdRedTyPack.outTy (IdRedTy.toPack ?IA)) with (tId IA.(IdRedTy.ty) IA.(IdRedTy.lhs) IA.(IdRedTy.rhs)) in *.

Notation "[ Γ ||-Id< l > A ]" := (IdRedTy Γ l A) (at level 0, Γ, l,  A at level 50).
Notation "[ Γ ||-Id< l > A ≅ B | RA ]" := (IdRedTyEq (Γ:=Γ) (l:=l) (A:=A) RA B) (at level 0, Γ, l, A, B, RA at level 50).
Notation "[ Γ ||-Id< l > t : A | RA ]" := (IdRedTm (Γ:=Γ) (l:=l) (A:=A) RA t) (at level 0, Γ, l, t, A, RA at level 50).
Notation "[ Γ ||-Id< l > t ≅ u : A | RA ]" := (IdRedTmEq (Γ:=Γ) (l:=l) (A:=A) RA t u) (at level 0, Γ, l, t, u, A, RA at level 50).










