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

Inductive isLRFun@{i} `{ta : tag} `{WfContext ta}
  `{WfType ta} `{ConvType ta} `{RedType ta} `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta}
  {Γ : context}
  {dom cod : term} 
  {domRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ dom⟨ρ⟩}
  {codRedTm : forall {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), [ domRed ρ h | _ ||- a : _] -> term -> Type@{i}} 
  : term -> Type :=
| LamLRFun : forall A' t : term,
  (forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), 
      [domRed ρ h | Δ ||- dom⟨ρ⟩ ≅ A'⟨ρ⟩]) ->
  (forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
    (ha : [ domRed ρ h | Δ ||- a : dom⟨ρ⟩ ]), 
    codRedTm ρ h ha t[a .: (ρ >> tRel)]) ->
  isLRFun (tLambda A' t)
| NeLRFun : forall f : term, [Γ |- f ~ f : tProd dom cod] -> isLRFun f.


Module PiRedTm.
  Record FunRedTm@{i} `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta}`{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t dom cod : term} 
    {domRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ dom⟨ρ⟩}
    {codRedTm : forall {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), [ domRed ρ h | _ ||- a : _] -> term -> Type@{i}} 
    {codRedTmEq : forall {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), [ domRed ρ h | _ ||- a : _] -> term -> term -> Type@{i}}
  : Type := {
    nf : term;
    red : [ Γ |- t :⤳*: nf : tProd dom cod ];
    isfun : isLRFun (dom:=dom) (cod:=cod) (domRed:=@domRed) (codRedTm:=@codRedTm) nf;
    refl : [ Γ |- nf ≅ nf : tProd dom cod ];
    app {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ domRed ρ h | _ ||- a : _ ]) : codRedTm ρ h ha (tApp nf⟨ρ⟩ a) ;
    eq {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) 
      (ha : [ domRed ρ h | Δ ||- a : _ ])
      (hb : [ domRed ρ h | Δ ||- b : _ ])
      (eq : [ domRed ρ h | Δ ||- a ≅ b : _ ])
      : codRedTmEq ρ h ha (tApp nf⟨ρ⟩ a) (tApp nf⟨ρ⟩ b) ;
  }.

  Arguments FunRedTm {_ _ _ _ _ _ _ _ _}.


  Definition PiRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t A : term} {ΠA : PiRedTy Γ A}
  : Type := FunRedTm Γ t ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) 
    (fun Δ => ΠA.(PolyRedPack.shpRed ) (Δ := Δ))
    (fun Δ a ρ wfΔ ha t => [ΠA.(PolyRedPack.posRed) ρ wfΔ ha | _ ||- t : _])
    (fun Δ a ρ wfΔ ha t u => [ΠA.(PolyRedPack.posRed) ρ wfΔ ha | _ ||- t ≅ u : _]).


  Arguments PiRedTm {_ _ _ _ _ _ _ _ _}.

End PiRedTm.

Export PiRedTm(PiRedTm).

Definition Build_PiRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A : term} (ΠA : PiRedTy Γ A) (t : term)
    nf red isfun refl app eq : PiRedTm Γ t A ΠA :=
  PiRedTm.Build_FunRedTm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nf red isfun refl app eq.

Notation "[ Γ ||-Π t : A | ΠA ]" := (PiRedTm Γ t A ΠA).

Module PiRedTmEq.
  Record FunRedTmEq@{i} `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t u dom cod : term} 
    {domRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ dom⟨ρ⟩}
    {codRedTm : forall {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), [ domRed ρ h | _ ||- a : _] -> term -> Type@{i}} 
    {codRedTmEq : forall {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), [ domRed ρ h | _ ||- a : _] -> term -> term -> Type@{i}}
  : Type := 
  {
    redL : PiRedTm.FunRedTm@{i} Γ t dom cod (@domRed) (@codRedTm) (@codRedTmEq) ;
    redR : PiRedTm.FunRedTm@{i} Γ u dom cod (@domRed) (@codRedTm) (@codRedTmEq) ;
    eq : [ Γ |- redL.(PiRedTm.nf) ≅ redR.(PiRedTm.nf) : tProd dom cod ];
    eqApp {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [domRed ρ h | Δ ||- a : _ ] )
      : codRedTmEq ρ h ha (tApp redL.(PiRedTm.nf)⟨ρ⟩ a) (tApp redR.(PiRedTm.nf)⟨ρ⟩ a) ;
  }.

  Arguments FunRedTmEq {_ _ _ _ _ _ _ _ _}.
 
  Definition PiRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {t u A : term} {ΠA : PiRedTy Γ A}
  : Type := FunRedTmEq Γ t u ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) 
    (fun Δ => ΠA.(PolyRedPack.shpRed ) (Δ := Δ))
    (fun Δ a ρ wfΔ ha t => [ΠA.(PolyRedPack.posRed) ρ wfΔ ha | _ ||- t : _])
    (fun Δ a ρ wfΔ ha t u => [ΠA.(PolyRedPack.posRed) ρ wfΔ ha | _ ||- t ≅ u : _]).

  Arguments PiRedTmEq {_ _ _ _ _ _ _ _ _}.

End PiRedTmEq.

Export PiRedTmEq(PiRedTmEq).

Definition Build_PiRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A : term} (ΠA : PiRedTy Γ A) (t u : term)
    redL redR eq eqApp : PiRedTmEq Γ t u A ΠA :=
  PiRedTmEq.Build_FunRedTmEq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ redL redR eq eqApp.


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

Module SigRedTy := ParamRedTyPack.

Inductive isLRPair `{ta : tag} `{WfContext ta}
  `{WfType ta} `{ConvType ta} `{RedType ta} `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta}
  {Γ : context} {A : term} (ΣA : SigRedTy Γ A) : term -> Type :=
| PairLRpair : forall (A' B' a b : term)
  (rdom : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]),
      [ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- (SigRedTy.dom ΣA)⟨ρ⟩ ≅ A'⟨ρ⟩])
  (rcod : forall {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
    (ha : [ ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- a : ΣA.(PiRedTy.dom)⟨ρ⟩ ]),
      [ΣA.(PolyRedPack.posRed) ρ h ha | Δ ||- (SigRedTy.cod ΣA)[a .: (ρ >> tRel)] ≅ B'[a .: (ρ >> tRel)]])
  (rfst : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]),
      [ΣA.(PolyRedPack.shpRed) ρ h | Δ ||- a⟨ρ⟩ : (SigRedTy.dom ΣA)⟨ρ⟩])
  (rsnd : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]),
      [ΣA.(PolyRedPack.posRed) ρ h (rfst ρ h) | Δ ||- b⟨ρ⟩ : (SigRedTy.cod ΣA)[a⟨ρ⟩ .: (ρ >> tRel)] ]),

  isLRPair ΣA (tPair A' B' a b)

| NeLRPair : forall p : term, [Γ |- p ~ p : tSig (SigRedTy.dom ΣA) (SigRedTy.cod ΣA)] -> isLRPair ΣA p.

Module SigRedTm.

  Record SigRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A : term} {ΣA : SigRedTy Γ A} {t : term}
  : Type := {
    nf : term;
    red : [ Γ |- t :⤳*: nf : ΣA.(outTy) ];
    ispair : isLRPair ΣA nf;
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

Lemma wk1_subst_scons_eq {Γ Δ A B a} (ρ : Δ ≤ Γ) :  B⟨ρ⟩ = B⟨wk1 Γ A⟩[a .: ρ >> tRel].
Proof. rewrite wk1_ren_on; asimpl; now rewrite <- rinstInst'_term. Qed.

Module WRedHelpers.
Section WRedHelpers.
  Universe i.
  Context  `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    `{!WfContextProperties} `{!WfTypeProperties} 
    {Γ A B} 
    (wtyA : [Γ |- A])
    (wtyB : [Γ |- B])
    (RA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), LRPack Δ A⟨ρ⟩)
    (RB : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), LRPack Δ B⟨ρ⟩) 
    (RBeq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [RB Δ ρ wfΔ | _ ||- _ ≅ B⟨ρ⟩]) .


  Lemma shiftPolyRed  :
    PolyRedPack@{i} Γ A B⟨wk1 Γ A⟩.
  Proof.
    unshelve econstructor; tea.
    + intros; rewrite <- wk1_subst_scons_eq; now apply RB. 
    + eapply wft_wk; tea; gen_typing.
    + intros; cbn. rewrite <- wk1_subst_scons_eq. set (e := wk1_subst_scons_eq ρ).
      refine (match e as e in _ = y return [eq_rect B⟨ρ⟩ (fun t => LRPack Δ t) (RB Δ ρ h) y e | _ ||- _ ≅ B⟨ρ⟩] with | eq_refl _ => _ end).
      cbn; now apply RBeq.
  Qed.
      
  Context `{!RedTypeProperties} `{!ConvTypeProperties} (convA : [Γ |- A ≅ A]) (convB : [Γ |- B ≅ B]).
  
  Lemma arrRedTy0 : [Γ ||-Πd arr A B].
  Proof.
    unshelve econstructor; [exact A| exact B⟨wk1 Γ A⟩|..]; tea.
    + rewrite wk1_ren_on; eapply redtywf_refl.
      now eapply wft_simple_arr.
    + rewrite wk1_ren_on; eapply convty_simple_arr; tea.
    + now eapply shiftPolyRed.
  Qed.

  Definition arrRedTy : LRPack@{i} Γ (arr A B) := 
    Build_LRPack _ _ 
      (PiRedTyEq arrRedTy0)
      (fun t => PiRedTm _ t _ arrRedTy0)
      (fun t u => PiRedTmEq _ t u _ arrRedTy0).
End WRedHelpers.
End WRedHelpers.

(** ** Reducibility of W types *)

Module WRedTyPack.
Section WRedTyPack.
  Context  `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} {Γ : context} {A: term}.

  Record WRedTyPack@{i} :=
    {
      PRTPack :> ParamRedTyPack@{i} (T := tW) Γ A;
      (* Redundant but simplifying things *)
      (* domRed0 : LRPack@{i} Γ PRTPack.(ParamRedTyPack.dom) ; *)
      (* Required since we do not have yet that tRel 0 is reducible on a reducible type  *)
      (* codRed0 : LRPack@{i} (Γ ,, PRTPack.(ParamRedTyPack.dom)) PRTPack.(ParamRedTyPack.cod) ; *)
      codRed0 : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]),
        LRPack@{i} (Δ ,, PRTPack.(ParamRedTyPack.dom)⟨ρ⟩) PRTPack.(ParamRedTyPack.cod)⟨wk_up PRTPack.(ParamRedTyPack.dom) ρ⟩ ;
    }.

  (* Definition contTyRed (WA : WRedTyPack) {a}
    (Ra : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [WA.(PolyRedPack.shpRed) ρ wfΔ | _ ||- a⟨ρ⟩ : _])
    (dom := WA.(ParamRedTyPack.dom)) (cod := WA.(ParamRedTyPack.cod))
  : LRPack@{i} Γ (supContTy dom cod a).
  Proof.
    unfold supContTy. *)

(* Definition WRedTyPack `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} := 
  ParamRedTyPack (T:=tW). *)

Record WRedTyAdequate@{i j} (R : RedRel@{i j}) (WA : WRedTyPack@{i})
  : Type@{j} := 
  {
    PRTAd :> PolyRedPackAdequate R WA ;
    (* redAd0 : LRPackAdequate R WA.(redRed0) ; *)
    (* codAd0 : LRPackAdequate R WA.(codRed0) ; *)
    codAd0 : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), 
      LRPackAdequate R (WA.(codRed0) ρ wfΔ) ;
  }.
End WRedTyPack.
Arguments WRedTyPack {_ _ _ _ _}.
Arguments WRedTyAdequate {_ _ _ _ _ _ _}.
End WRedTyPack.

Export WRedTyPack(WRedTyPack, Build_WRedTyPack,WRedTyAdequate,Build_WRedTyAdequate).
Coercion WRedTyPack.PRTPack : WRedTyPack >-> ParamRedTyPack.
Coercion WRedTyPack.PRTAd : WRedTyAdequate >-> PolyRedPackAdequate.

Definition WRedTyEq `{ta : tag} 
  `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
  {Γ : context} {A : term} (WA : WRedTyPack Γ A) (B : term) :=
  ParamRedTyEq (T:=tW) Γ A B WA.

(* Notation "[ Γ ||-W A ≅ B | ΠA ]" := (WRedTyEq (Γ:=Γ) (A:=A) ΠA B). *)

Set Printing Universes.
Module WRedTm.
Section WRedTm.  
  Universe i.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context} {A: term} {WA : WRedTyPack@{i} Γ A}
    (dom:=WA.(ParamRedTyPack.dom)) (cod:=WA.(ParamRedTyPack.cod))
    (T:= tW dom cod).

  Lemma instWCodRed {Δ} {a} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ])
    (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _]) :
      forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|-Ξ]), LRPack@{i} Ξ cod⟨wk_up dom ρ⟩[a..]⟨ρ'⟩.
  Proof.
    intros.
    rewrite subst_ren_subst_mixed, <-wk_up_ren_subst. 
    unshelve eapply WA.(PolyRedPack.posRed); tea.
    now eapply Ra.
  Qed.

  Definition funRedTm Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) {a} k
    (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _]) 
    (WRedTm : forall  Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), term -> Type@{i}) 
    (WRedTmEq : forall  Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), term -> term -> Type@{i}) 
    : Type@{i} :=
      let coda := cod⟨wk_up dom ρ⟩[a..] in
    PiRedTm.FunRedTm Δ k coda T⟨wk_step coda ρ⟩ (instWCodRed ρ wfΔ Ra)
      (fun Ξ _ ρ' wfΞ _ t => WRedTm Ξ (ρ' ∘w ρ) wfΞ t)
      (fun Ξ _ ρ' wfΞ _ t u => WRedTmEq Ξ (ρ' ∘w ρ) wfΞ t u).

  Definition funRedTmEq Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) {a} k k'
    (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _]) 
    (WRedTm : forall  Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), term -> Type@{i}) 
    (WRedTmEq : forall  Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), term -> term -> Type@{i}) 
    : Type@{i} :=
    let coda := cod⟨wk_up dom ρ⟩[a..] in
    PiRedTmEq.FunRedTmEq Δ k k' coda T⟨wk_step coda ρ⟩ (instWCodRed ρ wfΔ Ra)
      (fun Ξ _ ρ' wfΞ _ t => WRedTm Ξ (ρ' ∘w ρ) wfΞ t)
      (fun Ξ _ ρ' wfΞ _ t u => WRedTmEq Ξ (ρ' ∘w ρ) wfΞ t u).


  (* Reducibility of terms at W types and reducible conversion of terms at W types.
    The two notions have to be defined mutually in order to state that the continuation k
    in the sup a k case is reducible, in particular extensional with respect to reducible
    conversion. For the same reason, we have to freely insert a Kripke style quantification
    on contexts and renamings (more precisely, in order to state that k⟨ρ⟩ b is reducible for
    any reducible term b in a "future" context Δ ≤ Γ)
  *)


  Inductive WRedTm  Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : term -> Type :=
    | mkWRedTm
     t nf
      (red : [Δ |- t :⤳*: nf : T⟨ρ⟩ ])
      (eq : [Δ |- nf ≅ nf : T⟨ρ⟩ ])
      (prop : WProp Δ ρ wfΔ nf)
      :
      WRedTm Δ ρ wfΔ t
  with WProp Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : term -> Type :=
    | supR {A B a k}
      (wtyA : [Δ |- A])
      (RAeq : [WA.(PolyRedPack.shpRed) ρ wfΔ | _ ||- _ ≅ A]) 
      (* dom⟨ρ⟩ instead of A in the context ? *)
      (wtyB : [Δ ,, A |- B ])
      (RBeq : [WA.(WRedTyPack.codRed0) ρ wfΔ | _ ||- _ ≅ B])
      (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _]) 
      (Rk : funRedTm Δ ρ wfΔ k Ra WRedTm WRedTmEq) :
      WProp Δ ρ wfΔ (tSup A B a k)
    | neR {k} : [Δ ||-NeNf k : T⟨ρ⟩] -> WProp Δ ρ wfΔ k
  with WRedTmEq Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : term -> term -> Type :=
    | mkWRedTmEq t u nfL nfR 
      (redL : [Δ |- t :⤳*: nfL : T⟨ρ⟩])
      (redR : [Δ |- u :⤳*: nfR : T⟨ρ⟩])
      (eq : [Δ |- nfL ≅ nfR : T⟨ρ⟩])
      (prop : WPropEq Δ ρ wfΔ nfL nfR)
      : WRedTmEq Δ ρ wfΔ t u
  with WPropEq Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : term -> term -> Type :=
    | supReq {A A' B B' a a' k k'}
      (wtyA : [Δ |- A])
      (wtyA' : [Δ |- A'])
      (RAeq : [WA.(PolyRedPack.shpRed) ρ wfΔ | _ ||- _ ≅ A]) 
      (RAeq' : [WA.(PolyRedPack.shpRed) ρ wfΔ | _ ||- _ ≅ A']) 
      (wtyB : [Δ ,, A |- B ])
      (wtyB' : [Δ ,, A' |- B' ])
      (RBeq : [WA.(WRedTyPack.codRed0) ρ wfΔ | _ ||- _ ≅ B])
      (RBeq' : [WA.(WRedTyPack.codRed0) ρ wfΔ | _ ||- _ ≅ B'])
      (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _]) 
      (Ra' : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a'⟨ρ'⟩ : _]) 
      (Raa' : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _]) 
      (Rk : funRedTm Δ ρ wfΔ k Ra WRedTm WRedTmEq)
      (Rk' : funRedTm Δ ρ wfΔ k' Ra' WRedTm WRedTmEq)
      (Rkk' : funRedTmEq Δ ρ wfΔ k k' Ra WRedTm WRedTmEq) :
      WPropEq Δ ρ wfΔ (tSup A B a k) (tSup A' B' a' k')
    | neReq {k k'} : [Δ ||-NeNf k ≅ k' : T⟨ρ⟩] -> WPropEq Δ ρ wfΔ k k'
    .

    (* The nested induction on funRedTm causes issues to Scheme and co *)
    Section Induction.
      Universe o.
      Context
        (Prt : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t, WRedTm Δ ρ wfΔ t -> Type@{o})
        (Pp : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t, WProp Δ ρ wfΔ t -> Type@{o})
        (Prte : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t u, WRedTmEq Δ ρ wfΔ t u -> Type@{o})
        (Ppe : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t u, WPropEq Δ ρ wfΔ t u -> Type@{o})
        (ihMkrt : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t nf : term) (red : [Δ |-[ ta ] t :⤳*: nf : T⟨ρ⟩])
              (eq : [Δ |-[ ta ] nf ≅ nf : T⟨ρ⟩]) (prop : WProp Δ ρ wfΔ nf),
            Pp Δ ρ wfΔ nf prop -> Prt Δ ρ wfΔ t (mkWRedTm Δ ρ wfΔ t nf red eq prop))
        (ihsupR : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (A B a k : term) (wtyA : [Δ |-[ ta ] A])
                (RAeq : [PolyRedPack.shpRed WA ρ wfΔ | _ ||- _ ≅ A]) (wtyB : [Δ,, A |-[ ta ] B])
                (RBeq : [WRedTyPack.codRed0 WA ρ wfΔ | _ ||- _ ≅ B])
                (Ra : forall (Ξ : context) (ρ' : Ξ ≤ Δ) (wfΞ : [ |-[ ta ] Ξ]), [PolyRedPack.shpRed WA (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _])
                (Rk : funRedTm Δ ρ wfΔ k Ra WRedTm WRedTmEq),
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b} Rb, Prt Ξ (ρ' ∘w ρ) wfΞ _ (PiRedTm.app Rk (a:=b) ρ' wfΞ Rb)) ->
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b b'} Rb Rb' Rbb', Prte Ξ (ρ' ∘w ρ) wfΞ _ _ (PiRedTm.eq Rk (a:=b) (b:=b') ρ' wfΞ Rb Rb' Rbb')) ->
              Pp Δ ρ wfΔ (tSup A B a k) (supR Δ ρ wfΔ wtyA RAeq wtyB RBeq Ra Rk))
        (ihneR : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (k : term) (r : [Δ ||-NeNf k : T⟨ρ⟩]),
              Pp Δ ρ wfΔ k (neR Δ ρ wfΔ r))
        (ihMkrte : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t u nfL nfR : term)
                (redL : [Δ |-[ ta ] t :⤳*: nfL : T⟨ρ⟩]) (redR : [Δ |-[ ta ] u :⤳*: nfR : T⟨ρ⟩])
                (eq : [Δ |-[ ta ] nfL ≅ nfR : T⟨ρ⟩]) (prop : WPropEq Δ ρ wfΔ nfL nfR),
              Ppe Δ ρ wfΔ nfL nfR prop -> Prte Δ ρ wfΔ t u (mkWRedTmEq Δ ρ wfΔ t u nfL nfR redL redR eq prop))
        (ihsupReq : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (A A' B B' a a' k k' : term) 
                (wtyA : [Δ |-[ ta ] A]) (wtyA' : [Δ |-[ ta ] A']) (RAeq : [PolyRedPack.shpRed WA ρ wfΔ | _ ||- _ ≅ A])
                (RAeq' : [PolyRedPack.shpRed WA ρ wfΔ | _ ||- _ ≅ A']) (wtyB : [Δ,, A |-[ ta ] B])
                (wtyB' : [Δ,, A' |-[ ta ] B']) (RBeq : [WRedTyPack.codRed0 WA ρ wfΔ | _ ||- _ ≅ B])
                (RBeq' : [WRedTyPack.codRed0 WA ρ wfΔ | _ ||- _ ≅ B'])
                (Ra : forall (Ξ : context) (ρ' : Ξ ≤ Δ) (wfΞ : [ |-[ ta ] Ξ]),
                      [PolyRedPack.shpRed WA (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _])
                (Ra' : forall (Ξ : context) (ρ' : Ξ ≤ Δ) (wfΞ : [ |-[ ta ] Ξ]),
                      [PolyRedPack.shpRed WA (ρ' ∘w ρ) wfΞ | _ ||- a'⟨ρ'⟩ : _])
                (Raa' : forall (Ξ : context) (ρ' : Ξ ≤ Δ) (wfΞ : [ |-[ ta ] Ξ]),
                        [PolyRedPack.shpRed WA (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _])
                (Rk : funRedTm Δ ρ wfΔ k Ra WRedTm WRedTmEq)
                (Rk' : funRedTm Δ ρ wfΔ k' Ra' WRedTm WRedTmEq)
                (Rkk' : funRedTmEq Δ ρ wfΔ k k' Ra WRedTm WRedTmEq),
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b} Rb, Prt Ξ (ρ' ∘w ρ) wfΞ _ (PiRedTm.app Rk (a:=b) ρ' wfΞ Rb)) ->
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b b'} Rb Rb' Rbb', Prte Ξ (ρ' ∘w ρ) wfΞ _ _ (PiRedTm.eq Rk (a:=b) (b:=b') ρ' wfΞ Rb Rb' Rbb')) ->
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b} Rb, Prt Ξ (ρ' ∘w ρ) wfΞ _ (PiRedTm.app Rk' (a:=b) ρ' wfΞ Rb)) ->
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b b'} Rb Rb' Rbb', Prte Ξ (ρ' ∘w ρ) wfΞ _ _ (PiRedTm.eq Rk' (a:=b) (b:=b') ρ' wfΞ Rb Rb' Rbb')) ->
            (forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) {b} Rb, Prte Ξ (ρ' ∘w ρ) wfΞ _ _ (PiRedTmEq.eqApp Rkk' (a:=b) ρ' wfΞ Rb)) ->
              Ppe Δ ρ wfΔ (tSup A B a k) (tSup A' B' a' k')
                (supReq Δ ρ wfΔ wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk'))
        (ihneReq : forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (k k' : term) (r : [Δ ||-NeNf k ≅ k' : T⟨ρ⟩]),
              Ppe Δ ρ wfΔ k k' (neReq Δ ρ wfΔ r)).

      Set Transparent Obligations.
      #[program]
      Definition WRedTm_mut_rect :=
        fix F (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WRedTm Δ ρ wfΔ t) {struct w} : Prt Δ ρ wfΔ t w :=
          match w as w0 in (WRedTm _ _ _ t0) return (Prt Δ ρ wfΔ t0 w0) with
          | mkWRedTm _ _ _ t0 nf red eq prop => ihMkrt Δ ρ wfΔ t0 nf red eq prop (F0 Δ ρ wfΔ nf prop)
          end
        with F0 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WProp Δ ρ wfΔ t) {struct w} :
            Pp Δ ρ wfΔ t w :=
          match w as w0 in (WProp _ _ _ t0) return (Pp Δ ρ wfΔ t0 w0) with
          | @supR _ _ _ A B a k wtyA RAeq wtyB RBeq Ra Rk => ihsupR Δ ρ wfΔ A B a k wtyA RAeq wtyB RBeq Ra Rk _ _
          | @neR _ _ _ k r => ihneR Δ ρ wfΔ k r
          end
        with F1 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WRedTmEq Δ ρ wfΔ t t0) {struct w} :
            Prte Δ ρ wfΔ t t0 w :=
          match w as w0 in (WRedTmEq _ _ _ t1 t2) return (Prte Δ ρ wfΔ t1 t2 w0) with
          | mkWRedTmEq _ _ _ t1 u nfL nfR redL redR eq prop =>
              ihMkrte Δ ρ wfΔ t1 u nfL nfR redL redR eq prop (F2 Δ ρ wfΔ nfL nfR prop)
          end
        with F2 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WPropEq Δ ρ wfΔ t t0) {struct w} :
            Ppe Δ ρ wfΔ t t0 w :=
          match w as w0 in (WPropEq _ _ _ t1 t2) return (Ppe Δ ρ wfΔ t1 t2 w0) with
          | @supReq _ _ _ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' =>
              ihsupReq Δ ρ wfΔ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' _ _ _ _ _
          | @neReq _ _ _ k k' r => ihneReq Δ ρ wfΔ k k' r
          end
        for
        F.

      #[program]
      Definition WProp_mut_rect :=
        fix F (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WRedTm Δ ρ wfΔ t) {struct w} : Prt Δ ρ wfΔ t w :=
          match w as w0 in (WRedTm _ _ _ t0) return (Prt Δ ρ wfΔ t0 w0) with
          | mkWRedTm _ _ _ t0 nf red eq prop => ihMkrt Δ ρ wfΔ t0 nf red eq prop (F0 Δ ρ wfΔ nf prop)
          end
        with F0 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WProp Δ ρ wfΔ t) {struct w} :
            Pp Δ ρ wfΔ t w :=
          match w as w0 in (WProp _ _ _ t0) return (Pp Δ ρ wfΔ t0 w0) with
          | @supR _ _ _ A B a k wtyA RAeq wtyB RBeq Ra Rk => ihsupR Δ ρ wfΔ A B a k wtyA RAeq wtyB RBeq Ra Rk _ _
          | @neR _ _ _ k r => ihneR Δ ρ wfΔ k r
          end
        with F1 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WRedTmEq Δ ρ wfΔ t t0) {struct w} :
            Prte Δ ρ wfΔ t t0 w :=
          match w as w0 in (WRedTmEq _ _ _ t1 t2) return (Prte Δ ρ wfΔ t1 t2 w0) with
          | mkWRedTmEq _ _ _ t1 u nfL nfR redL redR eq prop =>
              ihMkrte Δ ρ wfΔ t1 u nfL nfR redL redR eq prop (F2 Δ ρ wfΔ nfL nfR prop)
          end
        with F2 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WPropEq Δ ρ wfΔ t t0) {struct w} :
            Ppe Δ ρ wfΔ t t0 w :=
          match w as w0 in (WPropEq _ _ _ t1 t2) return (Ppe Δ ρ wfΔ t1 t2 w0) with
          | @supReq _ _ _ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' =>
              ihsupReq Δ ρ wfΔ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' _ _ _ _ _
          | @neReq _ _ _ k k' r => ihneReq Δ ρ wfΔ k k' r
          end
        for
        F0.

      #[program]
      Definition WRedTmEq_mut_rect :=
        fix F (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WRedTm Δ ρ wfΔ t) {struct w} : Prt Δ ρ wfΔ t w :=
          match w as w0 in (WRedTm _ _ _ t0) return (Prt Δ ρ wfΔ t0 w0) with
          | mkWRedTm _ _ _ t0 nf red eq prop => ihMkrt Δ ρ wfΔ t0 nf red eq prop (F0 Δ ρ wfΔ nf prop)
          end
        with F0 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WProp Δ ρ wfΔ t) {struct w} :
            Pp Δ ρ wfΔ t w :=
          match w as w0 in (WProp _ _ _ t0) return (Pp Δ ρ wfΔ t0 w0) with
          | @supR _ _ _ A B a k wtyA RAeq wtyB RBeq Ra Rk => ihsupR Δ ρ wfΔ A B a k wtyA RAeq wtyB RBeq Ra Rk _ _
          | @neR _ _ _ k r => ihneR Δ ρ wfΔ k r
          end
        with F1 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WRedTmEq Δ ρ wfΔ t t0) {struct w} :
            Prte Δ ρ wfΔ t t0 w :=
          match w as w0 in (WRedTmEq _ _ _ t1 t2) return (Prte Δ ρ wfΔ t1 t2 w0) with
          | mkWRedTmEq _ _ _ t1 u nfL nfR redL redR eq prop =>
              ihMkrte Δ ρ wfΔ t1 u nfL nfR redL redR eq prop (F2 Δ ρ wfΔ nfL nfR prop)
          end
        with F2 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WPropEq Δ ρ wfΔ t t0) {struct w} :
            Ppe Δ ρ wfΔ t t0 w :=
          match w as w0 in (WPropEq _ _ _ t1 t2) return (Ppe Δ ρ wfΔ t1 t2 w0) with
          | @supReq _ _ _ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' =>
              ihsupReq Δ ρ wfΔ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' _ _ _ _ _
          | @neReq _ _ _ k k' r => ihneReq Δ ρ wfΔ k k' r
          end
        for
        F1.

      #[program]
      Definition WPropEq_mut_rect :=
        fix F (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WRedTm Δ ρ wfΔ t) {struct w} : Prt Δ ρ wfΔ t w :=
          match w as w0 in (WRedTm _ _ _ t0) return (Prt Δ ρ wfΔ t0 w0) with
          | mkWRedTm _ _ _ t0 nf red eq prop => ihMkrt Δ ρ wfΔ t0 nf red eq prop (F0 Δ ρ wfΔ nf prop)
          end
        with F0 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t : term) (w : WProp Δ ρ wfΔ t) {struct w} :
            Pp Δ ρ wfΔ t w :=
          match w as w0 in (WProp _ _ _ t0) return (Pp Δ ρ wfΔ t0 w0) with
          | @supR _ _ _ A B a k wtyA RAeq wtyB RBeq Ra Rk => ihsupR Δ ρ wfΔ A B a k wtyA RAeq wtyB RBeq Ra Rk _ _
          | @neR _ _ _ k r => ihneR Δ ρ wfΔ k r
          end
        with F1 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WRedTmEq Δ ρ wfΔ t t0) {struct w} :
            Prte Δ ρ wfΔ t t0 w :=
          match w as w0 in (WRedTmEq _ _ _ t1 t2) return (Prte Δ ρ wfΔ t1 t2 w0) with
          | mkWRedTmEq _ _ _ t1 u nfL nfR redL redR eq prop =>
              ihMkrte Δ ρ wfΔ t1 u nfL nfR redL redR eq prop (F2 Δ ρ wfΔ nfL nfR prop)
          end
        with F2 (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (t t0 : term) (w : WPropEq Δ ρ wfΔ t t0) {struct w} :
            Ppe Δ ρ wfΔ t t0 w :=
          match w as w0 in (WPropEq _ _ _ t1 t2) return (Ppe Δ ρ wfΔ t1 t2 w0) with
          | @supReq _ _ _ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' =>
              ihsupReq Δ ρ wfΔ A A' B B' a a' k k' wtyA wtyA' RAeq RAeq' wtyB wtyB' RBeq RBeq' Ra Ra' Raa' Rk Rk' Rkk' _ _ _ _ _
          | @neReq _ _ _ k k' r => ihneReq Δ ρ wfΔ k k' r
          end
        for
        F2.

      Definition WRedInductionConcl :=
        (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t (w : WRedTm _ ρ wfΔ t), Prt Δ ρ wfΔ t w)
        × (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t (w : WProp _ ρ wfΔ t), Pp Δ ρ wfΔ t w)
        × (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t t0 (w : WRedTmEq _ ρ wfΔ t t0), Prte Δ ρ wfΔ t t0 w)
        × (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) t t0 (w : WPropEq _ ρ wfΔ t t0), Ppe Δ ρ wfΔ t t0 w).

      Definition WRedInduction : WRedInductionConcl := (WRedTm_mut_rect, WProp_mut_rect, WRedTmEq_mut_rect, WPropEq_mut_rect).
    End Induction.
  End WRedTm.

  Arguments WRedTm {_ _ _ _ _ _ _ _ _ _ _} _ {_}.
  Arguments WProp {_ _ _ _ _ _ _ _ _ _ _} _ {_}.
  Arguments WRedTmEq {_ _ _ _ _ _ _ _ _ _ _} _ {_}.
  Arguments WPropEq {_ _ _ _ _ _ _ _ _ _ _} _ {_}.
  Arguments WRedInductionConcl {_ _ _ _ _ _ _ _ _ _ _}.

  Section WRedTmHelpers.
    Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
      `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
      `{RedTerm ta} {Γ : context} {A: term} {WA : WRedTyPack Γ A}
       (wfΓ : [|-Γ]).

    Definition WRedTm' := WRedTm WA wk_id wfΓ.
    Definition WProp' := WProp WA wk_id wfΓ.
    
    Lemma to_whnf `{!ConvNeuProperties}  {Δ} {ρ : Δ ≤ Γ} {wfΔ t} (RPt : WProp WA ρ wfΔ t) : whnf t.
    Proof.
      destruct RPt as [| ? []]; constructor; now eapply convneu_whne.
    Qed.

    Definition nf {Δ} {ρ : Δ ≤ Γ} {wfΔ t} (Rt : WRedTm WA ρ wfΔ t) : term :=
      let '(mkWRedTm _ _ _ _ nf _ _ _) := Rt in nf.

    Definition red {Δ} {ρ : Δ ≤ Γ} {wfΔ t} (Rt : WRedTm WA ρ wfΔ t) : [Δ |- t :⤳*: nf Rt : _ ] :=
      let '(mkWRedTm _ _ _ _ _ red _ _) := Rt in red.

    Definition eq {Δ} {ρ : Δ ≤ Γ} {wfΔ t} (Rt : WRedTm WA ρ wfΔ t) : [Δ |- nf Rt ≅ nf Rt : _ ] :=
      let '(mkWRedTm _ _ _ _ _ _ eq _) := Rt in eq.

    Definition prop {Δ} {ρ : Δ ≤ Γ} {wfΔ t} (Rt : WRedTm WA ρ wfΔ t) : WProp WA ρ wfΔ (nf Rt) :=
      let '(mkWRedTm _ _ _ _ _ _ _ prop) := Rt in prop.

  End WRedTmHelpers.
  Arguments WProp' {_ _ _ _ _ _ _ _ _ _ _} _ _ _.
  Arguments WRedTm' {_ _ _ _ _ _ _ _ _ _ _} _ _ _.

  Module WRedTmEqHelpers.
  Section WRedTmEqHelpers.
    Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
      `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
      `{RedTerm ta} {Γ : context} {A: term} {WA : WRedTyPack Γ A} (wfΓ : [|-Γ]).

    Lemma to_whnf `{!ConvNeuProperties} {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (RPtu : WPropEq WA ρ wfΔ t u) : whnf t × whnf u.
    Proof.
      destruct RPtu as [| ?? []]; split; constructor; eapply convneu_whne; tea; now symmetry.
    Qed.

    Definition WRedTmEq' := WRedTmEq WA wk_id wfΓ.
    Definition WPropEq' := WPropEq WA wk_id wfΓ.

    Definition nfL {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (Rtu : WRedTmEq WA ρ wfΔ t u) : term :=
      let '(mkWRedTmEq  _ _ _ _ _ nfL _ _ _ _ _) := Rtu in nfL.

    Definition nfR {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (Rtu : WRedTmEq WA ρ wfΔ t u) : term :=
      let '(mkWRedTmEq  _ _ _ _ _ _ nfR _ _ _ _) := Rtu in nfR.

    Definition redL {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (Rtu : WRedTmEq WA ρ wfΔ t u) : [Δ |- t :⤳*: nfL Rtu : _ ] :=
      let '(mkWRedTmEq  _ _ _ _ _ _ _ redL _ _ _) := Rtu in redL.

    Definition redR {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (Rtu : WRedTmEq WA ρ wfΔ t u) : [Δ |- u :⤳*: nfR Rtu : _ ] :=
      let '(mkWRedTmEq  _ _ _ _ _ _ _ _ redR _ _) := Rtu in redR.

    Definition eq {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (Rtu : WRedTmEq WA ρ wfΔ t u) : [Δ |- nfL Rtu ≅ nfR Rtu : _ ] :=
      let '(mkWRedTmEq  _ _ _ _ _ _ _ _ _ eq _) := Rtu in eq.

    Definition prop {Δ} {ρ : Δ ≤ Γ} {wfΔ t u} (Rtu : WRedTmEq WA ρ wfΔ t u) : WPropEq WA ρ wfΔ (nfL Rtu) (nfR Rtu) :=
      let '(mkWRedTmEq  _ _ _ _ _ _ _ _ _ _ prop) := Rtu in prop.

    Definition mkWRedTmEq := mkWRedTmEq (WA:=WA).
    Definition supReq := supReq (WA:=WA).
    Definition neReq := neReq (WA:=WA).

  End WRedTmEqHelpers.
  Arguments WPropEq' {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _.
  Arguments WRedTmEq' {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _.
  End WRedTmEqHelpers.

 End WRedTm.

Export WRedTm(WRedTm, WProp, WRedTmEq, WPropEq,WRedInductionConcl, WRedInduction, WRedTm', WProp').
Module WRedTmEq := WRedTm.WRedTmEqHelpers.
Export WRedTmEq(WRedTmEq',WPropEq').

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
  | LRW {Γ A} (wfΓ : [|-Γ]) (WA : WRedTyPack@{j} Γ A) (WAad : WRedTyAdequate@{j k} (LR rec) WA) :
    LR rec Γ A (WRedTyEq WA) (WRedTm' WA wfΓ) (WRedTmEq' WA wfΓ)
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

  Definition LRW_@{i j k l} l {Γ A} (wfΓ : [|-Γ]) (WA : WRedTyPack@{k} Γ A)
                 (WAad : WRedTyAdequate (LR (LogRelRec@{i j k} l)) WA)
                 : [LogRel@{i j k l} l | Γ ||- A] :=
    LRbuild (LRW (LogRelRec l) wfΓ WA WAad).

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

(** ** Rebundling reducibility of product and sigma types *)

Module WRedTy.
Section WRedTy.
  Context `{ta : tag} `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}
    {Γ : context} {l : TypeLevel} {A : term}.

  Record WRedTy@{i j k l} :=
    {
      PRT :> ParamRedTy@{i j k l} tW Γ l A ;
      codRed0 : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]),
        [LogRel@{i j k l} l | Δ,, PRT.(ParamRedTy.dom)⟨ρ⟩ ||- PRT.(ParamRedTy.cod)⟨wk_up PRT.(ParamRedTy.dom) ρ⟩]
    }.

  Definition from@{i j k l} {WA : WRedTyPack@{k} Γ A}
    (WAad : WRedTyAdequate@{k l} (LogRel@{i j k l} l) WA) :
    WRedTy@{i j k l}.
  Proof.
    exists (ParamRedTy.from WAad); intros.
    econstructor; now unshelve eapply WRedTyPack.codAd0.
  Defined.

  Definition toPack@{i j k l} (WA : WRedTy@{i j k l}) :
    WRedTyPack@{k} Γ A.
  Proof.
    exists (ParamRedTy.toPack WA).
    intros; now eapply  codRed0.
  Defined.

  Definition toAd@{i j k l} (WA : WRedTy@{i j k l}) :  
    WRedTyAdequate@{k l} (LogRel@{i j k l} l) (toPack WA).
  Proof.
    split.
    - exact (ParamRedTy.toAd WA).
    - intros; eapply  codRed0.
  Defined.

  Lemma eta@{i j k l} (WA : WRedTy@{i j k l}) : from (toAd WA) = WA.
  Proof. reflexivity. Qed.

  Lemma beta_pack@{i j k l} {WA : WRedTyPack@{k} Γ A}
    (WAad : WRedTyAdequate@{k l} (LogRel@{i j k l} l) WA)
    : toPack (from WAad) = WA.
  Proof. reflexivity. Qed.

  Lemma beta_ad@{i j k l} {WA : WRedTyPack@{k} Γ A} 
    (WAad : WRedTyAdequate@{k l} (LogRel@{i j k l} l) WA)
    : toAd (from WAad) = WAad.
  Proof. reflexivity. Qed.

  Lemma ctx_wf@{i j k l} `{!WfContextProperties} (WA : WRedTy@{i j k l}) : [|-Γ].
  Proof. destruct WA as [[]]; gen_typing. Qed.

  Definition LRW'@{i j k l} `{!WfContextProperties} (WA : WRedTy@{i j k l}) :
    [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRW (LogRelRec l) (ctx_wf WA) _ (toAd WA)).

  Definition LRW@{i j k l} (wfΓ: [|-Γ]) (WA : WRedTy@{i j k l}) :
    [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRW (LogRelRec l) wfΓ _ (toAd WA)).

  Definition WRedTyEq@{i j k l} (WA : WRedTy@{i j k l}) := WRedTyEq (toPack WA).
  Definition WRedTm@{i j k l} `{!WfContextProperties} (WA : WRedTy@{i j k l}) := WRedTm' (toPack WA) (ctx_wf WA).
  Definition WRedTmEq@{i j k l} `{!WfContextProperties} (WA : WRedTy@{i j k l}) := WRedTmEq' (toPack WA) (ctx_wf WA).

End WRedTy.
Arguments WRedTy {_ _ _ _ _ _ _ _ _}.
End WRedTy.

Export WRedTy(WRedTy, Build_WRedTy, LRW').
Coercion WRedTy.toPack : WRedTy >-> WRedTyPack.
Coercion WRedTy.PRT : WRedTy >-> ParamRedTy.

Notation "[ Γ ||-W< l > A ]" := (WRedTy Γ l A).
Notation "[ Γ ||-W A ≅ B | RA ]" := (WRedTyEq (Γ:=Γ) (A:=A) RA B).
Notation "[ Γ ||-W t : A | RA | wfΓ ]" := (WRedTm' (Γ:=Γ) (A:=A) RA wfΓ t).
Notation "[ Γ ||-W t ≅ u : A | RA | wfΓ ]" := (WRedTmEq' (Γ:=Γ) (A:=A) RA wfΓ t u).

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










