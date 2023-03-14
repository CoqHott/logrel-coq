(** * LogRel.LogicalRelation: definition of the logical relation *)
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
    red : [ Γ |- A :⇒*: ty];
    ne : whne ty;
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
    red  : [ Γ |- B :⇒*: ty];
    ne : whne ty;
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
    red  : [ Γ |- t :⇒*: te : R.(neRedTy.ty)];
    ne : whne te ;
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
    redL      : [ Γ |- t :⇒*: termL : R.(neRedTy.ty) ];
    redR      : [ Γ |- u :⇒*: termR : R.(neRedTy.ty) ];
    whneL : whne termL;
    whneR : whne termR;
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
    red : [ Γ |- A  :⇒*: U ]
  }.

  Arguments URedTy {_ _ _ _}.

End URedTy.

Export URedTy(URedTy,Build_URedTy).


Notation "[ Γ ||-U< l > A ]" := (URedTy l Γ A) (at level 0, Γ, l, A at level 50).

Module URedTyEq.

  Record URedTyEq `{ta : tag} `{!WfType ta} `{!RedType ta} 
    {Γ : context} {B : term} : Set := {
    red : [Γ |- B :⇒*: U]
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
    red : [ Γ |- t :⇒*: te : U ];
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

  Arguments URedTmEq {_ _ _ _ _ _  _ _} rec.

End URedTm.

Export URedTm(URedTm,Build_URedTm,URedTmEq,Build_URedTmEq).
Notation "[ R | Γ ||-U t : A | l ]" := (URedTm R Γ t A l) (at level 0, R, Γ, t, A, l at level 50).
Notation "[ R | Γ ||-U t ≅ u : A | l ]" := (URedTmEq R Γ t u A l) (at level 0, R, Γ, t, u, A, l at level 50).

(** ** Reducibility of product types *)

Module PiRedTy.

  Record PiRedTy@{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A : term}
  : Type (* @ max(Set, i+1) *) := {
    na : aname ;
    dom : term ;
    cod : term ;
    red : [Γ |- A :⇒*: tProd na dom cod];
    domTy : [Γ |- dom];
    codTy : [Γ ,, vass na dom |- cod];
    eq : [Γ |- tProd na dom cod ≅ tProd na dom cod];
    domRed {Δ} (ρ : Δ ≤ Γ) : [ |- Δ ] -> LRPack@{i} Δ dom⟨ρ⟩ ;
    codRed {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
        [ (domRed ρ h) |  Δ ||- a : dom⟨ρ⟩] ->
        LRPack@{i} Δ (cod[a .: (ρ >> tRel)]) ;
    codExt
      {Δ a b}
      (ρ : Δ ≤ Γ)
      (h :  [ |- Δ ])
      (ha : [ (domRed ρ h) | Δ ||- a : dom⟨ρ⟩ ]) :
      [ (domRed ρ h) | Δ ||- b : dom⟨ρ⟩] ->
      [ (domRed ρ h) | Δ ||- a ≅ b : dom⟨ρ⟩] ->
      [ (codRed ρ h ha) | Δ ||- (cod[a .: (ρ >> tRel)]) ≅ (cod[b .: (ρ >> tRel)]) ]
  }.

  Arguments PiRedTy {_ _ _ _ _}.

  (** We separate the recursive "data", ie the fact that we have reducibility data (an LRPack)
  for the domain and codomain, and the fact that these are in the graph of the logical relation.
  This is crucial for Coq to accept the definition, because it makes the nesting simple enough
  to be accepted. We later on show an induction principle that does not have this separation to
  make reasoning easier. *)
  Record PiRedTyAdequate@{i j} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A : term} {R : RedRel@{i j}} {ΠA : PiRedTy@{i} Γ A}
  : Type@{j} := {
    domAd {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) : LRPackAdequate@{i j} R (ΠA.(domRed) ρ h);
    codAd {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ (ΠA.(domRed) ρ h) | Δ ||- a : ΠA.(dom)⟨ρ⟩ ])
      : LRPackAdequate@{i j} R (ΠA.(codRed) ρ h ha);
  }.

  Arguments PiRedTyAdequate {_ _ _ _ _ _ _}.

End PiRedTy.

Export PiRedTy(PiRedTy,Build_PiRedTy,PiRedTyAdequate,Build_PiRedTyAdequate).
Notation "[ Γ ||-Πd A ]" := (PiRedTy Γ A).

Module PiRedTyEq.

  Record PiRedTyEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} {ΠA : PiRedTy Γ A}
  : Type := {
    na : aname ;
    dom : term;
    cod : term;
    red : [Γ |- B :⇒*: tProd na dom cod];
    eq  : [Γ |- tProd ΠA.(PiRedTy.na) ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ≅ tProd na dom cod ];
    domRed {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
      [ (ΠA.(PiRedTy.domRed) ρ h) | Δ ||- ΠA.(PiRedTy.dom)⟨ρ⟩ ≅ dom⟨ρ⟩ ];
    codRed {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PiRedTy.domRed) ρ h | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩]) :
      [ (ΠA.(PiRedTy.codRed) ρ h ha) | Δ ||- ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)] ≅ cod[a .: (ρ >> tRel)] ];
  }.

  Arguments PiRedTyEq {_ _ _ _ _}.

End PiRedTyEq.

Export PiRedTyEq(PiRedTyEq,Build_PiRedTyEq).
Notation "[ Γ ||-Π A ≅ B | ΠA ]" := (PiRedTyEq Γ A B ΠA).

Module PiRedTm.

  Record PiRedTm `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{RedTerm ta}
    {Γ : context} {t A : term} {ΠA : PiRedTy Γ A}
  : Type := {
    nf : term;
    red : [ Γ |- t :⇒*: nf : tProd ΠA.(PiRedTy.na) ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ];
    isfun : isFun nf;
    refl : [ Γ |- nf ≅ nf : tProd ΠA.(PiRedTy.na) ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ];
    app {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ (ΠA.(PiRedTy.domRed) ρ h) | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      : [(ΠA.(PiRedTy.codRed) ρ h ha) | Δ ||- tApp nf⟨ρ⟩ a : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]] ;
    eq {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ (ΠA.(PiRedTy.domRed) ρ h) | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      (hb : [ (ΠA.(PiRedTy.domRed) ρ h) | Δ ||- b : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      (eq : [ (ΠA.(PiRedTy.domRed) ρ h) | Δ ||- a ≅ b : ΠA.(PiRedTy.dom)⟨ρ⟩ ])
      : [ (ΠA.(PiRedTy.codRed) ρ h ha) | Δ ||- tApp nf⟨ρ⟩ a ≅ tApp nf⟨ρ⟩ b : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)] ]
  }.

  Arguments PiRedTm {_ _ _ _ _ _ _ _}.

End PiRedTm.

Export PiRedTm(PiRedTm,Build_PiRedTm).
Notation "[ Γ ||-Π t : A | ΠA ]" := (PiRedTm Γ t A ΠA).

Module PiRedTmEq.

  Record PiRedTmEq `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{RedTerm ta}
    {Γ : context} {t u A : term} {ΠA : PiRedTy Γ A}
  : Type := {
    redL : [ Γ ||-Π t : A | ΠA ] ;
    redR : [ Γ ||-Π u : A | ΠA ] ;
    eq : [ Γ |- redL.(PiRedTm.nf) ≅ redR.(PiRedTm.nf) : tProd ΠA.(PiRedTy.na) ΠA.(PiRedTy.dom) ΠA.(PiRedTy.cod) ];
    eqApp {Δ a} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [(ΠA.(PiRedTy.domRed) ρ h) | Δ ||- a : ΠA.(PiRedTy.dom)⟨ρ⟩ ] )
      : [ ( ΠA.(PiRedTy.codRed) ρ h ha) | Δ ||-
          tApp redL.(PiRedTm.nf)⟨ρ⟩ a ≅ tApp redR.(PiRedTm.nf)⟨ρ⟩ a : ΠA.(PiRedTy.cod)[a .: (ρ >> tRel)]]
  }.

  Arguments PiRedTmEq {_ _ _ _ _ _ _ _}.

End PiRedTmEq.

Export PiRedTmEq(PiRedTmEq,Build_PiRedTmEq).

Notation "[ Γ ||-Π t ≅ u : A | ΠA ]" := (PiRedTmEq Γ t u A ΠA).

Module NeNf.
  Record RedTm `{ta : tag} `{Typing ta} `{ConvNeuConv ta} {Γ k A} : Set :=
    {
      ne : whne k ;
      ty : [Γ |- k : A] ;
      refl : [Γ |- k ~ k : A]
    }.
  Arguments RedTm {_ _ _}.

  Record RedTmEq `{ta : tag} `{ConvNeuConv ta} {Γ k l A} : Set :=
    {
      neL : whne k;
      neR : whne l;
      conv : [Γ |- k ~ l : A]
    }.

  Arguments RedTmEq {_ _}.
End NeNf.

Notation "[ Γ ||-NeNf k : A ]" := (NeNf.RedTm Γ k A) (at level 0, Γ, k, A at level 50).
Notation "[ Γ ||-NeNf k ≅ l : A ]" := (NeNf.RedTmEq Γ k l A) (at level 0, Γ, k, l, A at level 50).

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
      (fun t u => [ Γ ||-Π t ≅ u : A | ΠA ]).
  
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

End MoreDefs.
  
(** To be explicit with universe levels use the rhs, e.g
   [ LogRel@{i j k l} l | Γ ||- A] or [ LogRel0@{i j k} ||- Γ ||- A ≅ B | RA ]
 *)
Notation "[ Γ ||-< l > A ]" := [ LogRel l | Γ ||- A ].
Notation "[ Γ ||-< l > A ≅ B | RA ]" := [ LogRel l | Γ ||- A ≅ B | RA ].
Notation "[ Γ ||-< l > t : A | RA ]" := [ LogRel l | Γ ||- t : A | RA ].
Notation "[ Γ ||-< l > t ≅ u : A | RA ]" := [ LogRel l | Γ ||- t ≅ u : A | RA ].

(** ** Rebundling reducibility of product types *)

(** The definition of reducibility of product types in the logical relation, which separates
the "adequacy" part is not nice to work with. Here we relate it to the more natural one,
which lets us later on define an induction principle that does not show the separation at all. *)

Module PiRedTyPack.
Section PiRedTyPack.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.


  Record PiRedTyPack@{i j k l} {Γ : context} {A : term} {l : TypeLevel} 
    : Type@{l} := {
      na : aname ;
      dom : term ;
      cod : term ;
      red : [Γ |- A :⇒*: tProd na dom cod];
      domTy : [Γ |- dom];
      codTy : [Γ ,, vass na dom |- cod];
      eq : [Γ |- tProd na dom cod ≅ tProd na dom cod];
      domRed {Δ} (ρ : Δ ≤ Γ) : [ |- Δ ] -> [ LogRel@{i j k l} l | Δ ||- dom⟨ρ⟩ ] ;
      codRed {Δ} {a} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
          [ (domRed ρ h) |  Δ ||- a : dom⟨ρ⟩] ->
          [ LogRel@{i j k l} l | Δ ||- cod[a .: (ρ >> tRel)]] ;
      codExt
        {Δ a b}
        (ρ : Δ ≤ Γ)
        (h :  [ |- Δ ])
        (ha : [ (domRed ρ h) | Δ ||- a : dom⟨ρ⟩ ]) :
        [ (domRed ρ h) | Δ ||- b : dom⟨ρ⟩] ->
        [ (domRed ρ h) | Δ ||- a ≅ b : dom⟨ρ⟩] ->
        [ (codRed ρ h ha) | Δ ||- (cod[a .: (ρ >> tRel)]) ≅ (cod[b .: (ρ >> tRel)]) ]
    }.

  Arguments PiRedTyPack : clear implicits.

  Definition pack@{i j k l} {Γ A l} (ΠA : PiRedTy@{k} Γ A)
    (ΠAad : PiRedTyAdequate (LogRel@{i j k l} l) ΠA) 
    : PiRedTyPack@{i j k l} Γ A l.
  Proof.
    destruct ΠA as [na dom cod]; destruct ΠAad; cbn in *.
    unshelve econstructor; [eassumption| exact dom| exact cod|..].
    3-6: assumption.
    * intros; econstructor; now unshelve apply domAd.
    * intros; econstructor; now unshelve apply codAd.
    * intros. cbn. eauto.
  Defined.
    
  Definition toPiRedTy@{i j k l} {Γ A l} (ΠA : PiRedTyPack@{i j k l} Γ A l) :
    PiRedTy@{k} Γ A.
  Proof.
    destruct ΠA as [na dom cod ???? domRed codRed codExt].
    unshelve econstructor; [assumption|exact dom|exact cod|..].
    3-6: assumption.
    * intros; now eapply domRed.
    * intros; now eapply codRed.
    * intros; now eapply codExt.
  Defined.
  
  Definition toPiRedTyAd@{i j k l} {Γ A l} (ΠA : PiRedTyPack@{i j k l} Γ A l) :
    PiRedTyAdequate (LogRel@{i j k l} l) (toPiRedTy ΠA).
  Proof.
    destruct ΠA as [na dom cod ???? domRed codRed ?].
    unshelve econstructor; cbn; intros; [eapply domRed|eapply codRed].
  Defined.  

  Lemma pack_eta @{i j k l} {Γ A l} (ΠA : PiRedTyPack@{i j k l} Γ A l) :
    pack _ (toPiRedTyAd ΠA) = ΠA.
  Proof. destruct ΠA; reflexivity. Qed.

  Lemma pack_beta @{i j k l} {Γ A l} (ΠA : PiRedTy@{k} Γ A)
    (ΠAad : PiRedTyAdequate (LogRel@{i j k l} l) ΠA)  :
    toPiRedTy (pack _ ΠAad) = ΠA.
  Proof. destruct ΠA; destruct ΠAad; reflexivity. Qed.

  Lemma pack_beta_ad @{i j k l} {Γ A l} (ΠA : PiRedTy@{k} Γ A)
    (ΠAad : PiRedTyAdequate (LogRel@{i j k l} l) ΠA)  :
    toPiRedTyAd (pack _ ΠAad) = ΠAad.
  Proof. destruct ΠA; destruct ΠAad; reflexivity. Qed.

  Definition LRPi'@{i j k l} {l Γ A} (ΠA : PiRedTyPack@{i j k l} Γ A l)
    : [ LogRel@{i j k l} l | Γ ||- A ] :=
    LRbuild (LRPi (LogRelRec l) _ (toPiRedTyAd ΠA)).

  Definition prod@{i j k l} {l Γ A} (ΠA : PiRedTyPack@{i j k l} Γ A l) : term :=
    tProd (na ΠA) (dom ΠA) (cod ΠA).

  Lemma whne_noΠ `{!RedTypeProperties} {Γ A} : [Γ ||-Πd A] -> whne A -> False.
  Proof.
    intros [??? [?? r]] h.
    pose proof (UntypedReduction.red_whne _ _ (redty_red r) h).
    subst; inversion h.
  Qed.

End PiRedTyPack.

Arguments PiRedTyPack : clear implicits.
Arguments PiRedTyPack {_ _ _ _ _ _ _ _ _} _ _ _.

End PiRedTyPack.

Export PiRedTyPack(PiRedTyPack,Build_PiRedTyPack, LRPi').
Notation "[ Γ ||-Π< l > A ]" := (PiRedTyPack Γ A l) (at level 0, Γ, l, A at level 50).

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
    LogRelRec l (URedTy.level h) (URedTy.lt h) Γ t eqTy redTm eqTm <≈>
    LogRel (URedTy.level h) Γ t eqTy redTm eqTm.
  Proof.
    destruct l; [destruct (elim (URedTy.lt h))|].
    destruct h; inversion lt; subst; cbn; now split.
  Qed.


  Lemma TyEqRecFwd {l Γ A t u} (h : [Γ ||-U<l> A]) 
    (lr : [LogRelRec l (URedTy.level h) (URedTy.lt h) | Γ ||- t]) :
    [lr | Γ ||- t ≅ u] <≈> [RedTyRecFwd h lr | Γ ||- t ≅ u].
  Proof.
    unfold RedTyRecFwd.
    destruct h as [? lt]; cbn in *.
    induction lt; cbn; split; easy.
  Qed.

  Lemma TyEqRecBwd {l Γ A t u} (h : [Γ ||-U<l> A]) 
    (lr : [LogRel (URedTy.level h) | Γ ||- t ]) :
    [lr | Γ ||- t ≅ u] <≈> [RedTyRecBwd h lr | Γ ||- t ≅ u].
  Proof.
    unfold RedTyRecBwd.
    destruct h as [? lt]; cbn in *.
    induction lt; cbn; split; easy.
  Qed.

End LogRelRecFoldLemmas.

