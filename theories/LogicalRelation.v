From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import Notations MLTTTyping Untyped.

Set Primitive Projections.
Set Universe Polymorphism.


(* Note: modules are used as a hackish solution to go around uniqueness of field names for records *)

(** Helpers for manipulating logical relation data *)

Module LRKit.

  (* A LogRelKit contains all the data we will need from our logical relation*)
  #[universes(polymorphic)] Record LogRelKit@{i j} := {
    TyRel   : context -> term -> Type@{j};
    EqTyRel : forall (Γ : context) (A B   : term), TyRel Γ A -> Type@{i};
    TeRel   : forall (Γ : context) (t A   : term), TyRel Γ A -> Type@{i};
    EqTeRel : forall (Γ : context) (t u A : term), TyRel Γ A -> Type@{i}
  }.

End LRKit.

Export LRKit(LogRelKit,Build_LogRelKit).

Notation "[ K | Γ ||- A ]"               := (K.(LRKit.TyRel) Γ A).
Notation "[ K | Γ ||- A ≅ B | R ]"       := (K.(LRKit.EqTyRel) Γ A B R).
Notation "[ K | Γ ||- t : A | R ]"     := (K.(LRKit.TeRel) Γ t A R).
Notation "[ K | Γ ||- t ≅ u : A | R ]" := (K.(LRKit.EqTeRel) Γ t u A R).

(* The type of our inductively defined reducibility relation:
  for some R : RedRel, R Γ A eqTy redTm eqTm says
  that according to R, A is reducible in Γ and the associated reducible type equality
  (resp. term reducibility, term reducible equality) is eqTy (resp. redTm eqTm).
  One should think of RedRel as a functional relation taking two arguments (Γ and A) and returning
  three outputs (eqTy, redTm and eqTm) *)

  #[universes(polymorphic)]Definition RedRel@{i j | i < j +} :=
  context               ->
  term                  ->
  (term -> Type@{i})         ->
  (term -> Type@{i})         ->
  (term -> term -> Type@{i}) ->
  Type@{j}.

(* An LRPack contains the data corresponding to the codomain of RedRel seen as a functional relation *)

Module LRPack.

  #[universes(polymorphic)] Record LRPack@{i} {Γ : context} {A : term} := {
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

(* An LRPack it adequate wrt. a RedRel when its three unpacked components are *)
#[universes(polymorphic)] Definition LRPackAdequate@{i j} {Γ : context} {A : term}
  (R : RedRel@{i j}) (P : LRPack@{i} Γ A) : Type@{j} :=
  R Γ A P.(LRPack.eqTy) P.(LRPack.redTm) P.(LRPack.eqTm).

Arguments LRPackAdequate _ _ /.

Module LRAd.

  #[universes(polymorphic)] Record > LRAdequate {Γ : context} {A : term} {R : RedRel} := {
    pack :> LRPack Γ A ;
    adequate :> LRPackAdequate R pack
  }.

  Arguments LRAdequate : clear implicits.
  Arguments Build_LRAdequate {_ _ _ _}.

End LRAd.

Export LRAd(LRAdequate,Build_LRAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion LRAd.pack : LRAdequate >-> LRPack.
Coercion LRAd.adequate : LRAdequate >-> LRPackAdequate.

(** Universe levels *)

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

(** Reducibility of neutrals *)

Module neRedTy.

  Record neRedTy {Γ : context} {A : term} : Type := {
    ty : term;
    red : [ Γ |- A :⇒*: ty];
    ne : whne Γ ty;
    refl : [ Γ |- ty ≅ ty]
  }.

  Arguments neRedTy : clear implicits.

End neRedTy.

Export neRedTy(neRedTy, Build_neRedTy).
Notation "[ Γ ||-ne A ]" := (neRedTy Γ A).

Module neRedTyEq.

  Record neRedTyEq {Γ : context} {A B : term} {neA : [ Γ ||-ne A ]} : Type := {
      ty   : term;
      red  : [ Γ |- B :⇒*: ty];
      ne : whne Γ ty;
      eq  : [ Γ |- neA.(neRedTy.ty) ≅ ty]
  }.

  Arguments neRedTyEq : clear implicits.

End neRedTyEq.

Export neRedTyEq(neRedTyEq,Build_neRedTyEq).
Notation "[ Γ ||-ne A ≅ B | R ]" := (neRedTyEq Γ A B R).

Module neRedTm.

  Record neRedTm {Γ : context} {t A : term} {R : [ Γ ||-ne A ]} : Type := {
      term  : term;
      red  : [ Γ |- t :⇒*: term : R.(neRedTy.ty)];
      ne : whne Γ term ;
  }.

  Arguments neRedTm : clear implicits.

End neRedTm.

Export neRedTm(neRedTm, Build_neRedTm).

Notation "[ Γ ||-ne t : A | B ]" := (neRedTm Γ t A B).

Module neRedTmEq.

  Record neRedTmEq {Γ : context} {t u A : term} {R : [ Γ ||-ne A ]} : Type := {
      termL     : term;
      termR     : term;
      redL      : [ Γ |- t :⇒*: termL : R.(neRedTy.ty) ];
      redR      : [ Γ |- u :⇒*: termR : R.(neRedTy.ty) ];
      whneL : whne Γ termL;
      whneR : whne Γ termR;
      eq : [ Γ |- termL ≅ termR : A]
  }.

  Arguments neRedTmEq : clear implicits.

End neRedTmEq.

Export neRedTmEq(neRedTmEq, Build_neRedTmEq).
Notation "[ Γ ||-ne t ≅ u : A | R ] " := (neRedTmEq Γ t u A R).

Module URedTy.

  Record URedTy {l} {Γ : context} : Type := {
    level  : TypeLevel;
    lt  : level << l;
    wfCtx : [ |- Γ ]
  }.

  Arguments URedTy : clear implicits.

  Record URedTyEq {Γ : context} {B : term} : Type := {
    eq : B = U
  }.

  Arguments URedTyEq : clear implicits.

End URedTy.

Export URedTy(URedTy,Build_URedTy,URedTyEq,Build_URedTyEq).

Notation "[ Γ ||-U l ]" := (URedTy l Γ).
Notation "[ Γ ||-U≅ B ]" := (URedTyEq Γ B).

Module URedTm.

  Record URedTm {l} {rec : forall {l'}, l' << l -> LogRelKit}
  {Γ : context} {t : term} {R : [Γ ||-U l]} : Type := {
    term : term;
    red : [ Γ |- t :⇒*: term : U ];
    type : isType Γ term;
    rel : [rec R.(URedTy.lt) | Γ ||- t ] ;
  }.

  Arguments URedTm {_}.

  (*Universe term equality*)
  Record URedTmEq {l } {rec : forall {l'}, l' << l -> LogRelKit}
  {Γ : context} {t u : PCUICAst.term} {R : [Γ ||-U l]} := {
    redL : URedTm (@rec) Γ t R ;
    redR : URedTm (@rec) Γ u R ;
    eq   : [ Γ |- redL.(term) ≅ redR.(term) : U ];
    relL    : [ rec R.(URedTy.lt) | Γ ||- t ] ;
    relR    : [ rec R.(URedTy.lt) | Γ ||- u ] ;
    relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u | relL ] ;
  }.

  Arguments URedTmEq {_}.

End URedTm.

Export URedTm(URedTm,Build_URedTm,URedTmEq,Build_URedTmEq).
Notation "[ R | Γ ||-U t :U | l ]" := (URedTm R Γ t l).
Notation "[ R | Γ ||-U t ≅ u :U | l ]" := (URedTmEq R Γ t u l).

Module PiRedTy.

  #[universes(polymorphic)]Record PiRedTy@{i} {Γ : context} {A : term} := {
    na : aname ;
    dom : term ;
    cod : term ;
    redPi := tProd na dom cod ;
    red : [Γ |- A :⇒*: redPi];
    domTy : [Γ |- dom];
    codTy : [Γ ,, vass na dom |- cod];
    domRed {Δ} : [ |- Δ ] -> LRPack@{i} Δ dom;
    codRed {Δ a} (h : [ |- Δ ]) :
        [ (domRed h) |  Δ ||- a : dom ] ->
        LRPack@{i} Δ (cod{0 := a});
    codExt
      {Δ a b}
      (h :  [ |- Δ ])
      (ha : [ (domRed h) | Δ ||- a : dom ]) :
      [ (domRed h) | Δ ||- b : dom ] ->
      [ (domRed h) | Δ ||- a ≅ b : dom ] ->
      [ (codRed h ha) | Δ ||- (cod{0 := a}) ≅ (cod{0 := b}) ];
  }.

  Arguments PiRedTy : clear implicits.

  #[universes(polymorphic)] Record PiRedTyAdequate
    {Γ : context} {A : term} {R : RedRel} {ΠA : PiRedTy Γ A} :=
  {
    domAd {Δ} (h : [ |- Δ ]) : LRPackAdequate R (ΠA.(domRed) h);
    codAd {Δ a} (h : [ |- Δ ]) (ha : [ (ΠA.(domRed) h) | Δ ||- a : ΠA.(dom) ])
      : LRPackAdequate R (ΠA.(codRed) h ha);
  }.

  Arguments PiRedTyAdequate {_ _}.

End PiRedTy.

Export PiRedTy(PiRedTy,Build_PiRedTy,PiRedTyAdequate,Build_PiRedTyAdequate).
Notation "[ Γ ||-Πd A ]" := (PiRedTy Γ A).

Module PiRedTyEq.

  Record PiRedTyEq {Γ : context} {A B : term} {ΠA : PiRedTy Γ A} := {
    na                        : aname ;
    dom                       : term;
    cod                       : term;
    redPi                     := tProd na dom cod ;
    red                       : [Γ |- B :⇒*: redPi];
    eq                        : [Γ |- ΠA.(PiRedTy.redPi) ≅ redPi ];
    domRed {Δ} (h : [ |- Δ ]) : [ (ΠA.(PiRedTy.domRed) h) | Δ ||- ΠA.(PiRedTy.dom) ≅ dom ];
    codRed {Δ a} (h : [ |- Δ ])
      (ha : [ ΠA.(PiRedTy.domRed) h | Δ ||- a : ΠA.(PiRedTy.dom)]) :
      [ (ΠA.(PiRedTy.codRed) h ha) | Δ ||- ΠA.(PiRedTy.cod){0 := a} ≅ cod{0 := a} ];
  }.

  Arguments PiRedTyEq : clear implicits.

End PiRedTyEq.

Export PiRedTyEq(PiRedTyEq,Build_PiRedTyEq).
Notation "[ Γ ||-Π A ≅ B | ΠA ]" := (PiRedTyEq Γ A B ΠA).

Module PiRedTm.

  Record PiRedTm {Γ : context} {t A : term} {ΠA : PiRedTy Γ A} := {
    nf : term;
    red : [ Γ |- t :⇒*: nf : ΠA.(PiRedTy.redPi) ];
    isfun : isFun Γ nf;
    refl : [ Γ |- nf ≅ nf : ΠA.(PiRedTy.redPi) ];
    app {Δ a} (h : [ |- Δ ])
      (ha : [ (ΠA.(PiRedTy.domRed) h) | Δ ||- a : ΠA.(PiRedTy.dom) ])
      : [(ΠA.(PiRedTy.codRed) h ha) | Δ ||- tApp nf a : ΠA.(PiRedTy.cod){0 := a} ] ;
    eq {Δ a b} (h : [ |- Δ ])
      (ha : [ (ΠA.(PiRedTy.domRed) h) | Δ ||- a : ΠA.(PiRedTy.dom) ])
      (hb : [ (ΠA.(PiRedTy.domRed) h) | Δ ||- b : ΠA.(PiRedTy.dom) ])
      (eq : [ (ΠA.(PiRedTy.domRed) h) | Δ ||- a ≅ b : ΠA.(PiRedTy.dom) ])
      : [ (ΠA.(PiRedTy.codRed) h ha) | Δ ||- tApp nf a ≅ tApp nf b : ΠA.(PiRedTy.cod){0 := a} ]
  }.

  Arguments PiRedTm : clear implicits.

End PiRedTm.

Export PiRedTm(PiRedTm,Build_PiRedTm).
Notation "[ Γ ||-Π t : A | ΠA ]" := (PiRedTm Γ t A ΠA).

Module PiRedTmEq.

  Record PiRedTmEq {Γ : context} {t u A : term} {ΠA : PiRedTy Γ A}  := {
      redL : [ Γ ||-Π t : A | ΠA ] ;
      redR : [ Γ ||-Π u : A | ΠA ] ;
      eq : [ Γ |- redL.(PiRedTm.nf) ≅ redR.(PiRedTm.nf) : ΠA.(PiRedTy.redPi) ];
      eqApp {Δ a} (h : [ |- Δ ])
        (ha : [ (ΠA.(PiRedTy.domRed) h) | Δ ||- a : ΠA.(PiRedTy.dom) ] )
        : [ ( ΠA.(PiRedTy.codRed) h ha) | Δ ||-
            tApp redL.(PiRedTm.nf) a ≅ tApp redR.(PiRedTm.nf) a : ΠA.(PiRedTy.cod){0 := a}]
  }.

  Arguments PiRedTmEq : clear implicits.

End PiRedTmEq.

Export PiRedTmEq(PiRedTmEq,Build_PiRedTmEq).

Notation "[ Γ ||-Π t ≅ u : A | ΠA ]" := (PiRedTmEq Γ t u A ΠA).

Unset Elimination Schemes.

#[universes(polymorphic)]Inductive LR {l : TypeLevel} (rec : forall l', l' << l -> LogRelKit)
  : RedRel :=
  | LRU {Γ} (H : [Γ ||-U l]) :
      LR rec Γ U
      (fun B   => [Γ ||-U≅ B ])
      (fun t   => [ rec | Γ ||-U t     :U | H ])
      (fun t u => [ rec | Γ ||-U t ≅ u :U | H ])
  | LRne {Γ A} (neA : [ Γ ||-ne A ]) :
      LR rec Γ A
      (fun B   =>  [ Γ ||-ne A ≅ B     | neA])
      (fun t   =>  [ Γ ||-ne t     : A | neA])
      (fun t u =>  [ Γ ||-ne t ≅ u : A | neA])
  | LRPi {Γ : context} {A : term} (ΠA : [ Γ ||-Πd A ]) (ΠAad : PiRedTyAdequate (LR rec) ΠA) :
    LR rec Γ A
      (fun B   => [ Γ ||-Π A ≅ B     | ΠA ])
      (fun t   => [ Γ ||-Π t     : A | ΠA ])
      (fun t u => [ Γ ||-Π t ≅ u : A | ΠA ])
  (* Removed, as it is provable (!), cf LR_embedding in LRInduction *)
  (* | LREmb {Γ A l'} (l_ : l' << l) (H : [ rec l' l_ | Γ ||- A]) :
      LR rec Γ A
      (fun B   => [ rec l' l_ | Γ ||- A ≅ B     | H ])
      (fun t   => [ rec l' l_ | Γ ||- t     : A | H ])
      (fun t u => [ rec l' l_ | Γ ||- t ≅ u : A | H ]) *)
  .

Set Elimination Schemes.

(* Definition RelTy
{l : TypeLevel} (R : forall l', l' << l -> LogRelKit)
(Γ : context) (A : term) :=
  LRAdequate Γ A (LR R).

Notation "[ R | Γ ||-p A ]" := (RelTy R Γ A) (at level 0). *)
(* 
Definition RelTyEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (A B : term) (H : RelTy R Γ A) :=
  [ Γ ||-p A ≅ B | H ].

Definition RelTe {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t A : term) (H : RelTy R Γ A) :=
  [ Γ ||-p t : A | H ].

Definition RelTeEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t u A : term) (H : RelTy R Γ A) :=
  [ Γ ||-p t ≅ u : A | H ]. *)

#[universes(polymorphic)]Definition rec0 (l' : TypeLevel) (h : l' << zero) : LogRelKit :=
  match elim h with
  end.

#[universes(polymorphic)]Definition kit0 :=
  Build_LogRelKit
  (fun Γ A => LRAdequate Γ A (LR rec0))
  (fun Γ A B (R : LRAdequate Γ A (LR rec0)) => R.(LRPack.eqTy) B)
  (fun Γ t A (R : LRAdequate Γ A (LR rec0)) => R.(LRPack.redTm) t)
  (fun Γ t u A (R : LRAdequate Γ A (LR rec0)) => R.(LRPack.eqTm) t u).

Definition LogRelRec (l : TypeLevel) : forall l', l' << l -> LogRelKit :=
  match l with
    | zero => rec0
    | one => fun _ _ => kit0
  end.

Arguments LogRelRec l l' l_ /.

Definition rec1 :=
  LogRelRec one.

Definition LRl (l : TypeLevel) :=
  LR (LogRelRec l).

  (*TODO minimiser univers*)
Definition kit (l : TypeLevel) : LogRelKit :=
  Build_LogRelKit
    (fun Γ A => LRAdequate Γ A (LRl l))
    (fun Γ A B (R : LRAdequate Γ A (LRl l)) => R.(LRPack.eqTy) B)
    (fun Γ t A (R : LRAdequate Γ A (LRl l)) => R.(LRPack.redTm) t)
    (fun Γ t u A (R : LRAdequate Γ A (LRl l)) => R.(LRPack.eqTm) t u).

Definition KitRedTy (Γ : context) (l : TypeLevel) (A : term) : Type :=
  [ kit l | Γ ||- A].
Definition KitEqTy (Γ : context) (l : TypeLevel) (A B: term) (H : KitRedTy Γ l A): Type :=
  [ kit l | Γ ||- A ≅ B | H].
Definition KitRedTm (Γ : context) (l : TypeLevel) (t A : term) (H : KitRedTy Γ l A) : Type :=
  [ kit l | Γ ||- t : A | H].
Definition KitEqTm (Γ : context) (l : TypeLevel) (t u A : term) (H : KitRedTy Γ l A) : Type :=
  [ kit l | Γ ||- t ≅ u : A | H].

Notation "[ Γ ||-< l > A ]" := (KitRedTy Γ l A).
Notation "[ Γ ||-< l > A ≅ B | R ]" := (KitEqTy Γ l A B R).
Notation "[ Γ ||-< l > t : A | R ]" := (KitRedTm Γ l t A R).
Notation "[ Γ ||-< l > t ≅ u : A | R ]" := (KitEqTm Γ l t u A R).

Definition LRbuild {Γ l A rEq rTe rTeEq} :
  LR (LogRelRec l) Γ A rEq rTe rTeEq ->
  [Γ ||-< l > A] :=
  fun H => {|
    LRAd.pack := {| LRPack.eqTy := rEq ; LRPack.redTm := rTe ; LRPack.eqTm := rTeEq |} ;
    LRAd.adequate := H |}.

Definition LRunbuild {Γ l A} :
  [Γ ||-< l > A] ->
  ∑ rEq rTe rTeEq , LR (LogRelRec l) Γ A rEq rTe rTeEq :=
    fun H => (LRPack.eqTy H; LRPack.redTm H; LRPack.eqTm H; H.(LRAd.adequate)).

Create HintDb logrel.
#[global] Hint Constants Opaque : logrel.
#[global] Hint Variables Transparent : logrel.
Ltac logrel := eauto with logrel.

#[global] Hint Resolve LRbuild LRunbuild : logrel.

Definition LRU_ {l Γ} (H : [Γ ||-U l]) : [Γ ||-< l > U] :=
  LRbuild (LRU (LogRelRec l) H).

Definition LRne_ l {Γ A} (neA : [Γ ||-ne A])
  : [Γ ||-< l > A] :=
  LRbuild (LRne (LogRelRec l) neA).

Definition LRPi_ l {Γ A} (ΠA : [Γ ||-Πd A]) (ΠAad : PiRedTyAdequate (LR (LogRelRec l)) ΠA)
  : [Γ ||-< l > A] :=
  LRbuild (LRPi (LogRelRec l) ΠA ΠAad).