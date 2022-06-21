Require Import MLTTTyping.
Require Import Untyped.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition PCUICNormal PCUICCanonicity.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases.



Set Primitive Projections.
Set Universe Polymorphism.
Set Printing Universes.


Record neType (Γ : context) (A : term) : Type := ne {
    K  : term;
    D  : [ Γ |- A :⇒*: K];
    neK : neutral Γ K
}.

Notation "[ Γ ||-ne A ]" := (neType Γ A)  (at level 0).

Record neTypeEq (Γ : context) (A B : term) (C : [ Γ ||-ne A ]) : Type := nee {
    M   : term;
    D'  : [ Γ |- B :⇒*: A];
    neM : neutral Γ M;
    KM  : [ Γ |- K _ _ C ≅ M]
}.

Notation "[ Γ ||-ne A ≅ B | C ]" := (neTypeEq Γ A B C) (at level 0).

Record neTermNF (Γ : context) (k A : term) : Type := neTeNF {
    neknf : neutral Γ k;
    tkTy  : [ Γ |- k ::: A];
}.

Notation "[ Γ ||-neNf t ::: A ]" := (neTermNF Γ t A) (at level 0).

Record neTerm (Γ : context) (t A : term) (C : [ Γ ||-ne A ]) : Type := neTe {
    k  : term;
    d  : [ Γ |- t :⇒*: k ::: K _ _ C];
    nf : [ Γ ||-neNf k ::: K _ _ C]
}.

Notation "[ Γ ||-ne t ::: A | B ]" := (neTerm Γ t A B) (at level 0).

Record neTermEqNF (Γ : context) (k m A : term): Type := neTeEqNF {
    nekeq  : neutral Γ k;
    nekmeq : neutral Γ m;
    kEqm   : [ Γ |- k ≅ m ::: A]
}.

Notation "[ Γ ||-neNf t ≅ u ::: A ]" := (neTermEqNF Γ t u A) (at level 0).


Record neTermEq (Γ : context) (t u A : term) (C : [ Γ ||-ne A ]) : Type := neTeEq {
    k'     : term;
    m'     : term;
    d'     : [ Γ |- t :⇒*: k' ::: A ];
    d''    : [ Γ |- u :⇒*: m' ::: A ];
    kNFEqm : [ Γ ||-neNf k' ≅ m' ::: A ]
}.

Notation "[ Γ ||-ne t ≅ u ::: A | B ] " := (neTermEq Γ t u A B) (at level 0).

Inductive TypeLevel : Set :=
  | zero : TypeLevel
  | one  : TypeLevel.

Inductive TypeLevelLe : TypeLevel -> TypeLevel -> Type :=
    | Oi : TypeLevelLe zero one.

Notation "A << B" := (TypeLevelLe A B) (at level 0).

Module Type LogRelRec.

  Parameter l       : TypeLevel.
  Parameter URel    : context         -> Type.
  Parameter PiRel   : context -> term -> Type.
  Parameter TyRel   : context -> term -> Type.
  Parameter EqTyRel : forall (Γ : context) (A B : term)  , TyRel Γ A -> Type.
  Parameter TeRel   : forall (Γ : context) (t A : term)  , TyRel Γ A -> Type.
  Parameter EqTeRel : forall (Γ : context) (t u A : term), TyRel Γ A -> Type.

  Notation "[ Γ ||-U ]"                := (URel Γ) (at level 0).
  Notation "[ Γ ||-Π A ]"              := (PiRel Γ A) (at level 0).
  Notation "[ Γ ||- A ]"               := (TyRel Γ A) (at level 0).
  Notation "[ Γ ||- A ≅ B | C ]"       := (EqTyRel Γ A B C) (at level 0).
  Notation "[ Γ ||- t ::: A | C ]"     := (TeRel Γ t A C) (at level 0).
  Notation "[ Γ ||- t ≅ u ::: A | C ]" := (EqTeRel Γ t u A C) (at level 0).

End LogRelRec.

Module LogRel (LR : LogRelRec) .

  Import LR.
  (*Parameter rec : forall {l'},l' << l -> LogRelRec l'.*)

  Record URel' (Γ : context) : Type := { 
    l'  : TypeLevel;
    l_  : l' << l;
    wfc : [ |- Γ ]
  }.

  Notation "[ Γ ||-1U ]" := (URel' Γ) (at level 0).

  Record URelEq (Γ : context) (B : term) : Type := { 
    Beq : B = U
  }.
    
  Notation "[ Γ ||-1U≅ B ]" := (URelEq Γ B) (at level 0).

  Record UTerm {l' : TypeLevel} (Γ : context) (t : term) (l_ : l' << l) := {
    A : term;
    d : [ Γ |- t :⇒*: A ::: U ];
    typeA : isType A;
    tyrel : [Γ ||- t] ;
  }.

  Notation "[ Γ ||-1U t :::U| l ]" := (UTerm Γ t l) (at level 0).

  (*Universe term equality*)
  Record UTeEq {l'} (Γ : context) (t u : term) (l_ : l' << l) := {
      A'      : term;
      B'      : term;
      d_      : [ Γ |- t :⇒*: A' ::: U ];
      d'      : [ Γ |- u :⇒*: B' ::: U ];
      typeA'  : isType A';
      typeB'  : isType B';
      AeqBU   : [ Γ |- A' ≅ B' ::: U ];
      relt    : [ Γ ||- t ];
      relu    : [ Γ ||- u ];
      reltequ : [ Γ ||- t ≅ u | relt ]
  }.

  Notation "[ Γ ||-1U t ≅ u :::U| l ]" := (UTeEq Γ t u l) (at level 0).



  Definition RedRel@{i j} 
  := 
    context               -> 
    term                  -> 
   (term -> Type@{i})         -> 
   (term -> Type@{i})         -> 
   (term -> term -> Type@{i}) -> 
    Type@{j}. (*Type (n+3)*)

  Record LRPack (Γ : context) (A : term) (R : RedRel) := {
      relEq : term -> Type;
      relTerm : term -> Type;
      relEqTerm :  term -> term -> Type;
      relLR : R Γ A relEq relTerm relEqTerm
  }.

  Notation "[ Γ ||-0 A | R ]" := (LRPack Γ A R) (at level 0).

  Definition TyEqRelO {R : RedRel} (Γ : context) (A B : term) (L : [ Γ ||-0 A | R ]) : Type :=
      relEq _ _ _ L A.

  Notation "[ Γ ||-0 A ≅ B | R ]" := (TyEqRelO Γ A B R) (at level 0).

  Definition TeRelO {R : RedRel} (Γ : context) (t A : term) (L : [ Γ ||-0 A | R ]) : Type :=
      relTerm _ _ _ L A.

  Notation "[ Γ ||-0 t ::: A | R ]" := (TeRelO Γ t A R) (at level 0).

  Definition TeEqRelO {R : RedRel} (Γ : context) (t u A : term) (L : [ Γ ||-0 A | R ]) : Type :=
      relEqTerm _ _ _ L t u.

  Notation "[ Γ ||-0 t ≅ u ::: A | R ]" := (TeEqRelO Γ t u A R) (at level 0).

  (*Type (n+4)*)
  Record TyPiRel1 (Γ : context) (A : term) (R : RedRel) : Type := {
      F : term;
      G : term;
      D'_ {na} : [Γ |- A :⇒*: tProd na F G];
      conF : [Γ |- F];
      conG {na}: [Γ ,, vass na F |- G];
      _F {Δ} : [ |- Δ ] -> [Δ ||-0 F | R];
      _G {Δ a} (h : [ |- Δ ]) :
          [ Δ ||-0 a ::: F | _F h ] ->
          [ Δ ||-0  G{0 := a} | R ];
      G_ext 
          {Δ a b} 
          (h :  [ |- Δ ]) 
          (ha : [ Δ ||-0 a ::: F | _F h ])
          (hb : [ Δ ||-0 b ::: F | _F h ]) :
          [ Δ ||-0 a ≅ b ::: F | _F h] ->
          [ Δ ||-0 G{ 0 := a} ≅  G{0 := b} | _G h ha ];
  }.

  Notation "[ Γ ||-1Π A | R ]" := (TyPiRel1 Γ A R) (at level 0).

  Arguments  G {_} {_} {_} _.
  Arguments  F {_} {_} {_} _.
  Arguments _G {_} {_} {_} _ {_} {_}.
  Arguments _F {_} {_} {_} _ {_}.
  
  Check _F.

  Record TyPiEqRel1 {R : RedRel} (Γ : context) (A B : term) (H : [ Γ ||-1Π A | R ]) : Type := {
      F'                       : term;
      G'                       : term;
      D''_ {na}                : [Γ |- B :⇒*: tProd na F' G'];
      AeqB {na nb}             : [Γ |- tProd na H.(F) H.(G) ≅ tProd nb F' G' ];
      FeqF' {Δ} (h : [ |- Δ ]) : [Δ ||-0 H.(F) ≅ F' | H.(_F) h ];
      GeqG' {Δ a} (h : [ |- Δ ]) 
        (ha : [ Δ ||-0 a ::: H.(F) | H.(_F) h ]) :
        [Δ ||-0 H.(G){0 := a} ≅ G'{0 := a} | H.(_G) h ha ];
  }.

  Notation "[ Γ ||-1Π A ≅ B | H ]" := (TyPiEqRel1 Γ A B H) (at level 0).


  Record TePiRel1 {R : RedRel} (Γ : context) (t A : term)  (H : [ Γ ||-1Π A | R ]): Type := {
      f : term;
      redf {na} : [ Γ |- t :⇒*: f ::: tProd na H.(F) H.(G) ];
      fFun : isFun f;
      fEq {na} : [ Γ |- f ≅ f ::: tProd na H.(F) H.(G) ];
      appEq {Δ a b} (h : [ |- Δ ])
        (ha : [Δ ||-0 a ::: H.(F) | H.(_F) h ])
        (hb : [Δ ||-0 b ::: H.(F) | H.(_F) h ])
        (aeqb : [Δ ||-0 a ≅ b ::: H.(F) | H.(_F) h ])
        : [Δ ||-0 tApp f a ≅ tApp f b ::: H.(G){0 := a} | H.(_G) h ha ];
      appf {Δ a} (h : [ |- Δ ])
        (ha : [Δ ||-0 a ::: H.(F) | H.(_F) h ])
        : [Δ ||-0 tApp f a ::: H.(G){0 := a} | H.(_G) h ha ]
  }.

  Notation "[ Γ ||-1Π t ::: A | R ]" := (TePiRel1 Γ t A R) (at level 0).

  Record TePiEqRel1 {R : RedRel} (Γ : context) (t u A : term) (H : [ Γ ||-1Π A | R ]) : Type := {
      f' : term;
      g' : term;
      redf' {na} : [ Γ |- t :⇒*: f' ::: tProd na H.(F) H.(G) ];
      redg' {na} : [ Γ |- u :⇒*: g' ::: tProd na H.(F) H.(G) ];
      fFun' : isFun f';
      gFun' : isFun g';
      fEqg {na}: [ Γ |- f' ≅ g' ::: tProd na H.(F) H.(G) ];
      tRel : [ Γ ||-1Π t ::: A | H ];
      appEqfg {Δ a b} (h : [ |- Δ ]) 
        (ha : [Δ ||-0 a ::: H.(F) | H.(_F) h ])
        : [Δ ||-0 tApp f' a ≅ tApp g' b ::: H.(G){0 := a} | H.(_G) h ha ]
  }.

  Notation "[ Γ ||-1Π t ≅ u ::: A | H ]" := (TePiEqRel1 Γ t u A H) (at level 0).


  Print RedRel.
  Print TyPiRel1.

  Inductive LR@{i j} : RedRel@{i j} := 
    (*| LRU {Γ} (h : [ |- Γ]) (l' : TypeLevel) (l_ : l' << l) :
        LR Γ U 
        (fun B   => [ Γ ||-1U≅ B ])
        (fun t   => [ Γ ||-1U t     :::U| l_ ])
        (fun t u => [ Γ ||-1U t ≅ u :::U| l_ ])

    | LRne {Γ A} (neA : [ Γ ||-ne A ]) :
        LR Γ A
        (fun B   =>  [ Γ ||-ne A ≅ B       | neA])
        (fun t   =>  [ Γ ||-ne t     ::: A | neA])
        (fun t u =>  [ Γ ||-ne t ≅ u ::: A | neA])*)

    | LRPi {Γ A} {R} (h : LR = R) (H : [ Γ ||-1Π A | R ]) :
          LR Γ A
        (fun B   => [ Γ ||-1Π A ≅ B       | H ])
        (fun t   => [ Γ ||-1Π t     ::: A | H ])
        (fun t u => [ Γ ||-1Π t ≅ u ::: A | H ])
    
    (*| LRemn {Γ A l'} (l_ : l' << l) (H : [Γ ||- A]) :
        LR Γ A
        (fun B   => [ Γ ||- A ≅ B       | H ])
        (fun t   => [ Γ ||- t      :::A | H ]) 
        (fun t u => [ Γ ||- t ≅ u ::: A | H ])*)
    
  .




End LogRel.

