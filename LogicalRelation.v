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
    neK : neutral Γ K;
    KK : [ Γ |- K ≅ K ]
}.

Arguments K {_ _}.
Arguments D {_ _}.
Arguments neK {_ _}.
Arguments KK {_ _}.

Notation "[ Γ ||-ne A ]" := (neType Γ A)  (at level 0).

Record neTypeEq (Γ : context) (A B : term) (C : [ Γ ||-ne A ]) : Type := nee {
    M   : term;
    D'  : [ Γ |- B :⇒*: M];
    neM : neutral Γ M;
    KM  : [ Γ |- K C ≅ M]
}.

Arguments M {_ _ _ _}.
Arguments D' {_ _ _ _}.
Arguments neM {_ _ _ _}.
Arguments KM {_ _ _ _}.

Notation "[ Γ ||-ne A ≅ B | C ]" := (neTypeEq Γ A B C) (at level 0).

Record neTermNF (Γ : context) (k A : term) : Type := neTeNF {
    neknf : neutral Γ k;
    tkTy  : [ Γ |- k ::: A];
}.

Arguments neknf {_ _ _}.
Arguments tkTy {_ _ _}.

Notation "[ Γ ||-neNf t ::: A ]" := (neTermNF Γ t A) (at level 0).

Record neTerm (Γ : context) (t A : term) (C : [ Γ ||-ne A ]) : Type := neTe {
    k  : term;
    d  : [ Γ |- t :⇒*: k ::: K C];
    nf : [ Γ ||-neNf k ::: K C]
}.

Arguments k {_ _ _ _}.
Arguments d {_ _ _ _}.
Arguments nf {_ _ _ _}.

Notation "[ Γ ||-ne t ::: A | B ]" := (neTerm Γ t A B) (at level 0).

Record neTermEqNF (Γ : context) (k m A : term): Type := neTeEqNF {
    nekeq  : neutral Γ k;
    nekmeq : neutral Γ m;
    kEqm   : [ Γ |- k ≅ m ::: A]
}.

Arguments nekeq {_ _ _ _}.
Arguments nekmeq {_ _ _ _}.
Arguments kEqm {_ _ _ _}.

Notation "[ Γ ||-neNf t ≅ u ::: A ]" := (neTermEqNF Γ t u A) (at level 0).


Record neTermEq (Γ : context) (t u A : term) (C : [ Γ ||-ne A ]) : Type := neTeEq {
    k'     : term;
    m'     : term;
    d'     : [ Γ |- t :⇒*: k' ::: A ];
    d''    : [ Γ |- u :⇒*: m' ::: A ];
    kNFEqm : [ Γ ||-neNf k' ≅ m' ::: A ]
}.

Arguments k' {_ _ _ _ _}.
Arguments m' {_ _ _ _ _}.
Arguments d' {_ _ _ _ _}.
Arguments d'' {_ _ _ _ _}.
Arguments kNFEqm {_ _ _ _ _}.

Notation "[ Γ ||-ne t ≅ u ::: A | B ] " := (neTermEq Γ t u A B) (at level 0).

Inductive TypeLevel : Set :=
  | zero : TypeLevel
  | one  : TypeLevel.

Inductive TypeLevelLe : TypeLevel -> TypeLevel -> Set :=
    | Oi : TypeLevelLe zero one.

Notation "A << B" := (TypeLevelLe A B) (at level 0).

Definition elim (l l' : TypeLevel) :=
  match l with
    | zero => False
    | one => True
  end.

Definition elimm (l l' : TypeLevel) (h : l' << l) : elim l l' :=
  match h with
    | Oi => I
  end.

Record LogRelKit@{i j | i < j} := Kit {
  LRURel    : context         -> Type@{j};
  LRPiRel   : context -> term -> Type@{j};
  LRTyRel   : context -> term -> Type@{j};
  LREqTyRel : forall (Γ : context) (A B   : term), LRTyRel Γ A -> Type@{i};
  LRTeRel   : forall (Γ : context) (t A   : term), LRTyRel Γ A -> Type@{i};
  LREqTeRel : forall (Γ : context) (t u A : term), LRTyRel Γ A -> Type@{i}
}.

Notation "[ R | Γ ||-U ]"                := (LRURel    R Γ) (at level 0).
Notation "[ R | Γ ||-Π A ]"              := (LRPiRel   R Γ A) (at level 0).
Notation "[ R | Γ ||- A ]"               := (LRTyRel   R Γ A) (at level 0).
Notation "[ R | Γ ||- A ≅ B | C ]"       := (LREqTyRel R Γ A B C) (at level 0).
Notation "[ R | Γ ||- t ::: A | C ]"     := (LRTeRel   R Γ t A C) (at level 0).
Notation "[ R | Γ ||- t ≅ u ::: A | C ]" := (LREqTeRel R Γ t u A C) (at level 0).

Record URel {l} (rec : forall {l'} ,l' << l -> LogRelKit)
  (Γ : context) : Type := URelMk {
  l'  : TypeLevel;
  l_  : l' << l;
  wfc : [ |- Γ ]
}.

Arguments l' {_ _}.
Arguments l_ {_ _}.
Arguments wfc {_ _}.

Notation "[ R | Γ ||-1U ]" := (URel Γ R) (at level 0).

Record URelEq (Γ : context) (B : term) : Type := URelEqMk {
  Beq : B = U
}.

Arguments Beq {_ _}.

Notation "[ Γ ||-1U≅ B ]" := (URelEq Γ B) (at level 0).

Record UTerm {l l'} (rec : forall {l'} ,l' << l -> LogRelKit)
(Γ : context) (t : term) (l_ : l' << l) := UTermMk {
  A : term;
  dd : [ Γ |- t :⇒*: A ::: U ];
  typeA : isType A;
  tyrel : [ rec l_ | Γ ||- t] ;
}.

Arguments A {_ _ _ _}.
Arguments dd {_ _ _ _}.
Arguments typeA {_ _ _ _}.
Arguments tyrel {_ _ _ _}.

Notation "[ R | Γ ||-1U t :::U| l ]" := (UTerm R Γ t l) (at level 0).

(*Universe term equality*)
Record UTeEq {l l'} (rec : forall {l'} ,l' << l -> LogRelKit)
(Γ : context) (t u : term) (l_ : l' << l) := UTeEqMk {
    A'      : term;
    B'      : term;
    d_      : [ Γ |- t :⇒*: A' ::: U ];
    dd'      : [ Γ |- u :⇒*: B' ::: U ];
    typeA'  : isType A';
    typeB'  : isType B';
    AeqBU   : [ Γ |- A' ≅ B' ::: U ];
    relt    : [ rec l_ | Γ ||- t ];
    relu    : [ rec l_ | Γ ||- u ];
    reltequ : [ rec l_ | Γ ||- t ≅ u | relt ]
}.

Arguments A' {_ _ _ _ _}.
Arguments B' {_ _ _ _ _}.
Arguments d_ {_ _ _ _ _}.
Arguments dd' {_ _ _ _ _}.
Arguments typeA' {_ _ _ _ _}.
Arguments typeB' {_ _ _ _ _}.
Arguments AeqBU {_ _ _ _ _}.
Arguments relt {_ _ _ _ _}.
Arguments relu {_ _ _ _ _}.
Arguments reltequ {_ _ _ _ _}.

Notation "[ R | Γ ||-1U t ≅ u :::U| l ]" := (UTeEq R Γ t u l) (at level 0).

Definition RedRel@{i j | i < j} :=
  context               ->
  term                  ->
 (term -> Type@{i})         ->
 (term -> Type@{i})         ->
 (term -> term -> Type@{i}) ->
  Type@{j}.

(*Type (n+3)*)
Record LRPack@{i} (Γ : context) (A : term) := LRPackMk {
    relEq : term -> Type@{i};
    relTerm : term -> Type@{i};
    relEqTerm :  term -> term -> Type@{i};
}.

Arguments LRPackMk {_ _ _ _ _}.
Arguments relEq {_ _}.
Arguments relTerm {_ _}.
Arguments relEqTerm {_ _}.

Notation "[ Γ ||-0 A ]" := (LRPack Γ A) (at level 0).

Definition LRPackValid@{i j} {Γ : context} {A : term} (R : RedRel@{i j}) (P : LRPack@{i} Γ A) : Type@{j} :=
  R Γ A (relEq P) (relTerm P) (relEqTerm P).

Notation "[ R ||-1 H ]" := (LRPackValid R H) (at level 0).

Record LRValid (Γ : context ) (A : term) (R : RedRel) := LRValidMk {
  pack : [ Γ ||-0 A ];
  valid : [ R ||-1 pack ]
}.
Arguments LRValidMk {_ _ _}.
Arguments pack {_ _ _}.
Arguments valid {_ _ _}.

Definition TyEqRel1 (Γ : context) (A B : term) (L : LRPack Γ A) : Type :=
    relEq L B.

Notation "[ Γ ||-1 A ≅ B | R ]" := (TyEqRel1 Γ A B R) (at level 0).

Definition TeRel1 (Γ : context) (t A : term) (L : LRPack Γ A) : Type :=
    relTerm L t.

Notation "[ Γ ||-1 t ::: A | R ]" := (TeRel1 Γ t A R) (at level 0).

Definition TeEqRel1 (Γ : context) (t u A : term) (L : LRPack Γ A) : Type :=
    relEqTerm L t u.

Notation "[ Γ ||-1 t ≅ u ::: A | R ]" := (TeEqRel1 Γ t u A R) (at level 0).

(*Type (n+4)*)
Record TyPiRel0@{u0 u1}
  (Γ : context) (A : term)
  := TyPiRel0Mk {
    F : term;
    G : term;
    D'_ {na} : [Γ |- A :⇒*: tProd na F G];
    conF : [Γ |- F];
    conG {na}: [Γ ,, vass na F |- G];
    _F {Δ} : [ |- Δ ] -> LRPack@{u0} Δ F;
    _G {Δ a} (h : [ |- Δ ]) :
        [ Δ ||-1 a ::: F | _F h ] ->
        LRPack@{u0} Δ (G{0 := a});
    G_ext
        {Δ a b}
        (h :  [ |- Δ ])
        (ha : relTerm (_F h) a) :
        [ Δ ||-1 b ::: F | _F h ] ->
        [ Δ ||-1 a ≅ b ::: F | _F h ] ->
        [ Δ ||-1 (G{0 := a}) ≅ (G{0 := b}) | _G h ha ];
}.

Notation "[ Γ ||-0Π A ]" := (TyPiRel0 Γ A) (at level 0).

Arguments  conF {_ _}.
Arguments  conG {_ _}.
Arguments  G {_ _}.
Arguments  F {_ _}.
Arguments _F {_ _} _ {_}.
Arguments _G {_ _} _ {_ _}.
Arguments G_ext {_ _} _ {_ _ _}.

Record TyPiRel1 {Γ : context} {A : term} (R : RedRel) (_A : [ Γ ||-0Π A ]) :=
  TyPiRel1Mk {
    _F1 {Δ} (h : [ |- Δ ]) : LRPackValid R (_A.(_F) h);
    _G1 {Δ a} (h : [ |- Δ ]) (ha : [ Δ ||-1 a ::: _A.(F) | _A.(_F) h ]) : LRPackValid R (_A.(_G) h ha);
}.

Arguments _F1 {_ _ _ _} _ {_}.
Arguments _G1 {_ _ _ _} _ {_ _}.


Record TyPiEqRel1 (Γ : context) (A B : term)
(H : TyPiRel0 Γ A) := TyPiEqRel0Mk {
    F'                       : term;
    G'                       : term;
    D'' {na}                : [Γ |- B :⇒*: tProd na F' G'];
    AeqB {na nb}             : [Γ |- tProd na H.(F) H.(G) ≅ tProd nb F' G' ];
    FeqF' {Δ} (h : [ |- Δ ]) : [Δ ||-1 H.(F) ≅ F' | H.(_F) h ];
    GeqG' {Δ a} (h : [ |- Δ ])
      (ha : [ Δ ||-1 a ::: H.(F) | H.(_F) h ]) :
      [Δ ||-1 H.(G){0 := a} ≅ G'{0 := a} | H.(_G) h ha ];
}.

Arguments F' {_ _ _ }.
Arguments G' {_ _ _ }.
Arguments D'' {_ _ _ _}.
Arguments AeqB {_ _ _ _ _}.
Arguments FeqF' {_ _ _ _}.
Arguments GeqG' {_ _ _ _ _}.

Notation "[ Γ ||-1Π A ≅ B | H ]" := (TyPiEqRel1 Γ A B H) (at level 0).

Record TePiRel1 (Γ : context) (t A : term)
(H : TyPiRel0 Γ A) := TePiRel0Mk {
    f : term;
    redf {na} : [ Γ |- t :⇒*: f ::: tProd na H.(F) H.(G) ];
    fFun : isFun f;
    fEq {na} : [ Γ |- f ≅ f ::: tProd na H.(F) H.(G) ];
    appEq {Δ a b} (h : [ |- Δ ])
      (ha : [Δ ||-1 a ::: H.(F) | H.(_F) h ])
      (hb : [Δ ||-1 b ::: H.(F) | H.(_F) h ])
      (aeqb : [Δ ||-1 a ≅ b ::: H.(F) | H.(_F) h ])
      : [Δ ||-1 tApp f a ≅ tApp f b ::: H.(G){0 := a} | H.(_G) h ha ];
    appf {Δ a} (h : [ |- Δ ])
      (ha : [Δ ||-1 a ::: H.(F) | H.(_F) h ])
      : [Δ ||-1 tApp f a ::: H.(G){0 := a} | H.(_G) h ha ]
}.

Arguments f {_ _ _}.
Arguments redf {_ _ _ _}.
Arguments fFun {_ _ _}.
Arguments fEq {_ _ _ _}.
Arguments appEq {_ _ _ _ _ _}.
Arguments appf {_ _ _ _ _}.

Notation "[ Γ ||-1Π t ::: A | R ]" := (TePiRel1 Γ t A R) (at level 0).

Record TePiEqRel0 (Γ : context) (t u A : term)
(H : TyPiRel0 Γ A)  := TePiEqRel0Mk {
    f' : term;
    g' : term;
    redf' {na} : [ Γ |- t :⇒*: f' ::: tProd na H.(F) H.(G) ];
    redg' {na} : [ Γ |- u :⇒*: g' ::: tProd na H.(F) H.(G) ];
    fFun' : isFun f';
    gFun' : isFun g';
    fEqg {na}: [ Γ |- f' ≅ g' ::: tProd na H.(F) H.(G) ];
    tRel : [ Γ ||-1Π t ::: A | H ];
    appEqfg {Δ a} (h : [ |- Δ ])
      (ha : [Δ ||-1 a ::: H.(F) | H.(_F) h ])
      : [Δ ||-1 tApp f' a ≅ tApp g' a ::: H.(G){0 := a} | H.(_G) h ha ]
}.

Arguments f' {_ _ _ _}.
Arguments g' {_ _ _ _}.
Arguments redf' {_ _ _ _ _}.
Arguments redg' {_ _ _ _ _}.
Arguments fFun' {_ _ _ _}.
Arguments gFun' {_ _ _ _}.
Arguments fEqg {_ _ _ _ _}.
Arguments tRel {_ _ _ _}.
Arguments appEqfg {_ _ _ _ _ _}.

Notation "[ Γ ||-1Π t ≅ u ::: A | H ]" := (TePiEqRel0 Γ t u A H) (at level 0).

Inductive LR {l : TypeLevel} (rec : forall l' ,l' << l -> LogRelKit)
  : RedRel :=
  | LRU {Γ} (h : [ |- Γ]) (l' : TypeLevel) (l_ : l' << l) :
      LR rec Γ U
      (fun B   => [ Γ ||-1U≅ B ])
      (fun t   => [ rec | Γ ||-1U t     :::U| l_ ])
      (fun t u => [ rec | Γ ||-1U t ≅ u :::U| l_ ])
  | LRne {Γ A} (neA : [ Γ ||-ne A ]) :
      LR rec Γ A
      (fun B   =>  [ Γ ||-ne A ≅ B       | neA])
      (fun t   =>  [ Γ ||-ne t     ::: A | neA])
      (fun t u =>  [ Γ ||-ne t ≅ u ::: A | neA])
  | LRPi {Γ A} (H0 : [ Γ ||-0Π A ]) (H1 : TyPiRel1 (LR rec) H0) :
    LR rec Γ A
      (fun B   => [ Γ ||-1Π A ≅ B       | H0 ])
      (fun t   => [ Γ ||-1Π t     ::: A | H0 ])
      (fun t u => [ Γ ||-1Π t ≅ u ::: A | H0 ])
  | LRemb {Γ A l'} (l_ : l' << l) (H : [ rec _ l_ | Γ ||- A]) :
      LR rec Γ A
      (fun B   => [ _ | Γ ||- A ≅ B       | H ])
      (fun t   => [ _ | Γ ||- t     ::: A | H ])
      (fun t u => [ _ | Γ ||- t ≅ u ::: A | H ])
      .

Definition Rel1Ty
{l : TypeLevel} (R : forall l' ,l' << l -> LogRelKit)
(Γ : context) (A : term) :=
  LRValid Γ A (LR R).

Notation "[ R | Γ ||-1 A ]" := (Rel1Ty R Γ A) (at level 0).

Definition Rel1TyEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (A B : term) (H : [R | Γ ||-1 A]) :=
  [ Γ ||-1 A ≅ B | H.(pack) ].

Notation "[ Γ ||-1 A ≅ B | H ]" := (Rel1TyEq Γ A B H) (at level 0).

Definition Rel1Te   {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t A : term) (H : Rel1Ty R Γ A ) :=
  [ Γ ||-1 t ::: A | H.(pack) ].

Notation "[ Γ ||-1 t ::: A | H ]" := (Rel1Te Γ t A H) (at level 0).

Definition Rel1TeEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t u A : term) (H : Rel1Ty R Γ A) :=
  [ Γ ||-1 t ≅ u ::: A | H.(pack) ].

Notation "[ Γ ||-1 t ≅ u ::: A | H ]" := (Rel1TeEq Γ t u A H) (at level 0).

Definition rec0 (l' : TypeLevel) (h : l' << zero) : LogRelKit :=
  match elimm zero l' h with
  end.
Definition LR0 := LR rec0.
(*Definition kit1@{u u0 u1} :=
  Kit@{u1 u}
  (URel@{u0 u1} rec0@{u0 u1})
  (fun Γ A => TyPiRel1@{u1 u} Γ A LR0@{u1 u u0})
  (Rel1Ty@{u1 u u0} rec0@{u0 u1})
  Rel1TyEq@{u0 u1 u}
  Rel1Te@{u0 u1 u}
  Rel1TeEq@{u0 u1 u}.
*)

Definition kit0 :=
  Kit
  (URel rec0)
  (fun Γ A => TyPiRel0 Γ A)
  (Rel1Ty rec0)
  Rel1TyEq
  Rel1Te
  Rel1TeEq.

Definition LogRelRec (l l' : TypeLevel) (h : l' << l) : LogRelKit :=
  match l as t return ((l') << (t) -> LogRelKit) with
    | zero => fun h0 : (l') << (zero) => rec0 l' h0
    | one => fun _ : (l') << (one) => kit0
  end h.


Definition rec1 :=
  LogRelRec one .

Definition LR1 := LR rec1.

Definition LRL (l : TypeLevel) :=
  match l with
    | zero => LR0
    | one => LR1
  end.

  (*TODO minimiser univers*)
Definition kit (l : TypeLevel) : LogRelKit :=
  let rec := LogRelRec l in
  Kit
    (URel rec)
    (fun Γ A => [ Γ ||-0Π A ])
    (Rel1Ty rec)
    Rel1TyEq
    Rel1Te
    Rel1TeEq.

Definition recl (l : TypeLevel) :=
  match l with
    |zero => rec0
    |one => rec1
  end.

Record Ur (Γ : context) (l : TypeLevel) : Type := UrMk {
  l'' : TypeLevel;
  l__ : l'' << l;
  con :  [ |- Γ ]
}.

Arguments l'' {_ _}.
Arguments l__ {_ _}.
Arguments con {_ _}.

Definition PiUr (Γ : context) (l : TypeLevel) (A : term) : Type :=
  [ kit l | Γ ||-Π A].
Definition TyUr (Γ : context) (l : TypeLevel) (A : term) : Type :=
  [ kit l | Γ ||- A].

Definition TyEqUr (Γ : context) (l : TypeLevel) (A B: term) (H : TyUr Γ l A): Type :=
  [ kit l | Γ ||- A ≅ B | H].
Definition TeUr (Γ : context) (l : TypeLevel) (t A : term) (H : TyUr Γ l A) : Type :=
  [ kit l | Γ ||- t ::: A | H].
Definition TeEqUr (Γ : context) (l : TypeLevel) (t u A : term) (H : TyUr Γ l A) : Type :=
  [ kit l | Γ ||- t ≅ u ::: A | H].

Notation "[ Γ ||-< l |U]" := (Ur Γ l) (at level 0).
Notation "[ Γ ||-< l |Π A ]" := (PiUr Γ l A) (at level 0).
Notation "[ Γ ||-< l | A ]" := (TyUr Γ l A) (at level 0).
Notation "[ Γ ||-< l | A ≅ B | H ]" := (TyEqUr Γ l A B H) (at level 0).
Notation "[ Γ ||-< l | t ::: A | H ]" := (TeUr Γ l t A H) (at level 0).
Notation "[ Γ ||-< l | t ≅ u ::: A | H ]" := (TeEqUr Γ l t u A H) (at level 0).
