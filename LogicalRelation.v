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

Record LogRelKit@{i j | i<j } := Kit {
  LRURel    : context         -> Type@{j};
  LRPiRel   : context -> term -> Type@{j};
  LRTyRel   : context -> term -> Type@{j};
  LREqTyRel : forall (Γ : context) (A B   : term), LRTyRel Γ A -> Type@{i};
  LRTeRel   : forall (Γ : context) (t A   : term), LRTyRel Γ A -> Type@{i};
  LREqTeRel : forall (Γ : context) (t u A : term), LRTyRel Γ A -> Type@{i}
}.

(*Ideas:
  - add useless parameters to fill in monomorphic assumptions
  hacky + bloating
  - hope coq gets friendlier 
  - index LR by l and rec ?
  - ?????????*)
(*Module Type Param.

  Parameter l : TypeLevel.
  Parameter rec@{u u0 u1 u1 e3 i3 eq0 ast94 ba0 snoc def
  | u < u0, u1 < u , u0 < u2,
    e3 <= u0, e3 <= u2, i3 <= eq0,
    i3 <= ast94, i3 <= u0, i3 <= u2,
    ba0 <= eq0, ba0 <= ast94, 
    ba0 <= snoc, ba0 <= u0, ba0 <= u2,
    def <= eq0, def <= ast94, def <= u0, def <= u2,
    ast94 <= eq0, ast94 <= snoc, ast94 <= u0, ast94 <= u2
    }
  : forall {l'} ,l' << l -> LogRelKit@{u u0}.
End Param.

Module LogRel (P : Param).
Import P.
(l : TypeLevel) (rec : forall {l'} ,l' << l -> LogRelKit)

*)

Notation "[ R | Γ ||-U ]"                := (LRURel    R Γ) (at level 0).
Notation "[ R | Γ ||-Π A ]"              := (LRPiRel   R Γ A) (at level 0).
Notation "[ R | Γ ||- A ]"               := (LRTyRel   R Γ A) (at level 0).
Notation "[ R | Γ ||- A ≅ B | C ]"       := (LREqTyRel R Γ A B C) (at level 0).
Notation "[ R | Γ ||- t ::: A | C ]"     := (LRTeRel   R Γ t A C) (at level 0).
Notation "[ R | Γ ||- t ≅ u ::: A | C ]" := (LREqTeRel R Γ t u A C) (at level 0).

Record URel {l} (rec : forall {l'} ,l' << l -> LogRelKit)(Γ : context) 
: Type := URelMk{ 
  l'  : TypeLevel;
  l_  : l' << l;
  wfc : [ |- Γ ]
}.

Notation "[ R | Γ ||-1U ]" := (URel Γ R) (at level 0).

Record URelEq (Γ : context) (B : term) : Type := URelEqMk{ 
  Beq : B = U
}.
  
Notation "[ Γ ||-1U≅ B ]" := (URelEq Γ B) (at level 0).

Record UTerm {l l'} (rec : forall {l'} ,l' << l -> LogRelKit) 
(Γ : context) (t : term) (l_ : l' << l) := {
  A : term;
  dd : [ Γ |- t :⇒*: A ::: U ];
  typeA : isType A;
  tyrel : [ rec l_ | Γ ||- t] ;
}.

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
Notation "[ R | Γ ||-1U t ≅ u :::U| l ]" := (UTeEq R Γ t u l) (at level 0).

Definition RedRel@{i j} 
:= 
  context               -> 
  term                  -> 
 (term -> Type@{i})         -> 
 (term -> Type@{i})         -> 
 (term -> term -> Type@{i}) -> 
  Type@{j}.
  
(*Type (n+3)*)
Record LRPack@{i j | i < j} (Γ : context) (A : term) (R : RedRel@{i j}) := LRPackMk {
    relEq : term -> Type@{i};
    relTerm : term -> Type@{i};
    relEqTerm :  term -> term -> Type@{i};
    relLR : R Γ A relEq relTerm relEqTerm
}.

Arguments relEq {_} {_} {_}.
Arguments relTerm {_} {_} {_}.
Arguments relEqTerm {_} {_} {_}.
Arguments relLR {_} {_} {_}.
 
Notation "[ Γ ||-0 A | R ]" := (LRPack Γ A R) (at level 0).

Definition TyEqRelO@{i j} {R : RedRel@{i j}} (Γ : context) (A B : term) (L : LRPack@{i j} Γ A R ) : Type@{i} :=
    relEq L B.

Notation "[ Γ ||-0 A ≅ B | R ]" := (TyEqRelO Γ A B R) (at level 0).

Definition TeRelO@{i j} {R : RedRel@{i j}} (Γ : context) (t A : term) (L : LRPack@{i j} Γ A R ) : Type@{i} :=
    relTerm L t.

Notation "[ Γ ||-0 t ::: A | R ]" := (TeRelO Γ t A R) (at level 0).

Definition TeEqRelO@{i j} {R : RedRel@{ i j}} (Γ : context) (t u A : term) (L : LRPack@{i j} Γ A R) : Type@{i} :=
    relEqTerm L t u.

Notation "[ Γ ||-0 t ≅ u ::: A | R ]" := (TeEqRelO Γ t u A R) (at level 0).

(*Type (n+4)*)
Record TyPiRel1@{u0 u1}
  (Γ : context) (A : term) (R : RedRel@{u0 u1}) := {
    F : term;
    G : term;
    D'_ {na} : [Γ |- A :⇒*: tProd na F G];
    conF : [Γ |- F];
    conG {na}: [Γ ,, vass na F |- G];
    _F {Δ} : [ |- Δ ] -> LRPack@{u0 u1} Δ F R;
    _G {Δ a} (h : [ |- Δ ]) :
        TeRelO@{u0 u1} Δ a F (_F h) ->
        LRPack@{u0 u1} Δ (G{0 := a}) R;
    G_ext 
        {Δ a b} 
        (h :  [ |- Δ ]) 
        (ha : TeRelO@{u0 u1} Δ a F (_F h)) :
        TeRelO@{u0 u1} Δ b F (_F h) ->
        TeEqRelO@{u0 u1} Δ a b F (_F h) ->
        TyEqRelO@{u0 u1} Δ (G{ 0 := a}) (G{0 := b}) (_G h ha);
}.

Notation "[ Γ ||-1Π A | R ]" := (TyPiRel1 Γ A R) (at level 0).

Arguments  conF {_} {_} {_} _.
Arguments  conG {_} {_} {_} _.
Arguments  G {_} {_} {_} _.
Arguments  F {_} {_} {_} _.
Arguments _F {_} {_} {_} _ {_}.
Arguments _G {_} {_} {_} _ {_} {_}.

Record TyPiEqRel1@{i j} {R : RedRel@{i j}} (Γ : context) (A B : term) 
(H : TyPiRel1@{i j} Γ A R) := TyPiEqRel1Mk {
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

Record TePiRel1@{i j} 
{R : RedRel@{i j}} (Γ : context) (t A : term)  
(H : TyPiRel1@{i j} Γ A R) := {
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

Record TePiEqRel1@{i j} {R : RedRel@{i j}} (Γ : context) (t u A : term) 
(H : TyPiRel1@{i j} Γ A R)  := {
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

(*Inductive LR@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} : RedRel@{u0 u2} :=
  |LRU : forall (Γ : context) (_ : wfContext Γ) (l' : TypeLevel)
          (l_ : TypeLevelLe l' l),
        LR Γ U
          (fun B : term => URelEq Γ B)
          (fun t : term => @UTerm@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} l' Γ t l_)
          (fun t u : term => @UTeEq@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} l' Γ t u l_)
| LRne : forall (Γ : context) (A : term) (neA : neType Γ A),
         LR Γ A
           (fun B : term => neTypeEq Γ A B neA)
           (fun t : term => neTerm Γ t A neA)
           (fun t u : term => neTermEq Γ t u A neA)
| LRPi : forall (Γ : context) (A : term)
           (H : TyPiRel1@{u0 u2 e3 i3 eq0 ast94 ba0 snoc def} Γ A LR ),
         LR Γ A
           (fun B : term =>
            @TyPiEqRel1@{u0 u2 e3 i3 eq0 ast94 ba0 snoc def} LR Γ A B H)
           (fun t : term =>
            @TePiRel1@{u0 u2 e3 i3 eq0 ast94 ba0 snoc def} LR Γ t A H)
           (fun t u : term =>
            @TePiEqRel1@{u0 u2 e3 i3 eq0 ast94 ba0 snoc def} LR Γ t u A H)
| LRemn : forall (Γ : context) (A : term) (l' : TypeLevel)
            (l_ : TypeLevelLe l' l)
            (H : LRTyRel (@rec@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} l' l_) Γ A),
          LR Γ A
            (fun B : term => LREqTyRel (@rec@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} l' l_) Γ A B H)
            (fun t : term => LRTeRel (@rec@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} l' l_) Γ t A H)
            (fun t u : term =>
             LREqTeRel (@rec@{u u0 u1 u2 e3 i3 eq0 ast94 ba0 snoc def} l' l_) Γ t u A H).*)
#[bypass_check(positivity)]
Inductive LR@{u u0 u1} {l : TypeLevel} (rec : forall l' ,l' << l -> LogRelKit@{u u0}) 
  : RedRel@{u0 u1} := 
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
  | LRPi {Γ A} (H : [ Γ ||-1Π A | LR rec ])  :
    LR rec Γ A 
      (fun B   => [ Γ ||-1Π A ≅ B       | H ])
      (fun t   => [ Γ ||-1Π t     ::: A | H ]) 
      (fun t u => [ Γ ||-1Π t ≅ u ::: A | H ]) 
  | LRemb {Γ A l'} (l_ : l' << l) (H : [ rec _ l_ | Γ ||- A]) :
      LR rec Γ A
      (fun B   => [ rec _ l_ | Γ ||- A ≅ B       | H ])
      (fun t   => [ rec _ l_ | Γ ||- t     ::: A | H ]) 
      (fun t u => [ rec _ l_ | Γ ||- t ≅ u ::: A | H ])
      .






Definition Rel1Ty 
{l : TypeLevel} (R : forall l' ,l' << l -> LogRelKit)
(Γ : context) (A : term) :=
  [ Γ ||-0 A | LR R ].

Notation "[ R | Γ ||-1 A ]" := (Rel1Ty R Γ A) (at level 0). 

Definition Rel1TyEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (A B : term) (H : Rel1Ty R Γ A) :=
  [ Γ ||-0 A ≅ B | H ].

Notation "[ Γ ||-1 A ≅ B | H ]" := (Rel1TyEq Γ A B H) (at level 0).

Definition Rel1Te   {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t A : term) (H : Rel1Ty R Γ A ) :=
  [ Γ ||-0 t ::: A | H ].

Notation "[ Γ ||-1 t ::: A | H ]" := (Rel1Te Γ t A H) (at level 0).

Definition Rel1TeEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t u A : term) (H : Rel1Ty R Γ A) :=
  [ Γ ||-0 t ≅ u ::: A | H ].

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

Definition kit1@{u u0 u1} := 
  Kit@{u1 u}
  (URel@{u0 u1} rec0@{u0 u1})
  (fun Γ A => TyPiRel1@{u1 u} Γ A LR0@{u0 u1 u}) 
  (Rel1Ty@{u1 u u0} rec0@{u0 u1})
  Rel1TyEq@{u0 u1 u}
  Rel1Te@{u0 u1 u}
  Rel1TeEq@{u0 u1 u}.



Definition LogRelRec (l l' : TypeLevel) (h : l' << l) : LogRelKit :=
  match l with
    | zero => fun h0 => rec0 l' h0
    | one => fun _  => kit1
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
Definition kit@{u u0 u1 u2 u3 u4 u5 u6 u7 u8}
 (l : TypeLevel)  :=
  let rec := LogRelRec@{u8 u6 u} l in 
  Kit@{u6 u0} 
    (URel@{u8 u6} rec) 
    (fun Γ A => [ Γ ||-1Π A | LRL@{u3 u1 u2 u4 u5} l ]) 
    (Rel1Ty@{u6 u7 u8} rec) 
    Rel1TyEq@{u8 u6 u7}
    Rel1Te@{u8 u6 u7}
    Rel1TeEq@{u8 u6 u7}.

Record Ur (Γ : context) (l : TypeLevel) : Type := {
  l'' : TypeLevel;
  l__ : l'' << l;
  con :  [ |- Γ ]
}.

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
