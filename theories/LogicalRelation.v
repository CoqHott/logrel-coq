From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import MLTTTyping Untyped.

Set Primitive Projections.
Set Universe Polymorphism.

(*Modules are used as a hackish solution to go around uniqueness of field names for records*)

Module neType.

  Record neType {Γ : context} {A : term} : Type := {
    ty : term;
    red :> [ Γ |- A :⇒*: ty];
    ne :> whne Γ ty;
    refl : [ Γ |- ty ≅ ty]
  }.

  Arguments neType : clear implicits.

End neType.

Export neType(neType, Build_neType).
Notation "[ Γ ||-ne A ]" := (neType Γ A)  (at level 0).

Module neTypeEq.

  Record neTypeEq {Γ : context} {A B : term} {C : [ Γ ||-ne A ]} : Type := {
      ty   : term;
      red  :> [ Γ |- B :⇒*: ty];
      ne : whne Γ ty;
      eq  : [ Γ |- C.(neType.ty) ≅ ty]
  }.

  Arguments neTypeEq : clear implicits.

End neTypeEq.

Export neTypeEq(neTypeEq,Build_neTypeEq).
Notation "[ Γ ||-ne A ≅ B | C ]" := (neTypeEq Γ A B C) (at level 0).

Module neTerm.

  Record neTermNf {Γ : context} {k A : term} : Type := {
      ne : whne Γ k;
      ty  : [ Γ |- k ::: A];
  }.

  Arguments neTermNf : clear implicits.

  Record neTerm {Γ : context} {t A : term} {C : [ Γ ||-ne A ]} : Type := {
      term  : term;
      red  :> [ Γ |- t :⇒*: term ::: C.(neType.ty)];
      ne' : neTermNf Γ term C.(neType.ty)
  }.

  Arguments neTerm : clear implicits.

End neTerm.

Export neTerm(neTermNf,Build_neTermNf, neTerm, Build_neTerm).

Notation "[ Γ ||-neNf t ::: A ]" := (neTermNf Γ t A) (at level 0).
Notation "[ Γ ||-ne t ::: A | B ]" := (neTerm Γ t A B) (at level 0).

Module neTermEq.

  Record neTermEqNF {Γ : context} {k m A : term} : Type := {
      whneL : whne Γ k;
      whneR : whne Γ m;
      eq : [ Γ |- k ≅ m ::: A]
  }.

  Arguments neTermEqNF : clear implicits.

  Record neTermEq {Γ : context} {t u A : term} {C : [ Γ ||-ne A ]} : Type := {
      termL     : term;
      termR     : term;
      redL      : [ Γ |- t :⇒*: termL ::: A ];
      redR      : [ Γ |- u :⇒*: termR ::: A ];
      eq' :> neTermEqNF Γ termL termR A
  }.

  Arguments neTermEq : clear implicits.

End neTermEq.

Export neTermEq(neTermEqNF, Build_neTermEqNF, neTermEq, Build_neTermEq).
Notation "[ Γ ||-neNf t ≅ u ::: A ]" := (neTermEqNF Γ t u A) (at level 0).
Notation "[ Γ ||-ne t ≅ u ::: A | B ] " := (neTermEq Γ t u A B) (at level 0).

Inductive TypeLevel : Set :=
  | zero : TypeLevel
  | one  : TypeLevel.

Inductive TypeLevelLt : TypeLevel -> TypeLevel -> Set :=
    | Oi : TypeLevelLt zero one.

Notation "A << B" := (TypeLevelLt A B) (at level 0).

Definition LtSubst {l} (h : l = one) : zero << l.
Proof.
  rewrite h.
  constructor.
Qed.

Definition elim (l l' : TypeLevel) :=
  match l with
    | zero => False
    | one => True
  end.

Definition elimm (l l' : TypeLevel) (h : l' << l) : elim l l' :=
  match h with
    | Oi => I
  end.

Module LRKit.

  Record LogRelKit@{i j | i < j} := {
    URel    : context         -> Type@{j};
    PiRel   : context -> term -> Type@{j};
    TyRel   : context -> term -> Type@{j};
    EqTyRel : forall (Γ : context) (A B   : term), TyRel Γ A -> Type@{i};
    TeRel   : forall (Γ : context) (t A   : term), TyRel Γ A -> Type@{i};
    EqTeRel : forall (Γ : context) (t u A : term), TyRel Γ A -> Type@{i}
  }.

End LRKit.

Export LRKit(LogRelKit,Build_LogRelKit).

Notation "[ R | Γ ||-U ]"                := (R.(LRKit.URel) Γ) (at level 0).
Notation "[ R | Γ ||-Π A ]"              := (R.(LRKit.PiRel) Γ A) (at level 0).
Notation "[ R | Γ ||- A ]"               := (R.(LRKit.TyRel) Γ A) (at level 0).
Notation "[ R | Γ ||- A ≅ B | C ]"       := (R.(LRKit.EqTyRel) Γ A B C) (at level 0).
Notation "[ R | Γ ||- t ::: A | C ]"     := (R.(LRKit.TeRel) Γ t A C) (at level 0).
Notation "[ R | Γ ||- t ≅ u ::: A | C ]" := (R.(LRKit.EqTeRel) Γ t u A C) (at level 0).

Module URel.

  Record URel {l}
    {Γ : context} : Type := {
    level  : TypeLevel;
    lt  : level << l;
    wfCtx : [ |- Γ ]
  }.

  Arguments URel {_}.

  Record URelEq {Γ : context} {B : term} : Type := {
    eq : B = U
  }.

  Arguments URelEq : clear implicits.

End URel.

Export URel(URel,Build_URel,URelEq,Build_URelEq).

Notation "[ Γ ||-U ]" := (URel Γ) (at level 0).
Notation "[ Γ ||-U≅ B ]" := (URelEq Γ B) (at level 0).

Module UTerm.

  Record UTerm {l l'} {rec : forall {l'}, l' << l -> LogRelKit}
  {Γ : context} {t : term} {l_ : l' << l} := {
    term : term;
    red : [ Γ |- t :⇒*: term ::: U ];
    type : isType Γ term;
    rel : [rec l_ | Γ ||- t ] ;
  }.

  Arguments UTerm {_ _}.

  (*Universe term equality*)
  Record UTermEq {l l'} {rec : forall {l'}, l' << l -> LogRelKit}
  {Γ : context} {t u : PCUICAst.term} {l_ : l' << l} := {
    termL     : PCUICAst.term;
    termR     : PCUICAst.term;
    redL      : [ Γ |- t :⇒*: termL ::: U ];
    redR      : [ Γ |- u :⇒*: termR ::: U ];
    tyL  : isType Γ termL;
    tyR  : isType Γ termR;
    eq   : [ Γ |- termL ≅ termR ::: U ];
    relL    : [ rec l_ | Γ ||- t ] ;
    relR    : [ rec l_ | Γ ||- u ] ;
    relEq : [ rec l_ | Γ ||- t ≅ u | relL ] ;
  }.

  Arguments UTermEq {_ _}.

End UTerm.

Export UTerm(UTerm,Build_UTerm,UTermEq,Build_UTermEq).
Notation "[ R | Γ ||-U t :::U | l ]" := (UTerm R Γ t l) (at level 0).
Notation "[ R | Γ ||-U t ≅ u :::U | l ]" := (UTermEq R Γ t u l) (at level 0).

Definition RedRel@{i j | i < j} :=
  context               ->
  term                  ->
 (term -> Type@{i})         ->
 (term -> Type@{i})         ->
 (term -> term -> Type@{i}) ->
  Type@{j}.

Module LRPack.

  (*Type (n+3)*)
  Record LRPack@{i} {Γ : context} {A : term} := {
      eq : term -> Type@{i};
      term : term -> Type@{i};
      eqTerm :  PCUICAst.term -> PCUICAst.term -> Type@{i};
  }.

  Arguments LRPack : clear implicits.

End LRPack.

Export LRPack(LRPack,Build_LRPack).

Notation "[ Γ ||-p A ≅ B | R ]" := (@LRPack.eq Γ A R B) (at level 0).
Notation "[ Γ ||-p t ::: A | R ]" := (@LRPack.term Γ A R t ) (at level 0).
Notation "[ Γ ||-p t ≅ u ::: A | R ]" := (@LRPack.eqTerm Γ A R t u) (at level 0).

Definition LRPackValid@{i j} {Γ : context} {A : term} (R : RedRel@{i j}) (P : LRPack@{i} Γ A) : Type@{j} :=
  R Γ A P.(LRPack.eq) P.(LRPack.term) P.(LRPack.eqTerm).

Module LRValid.

  Record LRValid {Γ : context} {A : term} {R : RedRel} := {
    eq : term -> Type;
    term : term -> Type;
    eqTerm :  PCUICAst.term -> PCUICAst.term -> Type;
    valid : LRPackValid R (@Build_LRPack Γ A eq term eqTerm)
  }.

  Arguments LRValid : clear implicits.
  Arguments Build_LRValid {_ _ _ _ _ _}.

End LRValid.

Export LRValid(LRValid,Build_LRValid).

Coercion pack {Γ A R} (H : LRValid Γ A R) : LRPack Γ A :=
  @Build_LRPack Γ A H.(LRValid.eq) H.(LRValid.term) H.(LRValid.eqTerm).

Module TyPiRel.

  (*Type (n+4)*)
  Record TyPiRel@{i}
    {Γ : context} {A : term}
    := {
      na : aname ;
      dom : term ;
      cod : term ;
      redPi := tProd na dom cod ;
      red : [Γ |- A :⇒*: redPi];
      domTy : [Γ |- dom];
      codTy : [Γ ,, vass na dom |- cod];
      domRel {Δ} : [ |- Δ ] -> LRPack@{i} Δ dom;
      codRel {Δ a} (h : [ |- Δ ]) :
          [ Δ ||-p a ::: dom | domRel h ] ->
          LRPack@{i} Δ (cod{0 := a});
      codExt
        {Δ a b}
        (h :  [ |- Δ ])
        (ha : (domRel h).(LRPack.term) a) :
        [ Δ ||-p b ::: dom | domRel h ] ->
        [ Δ ||-p a ≅ b ::: dom | domRel h ] ->
        [ Δ ||-p (cod{0 := a}) ≅ (cod{0 := b}) | codRel h ha ];
  }.

  Arguments TyPiRel : clear implicits.

  Record TyPiRelValid {Γ : context} {A : term} {R : RedRel} {_A : TyPiRel Γ A} :=
  {
    domValid {Δ} (h : [ |- Δ ]) : LRPackValid R (_A.(domRel) h);
    codValid {Δ a} (h : [ |- Δ ]) (ha : [ Δ ||-p a ::: _A.(dom) | _A.(domRel) h ])
      : LRPackValid R (_A.(codRel) h ha);
  }.

  Arguments TyPiRelValid {_ _}.

End TyPiRel.

Export TyPiRel(TyPiRel,Build_TyPiRel,TyPiRelValid,Build_TyPiRelValid).
Notation "[ Γ ||-Πr A ]" := (TyPiRel Γ A) (at level 0).

Module TyPiEqRel.

  Record TyPiEqRel {Γ : context} {A B : term} {H : TyPiRel Γ A} := {
    na                        : aname ;
    dom                       : term;
    cod                       : term;
    redPi                     := tProd na dom cod ;
    red                       : [Γ |- B :⇒*: redPi];
    eq                        : [Γ |- H.(TyPiRel.redPi) ≅ redPi ];
    domRel {Δ} (h : [ |- Δ ]) : [Δ ||-p H.(TyPiRel.dom) ≅ dom | H.(TyPiRel.domRel) h ];
    codRel {Δ a} (h : [ |- Δ ])
      (ha : [ Δ ||-p a ::: H.(TyPiRel.dom) | H.(TyPiRel.domRel) h ]) :
      [Δ ||-p H.(TyPiRel.cod){0 := a} ≅ cod{0 := a} | H.(TyPiRel.codRel) h ha ];
  }.

  Arguments TyPiEqRel : clear implicits.

End TyPiEqRel.

Export TyPiEqRel(TyPiEqRel,Build_TyPiEqRel).
Notation "[ Γ ||-Π A ≅ B | H ]" := (TyPiEqRel Γ A B H) (at level 0).

Module TePiRel.

  Record TePiRel {Γ : context} {t A : term} {H : TyPiRel Γ A} := {
    nf : term;
    red : [ Γ |- t :⇒*: nf ::: H.(TyPiRel.redPi) ];
    nfFun : isFun Γ nf;
    refl : [ Γ |- nf ≅ nf ::: H.(TyPiRel.redPi) ];
    appRel {Δ a} (h : [ |- Δ ])
      (ha : [Δ ||-p a ::: H.(TyPiRel.dom) | H.(TyPiRel.domRel) h ])
      : [Δ ||-p tApp nf a ::: H.(TyPiRel.cod){0 := a} | H.(TyPiRel.codRel) h ha ] ;
    eqRel {Δ a b} (h : [ |- Δ ])
      (ha : [Δ ||-p a ::: H.(TyPiRel.dom) | H.(TyPiRel.domRel) h ])
      (hb : [Δ ||-p b ::: H.(TyPiRel.dom) | H.(TyPiRel.domRel) h ])
      (eq : [Δ ||-p a ≅ b ::: H.(TyPiRel.dom) | H.(TyPiRel.domRel) h ])
      : [Δ ||-p tApp nf a ≅ tApp nf b ::: H.(TyPiRel.cod){0 := a} | H.(TyPiRel.codRel) h ha ];
  }.

  Arguments TePiRel : clear implicits.

End TePiRel.

Export TePiRel(TePiRel,Build_TePiRel).
Notation "[ Γ ||-Π t ::: A | R ]" := (TePiRel Γ t A R) (at level 0).

Module TePiEqRel.

  Record TePiEqRel {Γ : context} {t u A : term} {H : TyPiRel Γ A}  := {
      nfL : term;
      nfR : term;
      redL : [ Γ |- t :⇒*: nfL ::: H.(TyPiRel.redPi) ];
      redR : [ Γ |- u :⇒*: nfR ::: H.(TyPiRel.redPi) ];
      nfFunL : isFun Γ nfL;
      nfFunR : isFun Γ nfR;
      eq : [ Γ |- nfL ≅ nfR ::: H.(TyPiRel.redPi) ];
      rel : [ Γ ||-Π t ::: A | H ];
      eqApp {Δ a} (h : [ |- Δ ])
        (ha : [Δ ||-p a ::: H.(TyPiRel.dom) | H.(TyPiRel.domRel) h ])
        : [Δ ||-p tApp nfL a ≅ tApp nfR a ::: H.(TyPiRel.cod){0 := a} | H.(TyPiRel.codRel) h ha ]
  }.

  Arguments TePiEqRel : clear implicits.

End TePiEqRel.

Export TePiEqRel(TePiEqRel,Build_TePiEqRel).

Notation "[ Γ ||-Π t ≅ u ::: A | H ]" := (TePiEqRel Γ t u A H) (at level 0).

Inductive LR {l : TypeLevel} (rec : forall l', l' << l -> LogRelKit)
  : RedRel :=
  | LRU {Γ} (H : [Γ ||-U ]) :
      LR rec Γ U
      (fun B   => [Γ ||-U≅ B ])
      (fun t   => [ rec | Γ ||-U t     :::U | H.(URel.lt) ])
      (fun t u => [ rec | Γ ||-U t ≅ u :::U | H.(URel.lt) ])
  | LRne {Γ A} (neA : [ Γ ||-ne A ]) :
      LR rec Γ A
      (fun B   =>  [ Γ ||-ne A ≅ B       | neA])
      (fun t   =>  [ Γ ||-ne t     ::: A | neA])
      (fun t u =>  [ Γ ||-ne t ≅ u ::: A | neA])
  | LRPi {Γ : context} {A : term} (ΠA : [ Γ ||-Πr A ]) (ΠAvalid : TyPiRelValid (LR rec) ΠA) :
    LR rec Γ A
      (fun B   => [ Γ ||-Π A ≅ B       | ΠA ])
      (fun t   => [ Γ ||-Π t     ::: A | ΠA ])
      (fun t u => [ Γ ||-Π t ≅ u ::: A | ΠA ])
  | LREmb {Γ A l'} (l_ : l' << l) (H : [ rec _ l_ | Γ ||- A]) :
      LR rec Γ A
      (fun B   => [ _ | Γ ||- A ≅ B       | H ])
      (fun t   => [ _ | Γ ||- t     ::: A | H ])
      (fun t u => [ _ | Γ ||- t ≅ u ::: A | H ])
  .

Definition RelTy
{l : TypeLevel} (R : forall l', l' << l -> LogRelKit)
(Γ : context) (A : term) :=
  LRValid Γ A (LR R).

Notation "[ R | Γ ||-p A ]" := (RelTy R Γ A) (at level 0).
(* 
Definition RelTyEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (A B : term) (H : RelTy R Γ A) :=
  [ Γ ||-p A ≅ B | H ].

Definition RelTe {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t A : term) (H : RelTy R Γ A) :=
  [ Γ ||-p t ::: A | H ].

Definition RelTeEq {l : TypeLevel} {R : forall l' ,l' << l -> LogRelKit}
(Γ : context) (t u A : term) (H : RelTy R Γ A) :=
  [ Γ ||-p t ≅ u ::: A | H ]. *)

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
  Build_LogRelKit
  (@URel zero)
  TyPiRel
  (fun Γ A => LRValid Γ A (LR rec0))
  (fun Γ A B (R : LRValid Γ A (LR rec0)) => R.(LRPack.eq) B)
  (fun Γ t A (R : LRValid Γ A (LR rec0)) => R.(LRPack.term) t)
  (fun Γ t u A (R : LRValid Γ A (LR rec0)) => R.(LRPack.eqTerm) t u).

Definition LogRelRec (l l' : TypeLevel) (h : l' << l) : LogRelKit :=
  match l as t return ((l') << (t) -> LogRelKit) with
    | zero => fun h0 : (l') << (zero) => rec0 l' h0
    | one => fun _ : (l') << (one) => kit0
  end h.

Definition rec1 :=
  LogRelRec one.

Definition LR1 := LR rec1.

Definition LRL (l : TypeLevel) :=
  match l with
    | zero => LR0
    | one => LR1
  end.

  (*TODO minimiser univers*)
Definition kit (l : TypeLevel) : LogRelKit :=
  let rec := LogRelRec l in
  Build_LogRelKit
    (@URel l)
    (fun Γ A => TyPiRel Γ A)
    (fun Γ A => LRValid Γ A (LR rec))
    (fun Γ A B (R : LRValid Γ A (LR rec)) => R.(LRPack.eq) B)
    (fun Γ t A (R : LRValid Γ A (LR rec)) => R.(LRPack.term) t)
    (fun Γ t u A (R : LRValid Γ A (LR rec)) => R.(LRPack.eqTerm) t u).

Definition recl (l : TypeLevel) :=
  match l with
    |zero => rec0
    |one => rec1
  end.

Definition Ur (Γ : context) (l : TypeLevel) : Type :=
  [ kit l | Γ ||-U].
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

Definition LRbuild {Γ l A rEq rTe rTeEq} :
  LR (recl l) Γ A rEq rTe rTeEq ->
  [Γ ||-< l | A] :=
  match l with
    | zero => fun H => Build_LRValid H
    | one => fun H => Build_LRValid H
end.

Lemma LRunbuild {Γ l A} :
  [Γ ||-< l | A] ->
  ∑ rEq rTe rTeEq , LR (recl l) Γ A rEq rTe rTeEq.
Proof.
  intros [].
  destruct l ; red in valid ; cbn in *.
  all: do 3 eexists ; eassumption.
Qed.

Create HintDb logrel.
#[global] Hint Constants Opaque : logrel.
#[global] Hint Variables Transparent : logrel.
Ltac logrel := eauto with logrel.

#[global] Hint Resolve LRbuild : logrel.

Definition LRU_ {Γ} l (H : [Γ ||-U]) : [Γ ||-< l | U] :=
  Build_LRValid (LRU (LogRelRec l) H).

Definition LRne_ (Γ : context) l {A : term} (neA : [Γ ||-ne A])
  : [Γ ||-< l | A] :=
  Build_LRValid (LRne (LogRelRec l) neA).

Definition LRPi_ (Γ : context) l {A : term}
  (ΠrA : [Γ ||-Πr A]) (ΠvA : TyPiRelValid (LR (LogRelRec l)) ΠrA)
  : [Γ ||-<l | A] :=
  Build_LRValid (LRPi (LogRelRec l) ΠrA ΠvA).

Definition LREmb_ (Γ : context) {l l'} (l_ : l' << l) {A : term}
  (H : [LogRelRec l l' l_ | Γ ||- A])
  : [ Γ ||-< l | A ]
  := Build_LRValid (LREmb (LogRelRec l) l_ H).

(*Definition eta {A B} (f : A -> B) : f = fun x => f x := eq_refl.

Definition emb' {Γ A} l (l_ : l = one) (p : [Γ ||-< zero | A ]) :  [Γ ||-< l | A].
  destruct p.
  econstructor.
  rewrite l_.
  rewrite (eta relEq'0) in valid0.
  rewrite (eta relTerm'0) in valid0.
  rewrite (eta relEqTerm'0) in valid0.
  destruct valid0.
  eapply LRemb.
Qed.*)