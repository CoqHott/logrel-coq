(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.

(** ** Weak-head normal forms and neutrals. *)

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tNat : whnf tNat
  | whnf_tZero : whnf tZero
  | whnf_tSucc {n} : whnf (tSucc n)
  | whnf_tEmpty : whnf tEmpty
  | whnf_tSig {A B} : whnf (tSig A B)
  | whnf_tPair {A B a b} : whnf (tPair A B a b)
  | whnf_tList {A} : whnf (tList A)
  | whnf_tNil {A} : whnf (tNil A)
  | whnf_tCons {A a l} : whnf (tCons A a l)
  | whnf_whne {n} : whne n -> whnf n
  | whnf_whne_list {n} : whne_list n -> whnf n
with whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_tFst {p} : whne p -> whne (tFst p)
  | whne_tSnd {p} : whne p -> whne (tSnd p)
with whne_list : term -> Type :=
  | whne_tMap {A B f l} : whne l -> whne_list (tMap A B f l)
  | whne_list_whne {n} : whne n -> whne_list n.


#[global] Hint Constructors whne whne_list whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
    try solve [inversion H] ; block H
    | H : whne_list _ |- _ =>
    let H' := fresh in
    try solve [inversion H as [|? H'] ; inversion H'] ; block H
  end; unblock.

Lemma neSort s : whne (tSort s) -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi A B : whne (tProd A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda A t : whne (tLambda A t) -> False.
Proof.
  inversion 1.
Qed.

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

Lemma whne_list_not_map {t} : whne_list t -> ~~ Map.is_map t ->  whne t.
Proof.
  intros []; [cbn;discriminate| easy].
Qed.


(** ** Restricted classes of normal forms *)

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | EmptyType : isType tEmpty
  | SigType {A B} : isType (tSig A B)
  | ListType {A} : isType (tList A)
  | NeType {A}  : whne A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | EmptyPos : isPosType tEmpty
  | NePos {A}  : whne A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | NeFun  {f} : whne f -> isFun f.

Inductive isNat : term -> Type :=
  | ZeroNat : isNat tZero
  | SuccNat {t} : isNat (tSucc t)
  | NeNat {n} : whne n -> isNat n.

Inductive isPair : term -> Type :=
  | PairPair {A B a b} : isPair (tPair A B a b)
  | NePair {p} : whne p -> isPair p.

Definition isPosType_isType t (i : isPosType t) : isType t.
Proof. destruct i; now constructor. Defined.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isFun_whnf : isFun >-> whnf.

Definition isPair_whnf t (i : isPair t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isPair_whnf : isPair >-> whnf.

Definition isNat_whnf t (i : isNat t) : whnf t :=
  match i with
  | ZeroNat => whnf_tZero
  | SuccNat => whnf_tSucc
  | NeNat n => whnf_whne  n
  end.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isPair_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat : gen_typing.

(** ** Canonical forms *)

Inductive isCanonical : term -> Type :=
  | can_tSort {s} : isCanonical (tSort s)
  | can_tProd {A B} : isCanonical (tProd A B)
  | can_tLambda {A t} : isCanonical (tLambda A t)
  | can_tNat : isCanonical tNat
  | can_tZero : isCanonical tZero
  | can_tSucc {n} : isCanonical (tSucc n)
  | can_tEmpty : isCanonical tEmpty
  | can_tSig {A B} : isCanonical (tSig A B)
  | can_tPair {A B a b}: isCanonical (tPair A B a b)
  | can_tList {A} : isCanonical (tList A)
  | can_tNil {A} : isCanonical (tNil A)
  | can_tCons {A hd tl} : isCanonical (tCons A hd tl).

#[global] Hint Constructors isCanonical : gen_typing.

(** ** Normal forms and compactification *)

Lemma eta_map_lst_whne A l (x := Map.eta A l) :
  whne_list l -> whne x.(Map.lst).
Proof.
  destruct l; unfold x; cbn; intros h; inversion h; try easy.
  inv_whne.
Qed.
  
Lemma eta_map_whne A l (x := Map.eta A l) :
  whne x.(Map.lst) -> whne_list l.
Proof.
  destruct l; unfold x; cbn; now econstructor.
Qed.

Lemma whne_map n :
  whne n ->
  ~~ Map.is_map n.
Proof.
  intros [] ; now reflexivity.
Qed.