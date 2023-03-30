(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context LContexts.

(** ** Weak-head normal forms and neutrals. *)

Inductive whne {l : wfLCon} : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tBoolElim {P hz hs n} : whne n -> whne (tBoolElim P hz hs n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_containsne {t} : containsne t -> whne (tAlpha t)
with containsne {l : wfLCon} : term -> Type :=
  | necontne {t}: whne t -> containsne t
  | scontne {t} : containsne t -> containsne (tSucc t).

Inductive alphawhne (l : wfLCon) : term -> Type :=
  | alphawhne_base {n} : not_in_LCon (fst l) n -> alphawhne l (tAlpha (nat_to_term n))
  | alphawhne_tApp {n t} : alphawhne l n -> alphawhne l (tApp n t)
  | alphawhne_tNatElim {P hz hs n} : alphawhne l n -> alphawhne l (tNatElim P hz hs n)
  | alphawhne_tBoolElim {P hz hs n} : alphawhne l n -> alphawhne l (tBoolElim P hz hs n)
  | alphawhne_tEmptyElim {P e} : alphawhne l e -> alphawhne l (tEmptyElim P e)
  | alphawhne_alpha {t} : alphawhne l t -> alphawhne l (tAlpha t).
                                           

Inductive whnf {l : wfLCon} : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tNat : whnf tNat
  | whnf_tZero : whnf tZero
  | whnf_tSucc {n} : whnf (tSucc n)
  | whnf_tBool : whnf tBool
  | whnf_tTrue : whnf tTrue
  | whnf_tFalse : whnf tFalse
  | whnf_tEmpty : whnf tEmpty
  | whnf_whne {n} : whne (l := l) n -> whnf n
  | whnf_tAlpha {n} : alphawhne l n -> whnf n.
  
#[global] Hint Constructors whne whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

Lemma neSort {l} s : whne (l := l) (tSort s) -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi {l} A B : whne (l := l) (tProd A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda {l} A t : whne (l := l) (tLambda A t) -> False.
Proof.
  inversion 1.
Qed.

Lemma containsnewhnf {l} t : containsne (l := l) t -> whnf (l := l) t.
Proof.
  intro H.
  inversion H ; subst.
  - now eapply whnf_whne.
  - now eapply whnf_tSucc.
Qed.

Lemma containsnenattoterm {l} t : containsne (l := l) (nat_to_term t) -> False.
Proof.
  intro H.
  induction t ; cbn in *.
  - inversion H ; subst.
    now inversion H0.
  - inversion H ; subst.
    + inversion H0.
    + now eapply IHt.
Qed.

Lemma whnfnattoterm {l} t : whnf (l := l) (nat_to_term t).
Proof.
  induction t  ; cbn.
  - now econstructor.
  - now econstructor.
Qed.

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

(** ** Restricted classes of normal forms *)

Inductive isType {l} : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | BoolType : isType tBool
  | EmptyType : isType tEmpty
  | NeType {A}  : whne (l := l) A -> isType A.

Inductive isPosType {l} : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | BoolPos : isPosType tBool
  | EmptyPos : isPosType tEmpty
  | NePos {A}  : whne (l := l) A -> isPosType A.

Inductive isFun {l} : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | NeFun  {f} : whne (l := l) f -> isFun f.

Definition isPosType_isType {l} t (i : isPosType (l := l) t) : isType t :=
  match i with
    | UnivPos => UnivType
    | NatPos => NatType
    | BoolPos => BoolType
    | EmptyPos => EmptyType
    | NePos ne => NeType ne
  end.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf {l} t (i : isType t) : whnf (l:= l) t :=
  match i with
    | UnivType => whnf_tSort
    | ProdType => whnf_tProd
    | NatType => whnf_tNat
    | BoolType => whnf_tBool
    | EmptyType => whnf_tEmpty
    | NeType ne => whnf_whne ne
  end.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf {l} t (i : isFun t) : whnf (l:= l) t :=
  match i with
    | LamFun => whnf_tLambda
    | NeFun ne => whnf_whne ne
  end.

Coercion isFun_whnf : isFun >-> whnf.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf : gen_typing.
