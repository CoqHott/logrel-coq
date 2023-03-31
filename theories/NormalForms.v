(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.

(** ** Weak-head normal forms and neutrals. *)

Inductive whne (l : wfLCon) : term -> Type :=
  | whne_tRel {v} : whne l (tRel v)
  | whne_tApp {n t} : whne l n -> whne l (tApp n t)
  | whne_tNatElim {P hz hs n} : whne l n -> whne l (tNatElim P hz hs n)
  | whne_tBoolElim {P hz hs n} : whne l n -> whne l (tBoolElim P hz hs n)
  | whne_tEmptyElim {P e} : whne l e -> whne l (tEmptyElim P e)
  | whne_containsne {n t} : whne l t -> whne l (tAlpha (nSucc n t)).

Inductive alphawhne (l : wfLCon) : term -> Type :=
  | alphawhne_base {n} : not_in_LCon (pi1 l) n -> alphawhne l (tAlpha (nat_to_term n))
  | alphawhne_tApp {n t} : alphawhne l n -> alphawhne l (tApp n t)
  | alphawhne_tNatElim {P hz hs n} : alphawhne l n -> alphawhne l (tNatElim P hz hs n)
  | alphawhne_tBoolElim {P hz hs n} : alphawhne l n -> alphawhne l (tBoolElim P hz hs n)
  | alphawhne_tEmptyElim {P e} : alphawhne l e -> alphawhne l (tEmptyElim P e)
  | alphawhne_alpha {t} : alphawhne l t -> alphawhne l (tAlpha t).
                                           

Inductive whnf (l : wfLCon) : term -> Type :=
  | whnf_tSort {s} : whnf l (tSort s)
  | whnf_tProd {A B} : whnf l (tProd A B)
  | whnf_tLambda {A t} : whnf l (tLambda A t)
  | whnf_tNat : whnf l tNat
  | whnf_tZero : whnf l tZero
  | whnf_tSucc {n} : whnf l (tSucc n)
  | whnf_tBool : whnf l tBool
  | whnf_tTrue : whnf l tTrue
  | whnf_tFalse : whnf l tFalse
  | whnf_tEmpty : whnf l tEmpty
  | whnf_whne {n} : whne l n -> whnf l n
  | whnf_tAlpha {n} : alphawhne l n -> whnf l n.
  
#[global] Hint Constructors whne whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

Lemma neSort {l} s : whne l (tSort s) -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi {l} A B : whne l (tProd A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda {l} A t : whne l (tLambda A t) -> False.
Proof.
  inversion 1.
Qed.

Lemma containsnewhnf {l n} t : whne l t -> whnf l (nSucc n t).
Proof.
  intro H.
  induction n ; cbn ; now econstructor.
Qed.


Lemma nenattoterm {l n} : whne l (nat_to_term n) -> False.
Proof.
  intro H.
  induction n ; cbn in * ; inversion H.
Qed.

Lemma containsnenattoterm {l n} : whne l (tAlpha (nat_to_term n)) -> False.
Proof.
  intro H ; inversion H ; subst ; clear H.
  revert n0 H0.
  induction n ; cbn in * ; intros.
  - induction n0 ; cbn in *.
    + rewrite H0 in H1 ; inversion H1.
    + change (match tZero with tZero => False | _ => True end).
      now rewrite <- H0.
  - destruct n0 ; cbn in *.
    + rewrite H0 in H1 ; now inversion H1.
    + eapply IHn.
      now eapply tSucc_inj.
Qed.

Lemma whnfnattoterm {l} t : whnf l (nat_to_term t).
Proof.
  induction t  ; cbn ; now econstructor.
Qed.

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

(** ** Restricted classes of normal forms *)

Inductive isType l : term -> Type :=
  | UnivType {s} : isType l (tSort s)
  | ProdType { A B} : isType l (tProd A B)
  | NatType : isType l tNat
  | BoolType : isType l tBool
  | EmptyType : isType l tEmpty
  | NeType {A}  : whne l A -> isType l A.

Inductive isPosType l : term -> Type :=
  | UnivPos {s} : isPosType l (tSort s)
  | NatPos : isPosType l tNat
  | BoolPos : isPosType l tBool
  | EmptyPos : isPosType l tEmpty
  | NePos {A}  : whne l A -> isPosType l A.

Inductive isFun l : term -> Type :=
  | LamFun {A t} : isFun l (tLambda A t)
  | NeFun  {f} : whne l f -> isFun l f.

Definition isPosType_isType {l} t (i : isPosType l t) : isType l t :=
  match i with
    | UnivPos _ => UnivType _
    | NatPos _ => NatType _
    | BoolPos _ => BoolType _
    | EmptyPos _ => EmptyType _
    | NePos _ ne => NeType _ ne
  end.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf {l} t (i : isType l t) : whnf l t :=
  match i with
    | UnivType _ => whnf_tSort _
    | ProdType _ => whnf_tProd _
    | NatType _ => whnf_tNat _
    | BoolType _ => whnf_tBool _
    | EmptyType _ => whnf_tEmpty _
    | NeType _ ne => whnf_whne _ ne
  end.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf {l} t (i : isFun l t) : whnf l t :=
  match i with
    | LamFun _ => whnf_tLambda _
    | NeFun _ ne => whnf_whne _ ne
  end.

Coercion isFun_whnf : isFun >-> whnf.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf : gen_typing.
