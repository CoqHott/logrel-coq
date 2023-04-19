(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context LContexts.

(** ** Weak-head normal forms and neutrals. *)

Inductive whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tBoolElim {P hz hs n} : whne n -> whne (tBoolElim P hz hs n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_containsne {n t} : whne t -> whne (tAlpha (nSucc n t)).

Inductive alphawhne (l : wfLCon) (n : nat) : term -> Type :=
  | alphawhne_base :
    not_in_LCon (pi1 l) n ->
    alphawhne l n (tAlpha (nat_to_term n))
  | alphawhne_tApp {t u} : alphawhne l n t -> alphawhne l n (tApp t u)
  | alphawhne_tNatElim {P hz hs t} : alphawhne l n t -> alphawhne l n (tNatElim P hz hs t)
  | alphawhne_tBoolElim {P hz hs t} :
    alphawhne l n t ->
    alphawhne l n (tBoolElim P hz hs t)
  | alphawhne_tEmptyElim {P e} : alphawhne l n e -> alphawhne l n (tEmptyElim P e)
  | alphawhne_alpha {t} : alphawhne l n t -> alphawhne l n (tAlpha t).
                                           

Inductive whnf : term -> Type :=
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
  | whnf_whne {n} : whne n -> whnf n.
(*  | whnf_tAlpha {n} : alphawhne l n -> whnf l n.*)
  
#[global] Hint Constructors whne whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
        try solve [inversion H] ; block H
    | H : alphawhne _ _ _ |- _ =>
        try solve [inversion H] ; block H
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

Lemma containsnewhnf {n} t : whne t -> whnf (nSucc n t).
Proof.
  intro H.
  induction n ; cbn ; now econstructor.
Qed.


Lemma nenattoterm {n} : whne (nat_to_term n) -> False.
Proof.
  intro H.
  induction n ; cbn in * ; inversion H.
Qed.

Lemma containsnenattoterm {n} : whne (tAlpha (nat_to_term n)) -> False.
Proof.
  intro H ; inversion H ; subst ; clear H.
  revert n0 H0.
  unfold nat_to_term ; cbn.
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

Lemma whnfnattoterm t : whnf (nat_to_term t).
Proof.
  induction t  ; cbn ; now econstructor.
Qed.

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

(** ** Restricted classes of normal forms *)

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | BoolType : isType tBool
  | EmptyType : isType tEmpty
  | NeType {A}  : whne A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | BoolPos : isPosType tBool
  | EmptyPos : isPosType tEmpty
  | NePos {A}  : whne A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | NeFun  {f} : whne f -> isFun f.

Definition isPosType_isType t (i : isPosType t) : isType t :=
  match i with
    | UnivPos => UnivType
    | NatPos => NatType
    | BoolPos => BoolType
    | EmptyPos => EmptyType
    | NePos ne => NeType ne
  end.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t :=
  match i with
    | UnivType => whnf_tSort
    | ProdType => whnf_tProd
    | NatType => whnf_tNat
    | BoolType => whnf_tBool
    | EmptyType => whnf_tEmpty
    | NeType ne => whnf_whne ne
  end.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t :=
  match i with
    | LamFun => whnf_tLambda
    | NeFun ne => whnf_whne ne
  end.

Coercion isFun_whnf : isFun >-> whnf.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf : gen_typing.


(*Lemma whne_Ltrans {l l' t} (f : l' ≤ε l) :
  whne t -> whne l' t.
Proof.
  intro H ; induction H ; try now econstructor.
Qed.*)


Lemma alphawhne_Ltrans {l l' n t} (f : l' ≤ε l) :
  alphawhne l n t -> not_in_LCon l' n -> alphawhne l' n t.
Proof.
  intros H notinl' ; induction H ; try now econstructor.
Qed.

Lemma alphawhne_notinLCon {l n t} :
  alphawhne l n t -> not_in_LCon l n.
Proof.
  intro Hyp.
  induction Hyp ; easy.
Qed.
