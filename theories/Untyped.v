From LogRel.AutoSubst Require Import unscoped Ast.
From LogRel Require Import Utils BasicAst Context.

Export UnscopedNotations.
#[global] Open Scope subst_scope.

Notation U := (tSort set).
Notation "'eta_expand' f" := (tApp f⟨↑⟩ (tRel 0)) (at level 40, only parsing).

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {na A B} : whnf (tProd na A B)
  | whnf_tLambda {na A t} : whnf (tLambda na A t)
  | whnf_whne {n} : whne n -> whnf n
with whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t).

#[global] Hint Constructors whne whnf : gen_typing.

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType {na A B} : isType (tProd na A B)
  | NeType {A}  : whne A -> isType A.

Inductive isFun : term -> Type :=
  | LamFun {na A t} : isFun (tLambda na A t)
  | NeFun  {f} : whne f -> isFun f.

Definition isType_whnf t (i : isType t) : whnf t :=
  match i with
    | UnivType => whnf_tSort
    | ProdType => whnf_tProd
    | NeType ne => whnf_whne ne
  end.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t :=
  match i with
    | LamFun => whnf_tLambda
    | NeFun ne => whnf_whne ne
  end.

Coercion isFun_whnf : isFun >-> whnf.

Lemma neU : whne U -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi na A B : whne (tProd na A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda na A t : whne (tLambda na A t) -> False.
Proof.
  inversion 1.
Qed.

#[global] Hint Resolve isType_whnf isFun_whnf neU nePi neLambda : gen_typing.