From LogRel.AutoSubst Require Import unscoped Ast.
From LogRel Require Import Utils BasicAst Context.

Export UnscopedNotations.
#[global] Open Scope subst_scope.

Notation U := (tSort set).
Notation "'eta_expand' f" := (tApp f⟨↑⟩ (tRel 0)) (at level 40, only parsing).

Inductive whnf : term -> Type :=
  | whnf_tSort s : whnf (tSort s)
  | whnf_tProd na A B : whnf (tProd na A B)
  | whnf_tLambda na A t : whnf (tLambda na A t)
  | whnf_whne n : whne n -> whnf n
with whne : term -> Type :=
  | whne_tRel v : whne (tRel v)
  | whne_tApp n t : whne n -> whne (tApp n t).

#[global] Hint Constructors whne whnf : gen_typing.

Inductive isType : term -> Type :=
  | UnivType : isType U
  | ProdType {na A B} : isType (tProd na A B)
  | NeType {A}  : whne A -> isType A.

Inductive isFun : term -> Type :=
  | lamFun {na A t} : isFun (tLambda na A t)
  | NeFun  {A}  : whne A -> isFun A.

Lemma isType_whnf t : isType t -> whnf t.
Proof.
  induction 1; now constructor.
Qed.

Lemma isFun_whnf t : isFun t -> whnf t.
Proof.
  induction 1 ; now constructor.
Qed.

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