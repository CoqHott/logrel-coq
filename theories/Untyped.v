From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.

Definition neutral := whne RedFlags.default empty_global_env.
Definition emptyName : aname := 
  ltac:(repeat econstructor).

Inductive isType : term -> Type :=
  | ProdType {na A B} : isType (tProd na A B)
  | NeType {Γ A}  : neutral Γ A -> isType A. 

Inductive isFun : term -> Type :=
  | lamFun {na A t} : isFun (tLambda na A t)
  | NeFun  { Γ A }  : neutral Γ A -> isFun A.

Definition isWhnf (Γ : context) (A : term) := 
  whnf RedFlags.default empty_global_env Γ A.