From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.

Definition whne := whne RedFlags.default empty_global_env.
Definition whnf := whnf RedFlags.default empty_global_env.
Definition emptyName : aname := 
  ltac:(repeat econstructor).

Definition eta {A B} (f : A -> B) : f = fun x => f x := eq_refl.

Inductive isType : term -> Type :=
  | ProdType {na A B} : isType (tProd na A B)
  | NeType {Γ A}  : whne Γ A -> isType A. 

Inductive isFun : term -> Type :=
  | lamFun {na A t} : isFun (tLambda na A t)
  | NeFun  { Γ A }  : whne Γ A -> isFun A.