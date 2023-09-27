
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DeclarativeTyping Weakening GenericTyping.

From LogRel Require Import DirectedDirections DirectedErasure.
From LogRel Require DirectedDeclarativeTyping DirectedContext.

From PartialFun Require Import Monad PartialFun.

Import MonadNotations.
Set Universe Polymorphism.
Import IndexedDefinitions.
Import StdInstance.


Definition witType (d: direction) : Type :=
  match d with
  | Fun | Cofun => term
  | Discr => unit
  end.

Definition witList := list (∑ (d: direction), witType d).

Equations tsl_fun (γ : witList) : (direction × term) ⇀ term :=
  tsl_fun γ (d, (tSort s)) := ret (tLambda (tSort s) (tRel 0)) ;
  tsl_fun γ _ := undefined.



