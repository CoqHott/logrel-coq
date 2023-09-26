
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

Inductive ctx_data_entry :=
  (* TODO: complete me*).

Definition ctx_data := list ctx_data_entry.

Definition empty_store : forall (x: False), match x return Set with end :=
  fun x => match x as x return match x return Set with end with end.

#[global]
Instance empty_pfun : forall (x:False), PFun@{Set Set Set} (empty_store x) | 5 :=
  fun x => match x as x return PFun (empty_store x) with end.


Equations tsl_fun (γ : ctx_data) : term ⇀[empty_store] term :=
  tsl_fun γ A := undefined.



