
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms DeclarativeTyping Weakening GenericTyping.

From LogRel Require Import DirectedDirections DirectedErasure.
From LogRel Require DirectedDeclarativeTyping DirectedContext.

From PartialFun Require Import Monad PartialFun.

Import MonadNotations.
Set Universe Polymorphism.
Import IndexedDefinitions.
Import StdInstance.

(* NOTE: no need to handle lambda, because we only look at types in whnf *)
Equations type_action (γ : list (option term)) : term ⇀ term :=
  type_action γ (tSort s) := ret (tLambda (tSort s) (tRel 0)) ;
  type_action γ (tProd A B) := tB ← rec B ;; ret (tLambda A tB) ;
  type_action γ (tRel n) := match List.nth n γ None with
                        | Some t => ret t
                        | None => undefined
                        end ;
  type_action γ (tApp f a) := tf ← rec f ;; ret (tApp tf a) ;
  type_action γ _ := undefined.

