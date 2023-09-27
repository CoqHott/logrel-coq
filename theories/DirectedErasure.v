
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations.

From LogRel Require Context DirectedContext.

Fixpoint erase_dir (ctx: DirectedContext.context) : Context.context :=
  match ctx with
  | nil => nil
  | cons {| DirectedContext.ty := T |} l => cons T (erase_dir l)
  end.

(* TODO: translate derivations! *)
