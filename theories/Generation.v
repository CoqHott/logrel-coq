(** *LogRel.Generation: stronger inversion principles on typing. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms DeclarativeTyping.

Import DeclarativeTypingData.
Ltac prod_splitter :=
  solve [now repeat match goal with
  | |- sigT _ => eexists
  | |- prod _ _ => split 
  | |- and3 _ _ _ => split
  | |- and4 _ _ _ _ => split
  end].