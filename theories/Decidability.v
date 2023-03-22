(** * LogRel.Decidability: type-checker implementation. *)
From PartialFun Require Import PartialFun.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import BasicAst Context.

Inductive stack :=
| sApp (u : term) (π : stack)
| sNil.

Fixpoint zip t π :=
  match π with
  | sApp u π => zip (tApp t u) π
  | sNil => t
  end.

Equations wh_red_stack : term*stack ⇀ term :=
  wh_red_stack (tLambda _ _ t, sApp u π) :=
    v ← rec (t[u..], π) ;;
    ret v ;
  wh_red_stack (tLambda na A t, sNil) :=
    ret (tLambda na A t) ;
  wh_red_stack (tApp t u, π) :=
    v ← rec (t, sApp u π) ;;
    ret v ;
  (* Ideally, we would want to error when the stack is non-empty in this case. *)
  wh_red_stack (t, π) := ret (zip t π).

Equations wh_red : term ⇀ term :=
  wh_red t := t' ← call wh_red_stack (t,sNil) ;; ret t'.

Definition wh_red_fuel n t := fueled wh_red n t.

Compute (wh_red_fuel 10 (tApp (tLambda anDummy U (tRel 0)) U)).

(** Fails: not possible to mutually define functions? *)
Fail Equations conv : (context*term*term*term) ⇀ bool :=
  conv (Γ,A,t,u) :=
    A' ← call wh_red A ;;
    t' ← call wh_red t ;;
    u' ← call wh_red u ;;
    b ← call conv_red (Γ,A',t',u') ;;
    ret b ;
where conv_red : (context*term*term*term) ⇀ bool :=
  conv_red (Γ,A,t,u) := ret true.