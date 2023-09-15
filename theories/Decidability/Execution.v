(** * LogRel.Decidability.Execution: example executions of the type checker, in Coq. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Notations BasicAst Context GenericTyping DeclarativeTyping DeclarativeInstance BundledAlgorithmicTyping AlgorithmicTypingProperties.
From PartialFun Require Import Monad PartialFun.
From LogRel.Decidability Require Import Functions Soundness.

Import DeclarativeTypingProperties.
Import IndexedDefinitions.

#[local] Definition infer (Γ : context) (t : term) : Fueled (result term) :=
  (fueled typing 1000 (inf_state;Γ;tt;t)).

#[local] Definition check (Γ : context) (T t : term) : Fueled (result unit) := 
  (fueled typing 1000 (check_state;Γ;T;t)).

#[local] Definition check_ty (Γ : context) (t : term) : Fueled (result unit) := 
  (fueled typing 1000 (wf_ty_state;Γ;tt;t)).

#[local] Definition conv_tm (Γ : context) (T: term) (t1 : term) (t2 : term) : Fueled _ :=
  (fueled conv 1000 (tm_state;Γ;T;t1;t2)).


Ltac infer_auto :=
  match goal with
  | |- [ε |- ?t : ?T] =>
    assert [|- ε] by econstructor ;
      eassert (graph typing (inf_state;ε;tt;t) (ok _))
        as ?%implem_typing_sound%algo_typing_sound
        by (apply (fueled_graph_sound typing 1000 (inf_state;_)) ; reflexivity)
  end ; auto.

Ltac wf_ty_auto :=
  match goal with
  | |- [ε |- ?T] =>
      assert [|- ε] by econstructor ;
      eassert (graph typing (wf_ty_state;ε;tt;T) (ok _))
        as ?%implem_typing_sound%algo_typing_sound
        by (apply (fueled_graph_sound typing 1000 (wf_ty_state;_)) ; reflexivity)
  end ; auto.

Ltac check_auto :=
  match goal with
  | |- [ε |- ?t : ?T] =>
    assert [|- ε] by econstructor ;
    eassert (graph typing (check_state;ε;T;t) (ok _))
      as ?%implem_typing_sound%algo_typing_sound
      by (apply (fueled_graph_sound typing 1000 (check_state;_)) ; reflexivity) ;
    eassert (graph typing (wf_ty_state;ε;tt;T) (ok _))
      as ?%implem_typing_sound%algo_typing_sound
      by (apply (fueled_graph_sound typing 1000 (wf_ty_state;_)) ; reflexivity) ;
    auto
end.

(*** A series of example, each time the term in Coq first, then a proof that it type-checks
  in our system, proven via reification. *)

Check ((0;0) : ∑ x : nat, nat).

Goal [ε |- tPair tNat tNat tZero tZero : tSig tNat tNat].
Proof.
  infer_auto.
Qed.

Check ((fun x => nat_rec (fun _ => nat) 0 (fun _ ih => S (S ih)) x) : nat -> nat).

Goal [ε |-
  (tLambda tNat (tNatElim
    tNat
    tZero
    (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
    (tSucc (tSucc tZero))))
  : arr tNat tNat].
Proof.
  infer_auto.
Qed.

Check (eq_refl : (nat_rect (fun _ => Type) nat (fun _ ih => nat -> ih) 3) = (nat -> nat -> nat -> nat)).

Goal [ε |-
  tRefl U (arr tNat (arr tNat (arr tNat tNat))) : 
  tId U
    (arr tNat (arr tNat (arr tNat tNat)))
    (tNatElim
      U
      tNat
      (tLambda tNat (tLambda U (arr tNat (tRel 0))))
    (tSucc (tSucc (tSucc (tZero)))))].
Proof.
  check_auto.
Qed.