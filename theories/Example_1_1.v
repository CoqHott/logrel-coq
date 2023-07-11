
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context DeclarativeTyping.
From LogRel.Decidability Require Import Functions Soundness Completeness Termination.

#[local] Definition infer (Γ : context) (t : term) : Fueled (result term) :=
  (fueled typing 1000 (inf_state;Γ;tt;t)).

#[local] Definition check (Γ : context) (T t : term) : Fueled (result unit) := 
  (fueled typing 1000 (check_state;Γ;T;t)).

#[local] Definition check_ty (Γ : context) (t : term) : Fueled (result unit) := 
  (fueled typing 1000 (wf_ty_state;Γ;tt;t)).

#[local] Definition conv_tm (Γ : context) (T: term) (t1 : term) (t2 : term) : Fueled _ :=
  (fueled conv 1000 (tm_state;Γ;T;t1;t2)).

Definition rec2 (A B: term) : term := tSig A B⟨↑⟩.
Definition mkRec2 (A B: term) (a b: term) := tPair A B⟨↑⟩ a b.
Definition rec2pi1 (p: term) : term := tFst p.
Definition rec2pi2 (p: term) : term := tSnd p.
Eval vm_compute in (infer ε (mkRec2 tNat tNat tZero tZero)).

Definition rec3 (A B C: term) : term := tSig A (rec2 B C)⟨↑⟩.
Definition mkRec3 (A B C: term) (a b c: term) : term := tPair A (rec2 B C)⟨↑⟩ a (mkRec2 B C b c).
Definition rec3pi1 (p: term) : term := tFst p.
Definition rec3pi2 (p: term) : term := tFst (tSnd p).
Definition rec3pi3 (p: term) : term := tSnd (tSnd p).
Eval vm_compute in (infer ε (mkRec3 tNat tNat tNat tZero tZero tZero)).


Fixpoint nat_to_tNat (n: nat) :=
  match n with
  | O => tZero
  | S n => tSucc (nat_to_tNat n)
  end.
Definition forty_two : term := nat_to_tNat 42.

Definition glue : term :=
  tLambda (rec2 tNat tNat)
    (mkRec3 tNat tNat tNat
       (rec2pi1 (tRel 0))
       (rec2pi2 (tRel 0))
       forty_two
    ).
Eval vm_compute in (infer ε glue).

Definition glue_retr : term :=
  tLambda (rec3 tNat tNat tNat)
    (mkRec2 tNat tNat
       (rec3pi1 (tRel 0))
       (rec3pi2 (tRel 0))
    ).
Eval vm_compute in (infer ε glue_retr).

Definition idtest : term :=
  tLambda (rec2 tNat tNat)
    (mkRec2 tNat tNat
       (rec2pi1 (tRel 0))
       (rec2pi2 (tRel 0))
    ).
Eval vm_compute in (infer ε idtest).
Eval vm_compute in (infer ε (idterm (rec2 tNat tNat))).


Eval vm_compute in (conv_tm ε (rec2 tNat tNat) idtest (idterm (rec2 tNat tNat))).







