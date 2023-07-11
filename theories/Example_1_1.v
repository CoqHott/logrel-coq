
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Notations BasicAst Context GenericTyping DeclarativeTyping DeclarativeInstance BundledAlgorithmicTyping.
From PartialFun Require Import Monad PartialFun.
From LogRel.Decidability Require Import Functions Soundness Completeness Termination.

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

Definition rec2 (A B: term) : term := tSig A B⟨↑⟩.
Definition mkRec2 (A B: term) (a b: term) := tPair A B⟨↑⟩ a b.
Definition rec2pi1 (p: term) : term := tFst p.
Definition rec2pi2 (p: term) : term := tSnd p.
Eval vm_compute in (infer ε (mkRec2 tNat tNat tZero tZero)).

Definition rec2N := rec2 tNat tNat.
Definition mkRec2N (a b : term) := mkRec2 tNat tNat a b.

Definition rec3 (A B C: term) : term := tSig A (rec2 B C)⟨↑⟩.
Definition mkRec3 (A B C: term) (a b c: term) : term := tPair A (rec2 B C)⟨↑⟩ a (mkRec2 B C b c).
Definition rec3pi1 (p: term) : term := tFst p.
Definition rec3pi2 (p: term) : term := tFst (tSnd p).
Definition rec3pi3 (p: term) : term := tSnd (tSnd p).
Eval vm_compute in (infer ε (mkRec3 tNat tNat tNat tZero tZero tZero)).

Definition rec3N := rec3 tNat tNat tNat.
Definition mkRec3N (a b c : term) := mkRec3 tNat tNat tNat a b c.

Definition idtype A := (arr A A).
Definition idty_rec2N := idtype rec2N.

Fixpoint nat_to_tNat (n: nat) :=
  match n with
  | O => tZero
  | S n => tSucc (nat_to_tNat n)
  end.
Definition forty_two : term := nat_to_tNat 42.

Definition glue : term :=
  tLambda rec2N
    (mkRec3N
       (rec2pi1 (tRel 0))
       (rec2pi2 (tRel 0))
       forty_two
    ).
Eval vm_compute in (infer ε glue).
Check (eq_refl : infer ε glue = Success (ok (arr rec2N rec3N))).

Definition glue_retr : term :=
  tLambda rec3N
    (mkRec2N
       (rec3pi1 (tRel 0))
       (rec3pi2 (tRel 0))
    ).
Eval vm_compute in (infer ε glue_retr).
Check (eq_refl : infer ε glue_retr = Success (ok (arr rec3N rec2N))).

Eval vm_compute in (conv_tm ε idty_rec2N (idterm rec2N) (comp rec2N glue_retr glue)).

Definition map_example :=
  tLambda (tList rec2N) (tMap rec3N rec2N glue_retr (tMap rec2N rec3N glue (tRel 0))).

Eval vm_compute in (conv_tm ε (idtype (tList rec2N)) map_example (idterm (tList rec2N))).

Lemma map_example_conv : conv_tm ε (idtype (tList rec2N)) map_example (idterm (tList rec2N)) = Success (ok tt).
Proof.
  reflexivity.
Qed.

Lemma map_example_ty_eq : infer ε map_example = Success (ok (idtype (tList rec2N))).
Proof.
  reflexivity.
Qed.

Lemma map_example_ty : [ε |- map_example : idtype (tList rec2N)].
Proof.
  pose proof map_example_ty_eq as e.
  unfold infer in e.
  eapply (fueled_graph_sound typing _ (inf_state; _)) in e.
  apply implem_typing_sound, algo_typing_sound in e.
  + assumption.
  + constructor.
Fail Qed. (* Stack overflow *)
Admitted.

Lemma idterm_ty : infer ε (idterm (tList rec2N)) = Success (ok (idtype (tList rec2N))).
Proof.
  reflexivity.
Qed.

Theorem example_1_1_conv : [ε |- map_example ≅ idterm (tList rec2N) : idtype (tList rec2N)].
Proof.
  pose proof map_example_conv as e.
  unfold conv_tm in e.
  eapply (fueled_graph_sound conv) in e.
  apply implem_conv_sound, algo_conv_sound in e.
  - assumption.
  - apply map_example_ty.
  - clear.
    pose proof idterm_ty as e.
    unfold infer in e.
    eapply (fueled_graph_sound typing _ (inf_state; _)) in e.
    apply implem_typing_sound, algo_typing_sound in e.
    + assumption.
    + constructor.
Fail Qed.
Admitted.