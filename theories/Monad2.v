From LogRel.AutoSubst Require Import core unscoped Ast Extra.
Require Import PeanoNat.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening GenericTyping.

Inductive Dial@{i} (wl : wfLCon) (P : wfLCon -> Type@{i}) : Type@{i} :=
| eta : P wl -> Dial wl P
| ϝdig {n} {ne : not_in_LCon (pi1 wl) n} :
  Dial (wl ,,l (ne, true)) P ->
  Dial (wl ,,l (ne, false)) P ->
  Dial wl P.

Definition Dbind (wl : wfLCon) (P Q : wfLCon -> Type)
  (f : forall wl', wl' ≤ε wl -> P wl' -> Dial wl' Q)
  (p : Dial wl P) : Dial wl Q.
Proof.
  induction p.
  - eapply f ; try eassumption.
    now eapply wfLCon_le_id.
  - unshelve eapply ϝdig.
    2: eassumption.
    + eapply IHp1.
      intros ; eapply f ; try eassumption.
      eapply wfLCon_le_trans.
      eassumption.
      eapply LCon_le_step.
      now eapply wfLCon_le_id.
    + eapply IHp2.
      intros ; eapply f ; try eassumption.
      eapply wfLCon_le_trans.
      eassumption.
      eapply LCon_le_step.
      now eapply wfLCon_le_id.
Qed.

Fixpoint BType (wl : wfLCon) (P : wfLCon -> Type)
  (Q : forall wl', P wl' -> Type)
  (p : Dial wl P) : Type    :=
  match p with
  | eta _ _ x => Q wl x
  | ϝdig _ _ pt pf => prod (@BType _ P Q pt) (BType _ P Q pf)
  end.

(*Fixpoint BType_dep (wl : wfLCon) (P : wfLCon -> Type)
  (Q : forall wl', P wl' -> Type)
  (R : forall wl' p, Q wl' p -> Type)
  (p : Dial wl P) :
  BType wl P Pe Q Qe p -> Type :=
  match p with
  | eta _ _ x => fun H => R wl x H
  | ϝdig _ _ pt pf => fun H => prod (BType_dep _ P Q R pt (fst H))
                                 (BType_dep _ P Q R pf (snd H))
  end.
*)
