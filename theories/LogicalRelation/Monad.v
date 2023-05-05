From LogRel.AutoSubst Require Import core unscoped Ast Extra.
Require Import PeanoNat.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening GenericTyping.

Record Weak (wl : wfLCon) (P : wfLCon -> Type) : Type :=
  { PN : nat ;
    WP : forall wl' : wfLCon, wl' ≤ε wl -> AllInLCon PN wl' -> P wl' ;
    }.

Definition Wret (wl : wfLCon) (P : wfLCon -> Type)
  (Pe : forall wl' wl'', wl'' ≤ε wl' -> P wl' -> P wl'')
  (p : P wl) : Weak wl P.
Proof.
  unshelve econstructor.
  - exact 0.
  - intros ; now eapply Pe.
Defined.

Definition Wbind (wl : wfLCon) (P Q : wfLCon -> Type)
  (Pe : forall wl' wl'', wl'' ≤ε wl' -> P wl' -> P wl'')
  (Qe : forall wl' wl'', wl'' ≤ε wl' -> Q wl' -> Q wl'')
  (f : forall wl', wl' ≤ε wl -> P wl' -> Weak wl' Q)
  (p : Weak wl P) : Weak wl Q.
Proof.
  unshelve econstructor.
  - unshelve refine (max (PN wl P p) (Max_Bar _ _ _)).
    + exact wl.
    + exact (PN _ _ p).
    + intros wl' tau Ninfl.
      eapply PN.
      eapply f.
      * eassumption.
      * eapply WP ; try eassumption.
  - intros wl' tau Ninfl.
    unshelve eapply WP.
    4:{ eapply AllInLCon_le ; try eassumption.
        etransitivity.
        eapply (Max_Bar_Bar_lub _ _
                  (fun wl'0 tau0 Ninfl0 => PN wl'0 Q (f wl'0 tau0 (WP wl P p wl'0 tau0 Ninfl0)))).
        eapply Nat.le_max_r.
    }
    eapply Bar_lub_smaller.
    Unshelve.
    + eassumption.
    + eapply AllInLCon_le ; try eassumption.
      now eapply Nat.le_max_l.
    + now eapply Bar_lub_ub.
    + now eapply Bar_lub_AllInLCon.
Defined.      
