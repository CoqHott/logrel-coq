From LogRel.AutoSubst Require Import core unscoped Ast Extra.
Require Import PeanoNat.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening GenericTyping.

Record Psh (wl : wfLCon) :=
  { typ : forall wl',  wl' ≤ε wl -> Type ;
    mon : forall wl' wl''  (alpha : wl' ≤ε wl) (beta : wl'' ≤ε wl')
    (delta : wl'' ≤ε wl),
      typ wl' alpha -> typ wl'' delta
  }.

Arguments typ [_] _.
Arguments mon [_ _ _] _.

Record Weak (wl : wfLCon) (P : forall wl', wl' ≤ε wl  -> Type) : Type :=
  { PN : nat ;
    WP : forall (wl' : wfLCon) (alpha : wl' ≤ε wl),
      AllInLCon PN wl' -> P wl' alpha ;
  }.


Lemma monot (wl wl' wl'' : wfLCon)
  (P : forall wl',  wl' ≤ε wl -> Type)
  (alpha :  wl' ≤ε wl)
  (beta :  wl'' ≤ε wl') :
  Weak wl' (fun wl'' dzeta => P wl'' (dzeta •ε alpha)) ->
  Weak wl'' (fun wl''' dzeta => P wl''' ((dzeta •ε beta) •ε alpha)).
Proof.
  intros [N WN].
  exists N.
  intros wl''' dzeta allinl.
  exact (WN wl''' (dzeta •ε beta) allinl).
Qed.  


Definition Wbind (wl : wfLCon) (P Q : forall wl', wl' ≤ε wl  -> Type)
  (Pe : forall wl' (alpha : wl' ≤ε wl) wl'' (beta : wl'' ≤ε wl),
      wl'' ≤ε wl' -> P wl' alpha -> P wl'' beta)
  (Qe : forall wl' (alpha : wl' ≤ε wl) wl'' (beta : wl'' ≤ε wl),
      wl'' ≤ε wl' -> Q wl' alpha -> Q wl'' beta)
  (f : forall wl' (alpha : wl' ≤ε wl),
      P wl' alpha -> Weak wl' (fun wl'' beta => Q wl'' (beta •ε alpha))) :
  forall wl' (alpha : wl' ≤ε wl),
    Weak wl' (fun wl'' beta => P wl'' (beta •ε alpha)) ->
    Weak wl' (fun wl'' beta => Q wl'' (beta •ε alpha)).
Proof.
  intros * [N W].
  unshelve econstructor.
  { unshelve eapply (max N _).
    unshelve eapply Max_Bar.
    - exact wl'.
    - exact N.
    - intros wl'' beta allinl.
      unshelve eapply (f wl'' (beta •ε alpha)).
      now eapply W.
  }
  intros wl'' beta allinl.
  unshelve eapply Qe.
  4: unshelve eapply f.
  { unshelve eapply (Bar_lub (Bar_lub wl' wl'' N beta _) wl'').
    3: now eapply Bar_lub_smaller.
    3: eassumption.
    eapply AllInLCon_le.
    eapply Nat.le_max_l.
    eassumption.
  }
  + unshelve eapply Bar_lub_smaller.
  + eapply (Bar_lub wl' wl'' N beta _).
  + now eapply Bar_lub_ub.
  + unshelve eapply (_ •ε alpha).
    now eapply Bar_lub_ub.
  + eapply W.
    now eapply Bar_lub_AllInLCon.
  + eapply AllInLCon_le ; [ | now eapply Bar_lub_AllInLCon].
    etransitivity ; [ |now eapply Nat.le_max_r].
    etransitivity ; [ | now eapply Max_Bar_Bar_lub].
    cbn.
    reflexivity.
Qed.    


Definition Wret (wl : wfLCon) (P : forall wl', wl' ≤ε wl  -> Type)
  (Pe : forall wl' (alpha : wl' ≤ε wl) wl'' (beta : wl'' ≤ε wl),
      wl'' ≤ε wl' -> P wl' alpha -> P wl'' beta)
  (p : P wl (idε wl)) : Weak wl P.
Proof.
  unshelve econstructor.
  - exact 0.
  - intros ; now eapply Pe.
Defined.


(*
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
*)
