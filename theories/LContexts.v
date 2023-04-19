Require Import ssreflect.
Require Import Coq.Arith.EqNat PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils.

Notation LCon := (list (prod nat bool)).

Inductive in_LCon : LCon -> nat -> bool -> Type :=
| in_here_l (l : LCon) {n b} : in_LCon (cons (n,b) l) n b
| in_there_l {l : LCon} {n b d} : in_LCon l n b -> in_LCon (cons d l) n b.

Inductive not_in_LCon : LCon -> nat -> Type :=
| not_in_nil : forall n, not_in_LCon nil n
| not_in_there : forall {l n m b}, n <> m -> not_in_LCon l n
                                 -> not_in_LCon (cons (m,b) l) n.

Inductive wf_LCon : LCon -> Type :=
| wf_nil : wf_LCon nil
| wf_cons : forall {l n b}, wf_LCon l -> not_in_LCon l n -> wf_LCon (cons (n,b) l).

Definition le_LCon l l' : Type :=
  forall n b, in_LCon l n b -> in_LCon l' n b.

Definition le_LCon_refl l : le_LCon l l := fun n b ne => ne.

Definition le_LCon_trans {l l' l''} :
  le_LCon l l' -> le_LCon l' l'' -> le_LCon l l'' :=
  fun le le' n b ne => le' n b (le n b ne).



Fixpoint nSucc (n : nat) (t : term) : term :=
  match n with
  | 0 => t
  | S n => tSucc (nSucc n t)
  end.

Definition nat_to_term (n : nat) : term := nSucc n tZero.


Definition bool_to_term (b : bool) : term :=
  match b with
  | true => tTrue
  | false => tFalse
  end.

Record wfLCon :=
  {pi1 : LCon ; pi2 : wf_LCon pi1}.

Coercion pi1 : wfLCon >-> LCon.

Lemma notinLConnotinLCon {l n b} : not_in_LCon l n -> in_LCon l n b -> False.
Proof.
  intros notinl inl.
  induction inl.
  - inversion notinl ; subst.
    now apply H3.
  - eapply IHinl.
    now inversion notinl ; subst.
Qed.

Lemma nattoterminj {n m} : nat_to_term n = nat_to_term m -> n = m.
Proof.
  revert m.
  induction n ; cbn in *.
  - induction m ; try reflexivity ; cbn.
    intro H.
    exfalso.
    change (match tZero as t0 return Type with
            | tZero => False
            | _ => True
            end).
    now rewrite H.
  - intros m H.
    induction m ; cbn in *.
    + exfalso.
      change (match tZero as t0 return Type with
              | tZero => False
              | _ => True
              end).
      now rewrite <- H.
    + erewrite (IHn m) ; try reflexivity.
      now inversion H.
Qed.

Lemma uniqueinLCon {l n b b'} : wf_LCon l -> in_LCon l n b -> in_LCon l n b' -> b = b'.
Proof.
  intros wfl inl inl'.
  induction wfl.
  - now inversion inl.
  - inversion inl ; subst.
    + inversion inl' ; subst ; trivial.
      exfalso.
      exact (notinLConnotinLCon n1 H3).
    + inversion inl' ; subst.
      * exfalso ; exact (notinLConnotinLCon n1 H3).
      * exact (IHwfl H3 H4).
Qed.

Lemma decidInLCon l n : (in_LCon l n true) + (in_LCon l n false) + (not_in_LCon l n).
Proof.
  induction l.
  - right.
    now econstructor.
  - induction IHl as [IHl | IHl ].
    + induction IHl as [IHl | IHl].
      * left ; left ; now econstructor.
      * left ; right ; now econstructor.
    + destruct a as [m b].
      case (eq_nat_decide n m).
      * intro neqm.
        rewrite <- (proj1 (eq_nat_is_eq n m) neqm).
        case b.
        -- left ; left ; now econstructor.
        -- left ; right ; now econstructor.
      * intro noteq.
        right.
        econstructor ; try assumption.
        intro neqm ; rewrite neqm in noteq.
        eapply noteq.
        exact (eq_nat_refl _).
Qed.        
        
      
Definition wfLCons (l : wfLCon) {n : nat} (ne : not_in_LCon (pi1 l) n) (b : bool) : wfLCon.
Proof.
  exists (cons (n,b) (pi1 l)).
  econstructor ; trivial.
  exact (pi2 l).
Defined.

Definition wfLCons' (l : wfLCon) {n : nat} (d : (not_in_LCon (pi1 l) n) × bool) : wfLCon
  := let (ne,b) := d in wfLCons l ne b.

Notation " l ',,l' d " := (wfLCons' l d) (at level 20, d at next level).

Definition LCon_le (l l' : LCon) : Type := forall n b, in_LCon l' n b -> in_LCon l n b.

Definition wfLCon_le (l l' : wfLCon) : Type :=
  LCon_le (pi1 l) (pi1 l').

Notation " l ≤ε l' " := (wfLCon_le l l') (at level 40).

Definition wfLCon_le_id l : l ≤ε l := fun n b ne => ne.

Definition wfLCon_le_trans {l l' l''} : l ≤ε l' -> l' ≤ε l'' -> l ≤ε l'' :=
  fun f f' n b ne => f n b (f' n b ne).

Lemma LCon_le_in_LCon {l l' n b} {ne : not_in_LCon (pi1 l') n} :
  l ≤ε l' -> in_LCon l n b -> l ≤ε (l' ,,l (ne , b)).
Proof.
  intros f inl m b' inl'.
  destruct l as [l wfl] ; destruct l' as [l' wfl'] ; cbn in *.
  unfold wfLCon_le in f ; cbn in f.
  clear wfl wfl'.
  inversion inl' ; subst.
  - assumption.
  - now apply f.
Qed.

Lemma LCon_le_step {l l' n b} (ne : not_in_LCon (pi1 l') n) :
  l' ≤ε l -> l' ,,l (ne , b) ≤ε l.
Proof.
  intros f m b' inl.
  apply in_there_l ; now eapply (f m b').
Qed.
  
Lemma LCon_le_up {l l' n b} (ne : not_in_LCon (pi1 l) n) (ne' : not_in_LCon (pi1 l') n) :
  l' ≤ε l -> l' ,,l (ne' , b) ≤ε (l ,,l (ne , b)).
Proof.
  intros f m b' inl.
  eapply LCon_le_in_LCon.
  - now eapply LCon_le_step.
  - now eapply in_here_l.
  - exact inl.
Qed.


Fixpoint RemoveElt {l : LCon} {n b} (ne : in_LCon l n b) : LCon
  := match ne with
     | in_here_l l => l
     | @in_there_l l n b d ne => cons d (RemoveElt ne)
     end.

Lemma Remove_notinLCon {l : LCon} {n m b} (ne : in_LCon l n b) (me : not_in_LCon l m) :
  not_in_LCon (RemoveElt ne) m.
Proof.
  induction ne.
  - cbn in *.
    now inversion me.
  - destruct d ; cbn in *.
    inversion me ; subst.
    econstructor.
    + assumption.
    + now apply IHne.
Qed.

Definition wf_RemoveElt {l : wfLCon} {n b} (ne : in_LCon l n b) : wfLCon.
Proof.
  exists (RemoveElt ne).
  destruct l as [l wfl] ; cbn in *.
  induction ne.
  - now inversion wfl.
  - cbn.
    destruct d.
    econstructor.
    + eapply IHne.
      now inversion wfl.
    + eapply Remove_notinLCon.
      now inversion wfl.
Defined.

Lemma RemoveElt_le {l l' n b} (f : l' ≤ε l) (ne : in_LCon l n b) :
  (wf_RemoveElt (f n b ne))  ≤ε (wf_RemoveElt ne).
Proof.
Admitted.
  
Lemma LCon_le_le {l l'} :  l' ≤ε l -> length l <= length l'.
Proof.
  intro f.
  destruct l as [l wfl] ; cbn in *.
  revert l' f.
  induction wfl ; intros.
  - now eapply le_0_n.
  -
Admitted.

Fixpoint LCon_newElt (l : LCon) : nat :=
  match l with
  | nil => 0
  | cons (n , b) q => max (LCon_newElt q) (S n)
  end.

Lemma newElt_newElt_aux (l : LCon) (n : nat) :
  not_in_LCon l (max (LCon_newElt l) n).
Proof.
  revert n.
  induction l as [ | [n b]] ; intros.
  - constructor.
  - cbn.
    econstructor.
    + eapply Nat.neq_sym.
      eapply Nat.lt_neq.
      eapply Nat.lt_le_trans.
      eapply Nat.lt_succ_diag_r.
      etransitivity ; [eapply Nat.le_max_r |..] ; now eapply Nat.le_max_l.
    + now erewrite <- Nat.max_assoc.
Qed.

Lemma newElt_newElt (l : LCon) (n : nat) :
  not_in_LCon l (LCon_newElt l).
Proof.
  pose proof (newElt_newElt_aux l 0).
  now rewrite Nat.max_0_r in H.
Qed.
