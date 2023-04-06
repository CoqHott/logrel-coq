Require Import ssreflect.
Require Import Coq.Arith.EqNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils.

Notation LCon := (list (prod nat bool)).

Inductive in_LCon : LCon -> nat -> bool -> Prop :=
| in_here_l (l : LCon) {n b} : in_LCon (cons (n,b) l) n b
| in_there_l {l : LCon} {n b d} : in_LCon l n b -> in_LCon (cons d l) n b.

Inductive not_in_LCon : LCon -> nat -> Prop :=
| not_in_nil : forall n, not_in_LCon nil n
| not_in_there : forall {l n m b}, n <> m -> not_in_LCon l n
                                 -> not_in_LCon (cons (m,b) l) n.

Inductive wf_LCon : LCon -> Prop :=
| wf_nil : wf_LCon nil
| wf_cons : forall {l n b}, wf_LCon l -> not_in_LCon l n -> wf_LCon (cons (n,b) l).

Definition le_LCon l l' : Prop :=
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
      exfalso ; exact (notinLConnotinLCon H H4).
    + inversion inl' ; subst.
      * exfalso ; exact (notinLConnotinLCon H H4).
      * exact (IHwfl H4 H5).
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

Definition LCon_le (l l' : LCon) : Prop := forall n b, in_LCon l' n b -> in_LCon l n b.

Definition wfLCon_le (l l' : wfLCon) : Prop :=
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
