Require Import ssreflect.
Require Import Coq.Arith.EqNat PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils.

Notation LCon := (list (prod nat nat)).

Inductive in_LCon : LCon -> nat -> nat -> SProp :=
| in_here_l (l : LCon) {n b} : in_LCon (cons (n,b) l) n b
| in_there_l {l : LCon} {n b d} : in_LCon l n b -> in_LCon (cons d l) n b.


Inductive not_in_LCon : LCon -> nat -> SProp :=
| not_in_nil : forall n, not_in_LCon nil n
| not_in_there : forall {l n m b}, ((n = m) -> False) -> not_in_LCon l n
                                 -> not_in_LCon (cons (m,b) l) n.

Inductive wf_LCon : LCon -> SProp :=
| wf_nil : wf_LCon nil
| wf_cons : forall {l n b}, wf_LCon l -> not_in_LCon l n -> wf_LCon (cons (n,b) l).

Inductive SFalse : SProp := .

Inductive Sor (A B : SProp) : SProp :=  Sinl : A -> Sor A B | Sinr : B -> Sor A B.

Inductive Ssig (A : Type) (P : A -> SProp) : Type :=
  Sexist : forall x : A, P x -> Ssig A P.

Arguments Ssig [A]%type_scope P%type_scope.
Arguments Sexist [A]%type_scope P%function_scope x _.

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
  enough (H : SFalse) by inversion H.
  induction inl.
  - inversion notinl ; subst.
    easy.
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
  destruct (Nat.eq_dec b b') ; [assumption | ].
  enough (H : SFalse) by inversion H.
  revert inl inl' ; induction wfl ; intros.
  - now inversion inl.
  - inversion inl ; subst.
    + inversion inl' ; subst ; trivial.
      1: exfalso ; now eapply n0.
      exfalso.
      exact (notinLConnotinLCon n2 H3).
    + inversion inl' ; subst.
      * exfalso ; exact (notinLConnotinLCon n2 H3).
      * exact (IHwfl H3 H4).
Qed.

Inductive or_inLCon l n : Type :=
| or_inl : forall m, in_LCon l n m  -> or_inLCon l n
| or_notinl : not_in_LCon l n -> or_inLCon l n.
Arguments or_inl [_ _] _.
Arguments or_notinl [_ _] _.

Fixpoint decidInLCon l n : or_inLCon l n .
Proof.
  unshelve refine (match l with
                   | nil => _
                   | cons (m, b) q => _
                   end).
  - econstructor 2 ; now econstructor.
  - unshelve refine
      (match (decidInLCon q n) with
       | or_inl m H => _
       | or_notinl H => _
       end).
    + econstructor 1. now econstructor.
    + case (eq_nat_decide n m).
      * intro neqm.
        rewrite <- (proj1 (eq_nat_is_eq n m) neqm).
        econstructor 1 ; now econstructor.
      * intro noteq.
        econstructor 2.
        econstructor ; try assumption.
        intro neqm ; rewrite neqm in noteq.
        eapply noteq.
        exact (eq_nat_refl _).
Defined.

Lemma decidInLCon_true (l : wfLCon) n m (Hin: in_LCon l n m) :
  decidInLCon l n = or_inl m Hin.
Proof.
  destruct (decidInLCon l n).
  + assert (H := uniqueinLCon l.(pi2) Hin i) ; now subst. 
  + exfalso.
    now eapply notinLConnotinLCon.
Qed.

Lemma decidInLCon_notinLCon (l : wfLCon) n (Hin: not_in_LCon l n) :
  decidInLCon l n = or_notinl Hin.
Proof.
  destruct (decidInLCon l n).
  + exfalso.
    now eapply notinLConnotinLCon.
  + reflexivity. 
Qed.

Arguments decidInLCon_true [_ _] _.
Arguments decidInLCon_notinLCon [_ _] _.

      
Definition wfLCons (l : wfLCon) {n : nat} (ne : not_in_LCon (pi1 l) n) (b : nat) : wfLCon.
Proof.
  exists (cons (n,b) (pi1 l)).
  econstructor ; trivial.
  exact (pi2 l).
Defined.

Notation " l ',,l' ( ne , b ) " := (wfLCons l ne b) (at level 20, ne, b at next level).

Definition LCon_le (l l' : LCon) : SProp :=
  forall n b, in_LCon l' n b -> in_LCon l n b.

Definition wfLCon_le (l l' : wfLCon) : SProp :=
  LCon_le (pi1 l) (pi1 l').

Notation " l ≤ε l' " := (wfLCon_le l l') (at level 40).

Definition wfLCon_le_id l : l ≤ε l := fun n b ne => ne.

Notation " 'idε' " := (wfLCon_le_id) (at level 40).

Definition wfLCon_le_trans {l l' l''} : l ≤ε l' -> l' ≤ε l'' -> l ≤ε l'' :=
  fun f f' n b ne => f n b (f' n b ne).

Notation " a •ε b " := (wfLCon_le_trans a b) (at level 40).

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

Lemma not_in_LCon_le_not_in_LCon {l l' n} (ne : not_in_LCon (pi1 l') n) :
  l' ≤ε l -> not_in_LCon (pi1 l) n.
Proof.
  intros f ; destruct (decidInLCon l n) as [i | ] ; [.. | assumption].
  1: exfalso ; eapply notinLConnotinLCon ; eauto.
Qed.



    
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
  now erewrite Nat.max_0_r in H.
Qed.
