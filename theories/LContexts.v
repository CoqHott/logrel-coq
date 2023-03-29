Require Import ssreflect.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.

Inductive SFalse : SProp := .

Definition LCon := list (prod nat bool).

Inductive in_LCon : LCon -> nat -> bool -> Prop :=
| in_here (l : LCon) {d b} : in_LCon (cons (d,b) l) d b
| in_there {l : LCon} {d b d' b'} : in_LCon l d b -> in_LCon (cons (d',b') l) d b.

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

Fixpoint nat_to_term (n : nat) : term :=
  match n with
  | 0 => tZero
  | S n => tSucc (nat_to_term n)
  end.

Definition bool_to_term (b : bool) : term :=
  match b with
  | true => tTrue
  | false => tFalse
  end.

Record SsigT (A : Type) (B : A -> Prop) :=
  exist {fst : A ; snd : B fst}.
Arguments fst [_ _] _.
Arguments snd [_ _] _.

Definition wfLCon := SsigT LCon wf_LCon.

Lemma notinLConnotinLCon {l n b} : not_in_LCon l n -> in_LCon l n b -> False.
Proof.
  intros notinl inl.
  eapply SFalse_ind.
  induction inl.
  - inversion notinl ; subst.
    eapply False_sind.
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
      exfalso ; exact (notinLConnotinLCon H H5).
    + inversion inl' ; subst.
      * exfalso ; exact (notinLConnotinLCon H H5).
      * exact (IHwfl H5 H6).
Qed.
