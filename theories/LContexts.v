Require Import ssreflect.
Require Import Coq.Arith.EqNat PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils.

Notation LCon := (list (prod nat bool)).

Inductive in_LCon : LCon -> nat -> bool -> Prop :=
| in_here_l (l : LCon) {n b} : in_LCon (cons (n,b) l) n b
| in_there_l {l : LCon} {n b d} : in_LCon l n b -> in_LCon (cons d l) n b.


Inductive not_in_LCon : LCon -> nat -> Prop :=
| not_in_nil : forall n, not_in_LCon nil n
| not_in_there : forall {l n m b}, ((n = m) -> False) -> not_in_LCon l n
                                 -> not_in_LCon (cons (m,b) l) n.

Inductive wf_LCon : LCon -> Type :=
| wf_nil : wf_LCon nil
| wf_cons : forall {l n b}, wf_LCon l -> not_in_LCon l n -> wf_LCon (cons (n,b) l).




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

Fixpoint decidInLCon l n :
  (in_LCon l n true) + (in_LCon l n false) + (not_in_LCon l n).
Proof.
  unshelve refine (match l with
                   | nil => _
                   | cons (m, b) q => _
                   end).
  - right.
    now econstructor.
  - unshelve refine
      (match (decidInLCon q n) with
       | inl IHl => _
       | inr IHl => _
       end).
    + unshelve refine
      (match IHl with
       | inl IHl => _
       | inr IHl => _
       end).
      * left ; left ; now econstructor.
      * left ; right ; now econstructor.
    + case (eq_nat_decide n m).
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
Defined.
Print decidInLCon.
(*  induction l.
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
Defined.        *)
        
      
Definition wfLCons (l : wfLCon) {n : nat} (ne : not_in_LCon (pi1 l) n) (b : bool) : wfLCon.
Proof.
  exists (cons (n,b) (pi1 l)).
  econstructor ; trivial.
  exact (pi2 l).
Defined.

Definition wfLCons' (l : wfLCon) {n : nat} (d : (not_in_LCon (pi1 l) n) × bool) : wfLCon
  := let (ne,b) := d in wfLCons l ne b.

Notation " l ',,l' d " := (wfLCons' l d) (at level 20, d at next level).

Definition LCon_le (l l' : LCon) : Type :=
  forall n b, in_LCon l' n b -> in_LCon l n b.

Definition wfLCon_le (l l' : wfLCon) : Type :=
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

Definition AllInLCon (n : nat) (l : wfLCon) : Type :=
  forall (m : nat), m < n -> (in_LCon l m true) + (in_LCon l m false).


Axiom AllInLCon_Irrel : forall n wl (ne ne' : AllInLCon n wl), ne = ne'.
Axiom wfLCon_le_Irrel : forall wl wl' (ne ne' : wl' ≤ε wl), ne = ne'.


Lemma AllInLCon_le (n m : nat) (ninfm : n <= m) (l : wfLCon) :
  AllInLCon m l -> AllInLCon n l.
Proof.
  intros allinl k kinfm.
  unshelve refine (allinl k _).
  now eapply Nat.lt_le_trans.
Qed.

Lemma AllInLCon_S (n : nat) b l :
  AllInLCon n l -> in_LCon l n b -> AllInLCon (S n) l.
Proof.
  intros allinl ninl m minfSn.
  case (Compare_dec.le_lt_eq_dec m n).
  - now eapply Arith_prebase.lt_n_Sm_le.
  - intro minfn ; clear minfSn.
    now eapply allinl.
  - intro eq.
    rewrite eq.
    induction b.
    + now left.
    + now right.
Qed.
  

Fixpoint Lack_n (l : wfLCon) (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S k => match decidInLCon l k with
            | inl a => Lack_n l k
            | inr b => cons k (Lack_n l k)
           end
  end.
Print List.In.
Fixpoint In {A : Type} (a : A) (l : list A) {struct l} : Type :=
  match l with
  | nil => False
  | (b :: m)%list => (b = a) + In a m
  end.

Definition Incl {A : Type} (l l' : list A) : Type :=
  forall a : A, In a l -> In a l'.

Lemma Incl_nil {A} : forall (l : list A), Incl l nil -> l = nil.
Proof.
  intros.
  induction l.
  - reflexivity.
  - pose proof (t := X a (inl (eq_refl _))).
    now inversion t.
Qed.
  
Lemma Lack_n_notinLCon (n m : nat) (l : wfLCon) :
  In m (Lack_n l n) -> not_in_LCon l m.
Proof.
  revert m l.
  induction n.
  - intros.
    now exfalso.
  - intros.
    unfold Lack_n in X.
    destruct (decidInLCon l n) ; fold Lack_n in X.
    + cbn in *.
      now eapply IHn.
    + destruct X.
      * now rewrite <- e.
      * now eapply IHn.
Qed.

Lemma Lack_n_minfn (n m : nat) (l : wfLCon) :
  In m (Lack_n l n) -> m < n.
Proof.
  induction n.
  - intros ; exfalso.
    now inversion X.
  - intro inm.
    cbn in *.
    destruct (decidInLCon l n).
    + etransitivity.
      now eapply IHn.
      now eapply Nat.lt_succ_diag_r.
    + cbn in inm.
      destruct inm.
      * rewrite e.
        now eapply Nat.lt_succ_diag_r.
      * etransitivity.
        now eapply IHn.
        now eapply Nat.lt_succ_diag_r.
Qed.


Lemma notinLCon_Lack_n (n m : nat) (l : wfLCon) :
  m < n -> not_in_LCon l m -> In m (Lack_n l n).
Proof.
  induction n.
  - intros ; simpl.
    now inversion H.
  - intros ; simpl.
    destruct (Compare_dec.le_lt_eq_dec _ _  H).
    + eapply Arith_prebase.lt_S_n_stt in l0.
      destruct (decidInLCon l n).
      * now eapply IHn.
      * right.
        now eapply IHn.
    + injection e ; intros ; subst ; clear e.
      destruct (decidInLCon l n).
      * exfalso.
        destruct s ; now eapply notinLConnotinLCon.
      * left ; reflexivity.
Qed.
      
  
Print List.incl.
Lemma Lack_n_Lcon_le (n : nat) (l l' : wfLCon) :
  l' ≤ε l -> Incl (Lack_n l' n) (Lack_n l n).
Proof.
  intros f.
  induction n ; intros m inm.
  - now exfalso.
  - pose proof (Lack_n_minfn _ _ _ inm) as minfSn.
    pose proof (notinl' := Lack_n_notinLCon _ _ _ inm).
    eapply notinLCon_Lack_n ; try eassumption.
    destruct (decidInLCon l m) ; try assumption.
    exfalso.
    destruct s ; eapply notinLConnotinLCon ; try eassumption.
    all: now eapply f.
Qed.

Lemma Lack_n_le (n m : nat) (l : wfLCon) :
  n <= m -> Incl (Lack_n l n) (Lack_n l m).
Proof.
  intro ninfm.
  induction n.
  - intros k ink.
    inversion ink.
  - cbn.
    destruct (decidInLCon l n).
    + eapply IHn.
      now eapply Le.le_Sn_le_stt.
    + intros k ink.
      destruct ink.
      * subst.
        eapply notinLCon_Lack_n ; try assumption.
      * eapply IHn ; try assumption.
        now eapply Le.le_Sn_le_stt.
Qed.


    

Lemma Lack_n_Sn_eq (n m : nat) (l : wfLCon) (q : list nat) :
  Lack_n l (S n) = cons m q -> not_in_LCon l n ->  n = m.
Proof.
  revert m.
  induction n ; intros m Heq notinl.
  - cbn in *.
    destruct (decidInLCon l 0).
    + exfalso ; now inversion Heq.
    + now inversion Heq.
  - cbn in *.
    destruct (decidInLCon l (S n)).
    + destruct s ; exfalso ; eapply notinLConnotinLCon ; eassumption.
    + now inversion Heq.
Qed.

  
Lemma Lack_n_add (n m : nat) (l : wfLCon) (me : not_in_LCon l m)
  (q : list nat) (b : bool) :
  cons m q = Lack_n l n -> Lack_n (l ,,l (me, b)) n = q.
Proof.
  intros Heq.
  unfold Lack_n.
  revert q m me Heq.
  induction n ; intros.
  - exfalso.
    now inversion Heq.
  - fold Lack_n in *.
    pose proof (t:= Lack_n_Sn_eq _ _ _ _ (eq_sym Heq)).
    destruct l as [l wfl].
    cbn in *.
    remember (decidInLCon l n) as rem.
    destruct rem as [ [s | s] | s].
    + cbn in *.
      subst. now eapply IHn.
    + subst. now eapply IHn.
    + assert (forall (m : nat) (e : m = m), e = eq_refl _).
      * clear n l wfl b IHn q m me s Heqrem Heq t.
        refine (fix f m :=
                  match m as m0 return forall e : m0 = m0, e = eq_refl _ with
                | 0 => fun e => match e with
                         | eq_refl _ => eq_refl _
                       end
                  | S k => _
                  end).
        admit.
      * pose proof (t' := t s) ; clear t.
        subst.
        destruct eq_nat_decide.
        rewrite (H m (proj1 (eq_nat_is_eq m m) e)).
        cbn.
        destruct b.
        -- eapply IHn.
Admitted.     

  
Lemma Lack_nil_AllInLCon (n : nat) (l : wfLCon) :
  Lack_n l n = nil -> AllInLCon n l.
Proof.
  induction n.
  - intros eq0 m minf0.
    exfalso.
    now inversion minf0.
  - intro Hyp ; cbn in *.
    destruct (decidInLCon l n).
    + intros m minfn.
      case (Compare_dec.le_lt_eq_dec _ _ minfn).
      * intros hyp.
        eapply IHn.
        assumption.
        now eapply Arith_prebase.lt_S_n_stt.
      * intro eqSnm.
        injection eqSnm ; intros eqnm.
        now rewrite eqnm.
    + exfalso.
      now inversion Hyp.
Qed.

    
(*Fixpoint RemoveElt {l : LCon} {n b} (ne : in_LCon l n b) : LCon
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
Admitted.*)

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

Fixpoint Max_Bar_aux
  (wl : wfLCon) (n : nat) (q : list nat) :
  forall (e : q = Lack_n wl n)
         (P : forall wl', wl' ≤ε wl -> AllInLCon n wl' -> nat),
    nat.
Proof.
  revert wl.
  refine (match q with
          | nil => _
          | cons a q => _
          end) ; intros.
  - refine (P wl _ _).
    now eapply (idε).
    eapply Lack_nil_AllInLCon.
    now symmetry.
  - refine (max _ _).
    + unshelve eapply Max_Bar_aux.
      * unshelve eapply wfLCons ; [exact wl | exact a | | exact true].
        eapply Lack_n_notinLCon.
        rewrite <- e.
        now left.
      * exact n.
      * exact q.
      * symmetry.
        now eapply Lack_n_add.
      * intros * τ allinl.
        refine (P wl' _ allinl).
        unshelve eapply (_ •ε _).
        3: eapply LCon_le_step ; now eapply wfLCon_le_id.
        eassumption.
    + unshelve refine (Max_Bar_aux _ n q _ _).
      * unshelve eapply wfLCons ; [exact wl | exact a | | exact false].
        eapply Lack_n_notinLCon.
        rewrite <- e.
        now left.
      * symmetry.
        now eapply Lack_n_add.
      * intros * τ allinl.
        refine (P wl' _ allinl).
        eapply wfLCon_le_trans ; try eassumption.
        eapply LCon_le_step.
        now eapply wfLCon_le_id.
Defined.        

Definition Max_Bar (wl : wfLCon) (n : nat)
  (P: forall wl' : wfLCon, wl' ≤ε wl -> AllInLCon n wl' -> nat) : nat :=
  Max_Bar_aux wl n (Lack_n wl n) eq_refl P.

Lemma Max_Bar_aux_le (wl : wfLCon) (n : nat)
  (q : list nat)
  (e : q = Lack_n wl n)
  (P : forall wl' : wfLCon, wl' ≤ε wl -> AllInLCon n wl' -> nat)
  (Pe : forall (wl' wl'' : wfLCon)
               (τ : wl' ≤ε wl) (τ' : wl'' ≤ε wl),
      wl'' ≤ε wl' ->
      forall (ne : AllInLCon n wl') (ne' : AllInLCon n wl''),
        P wl'' τ' ne' <= P wl' τ ne)
  (wl' : wfLCon) (τ : wl' ≤ε wl) (ne : AllInLCon n wl') :
  P wl' τ ne <= Max_Bar_aux wl n q e P.
Proof.
  revert wl wl' ne e τ P Pe.
  induction q ; intros.
  - cbn.
    now eapply Pe.
  - cbn.
    edestruct (ne a).
    + unshelve eapply Lack_n_minfn.
      exact wl.
      rewrite <- e.
      now left.
    + etransitivity.
      2: now eapply Nat.max_lub_l.
      etransitivity.
      2:{ unshelve eapply IHq.
          * exact wl'.
          * eapply LCon_le_in_LCon ; eassumption. 
          * assumption.
          * intros.
            now eapply Pe.
      }
      eapply Pe.
      now eapply wfLCon_le_id.
    + etransitivity.
      2: now eapply Nat.max_lub_r.
      etransitivity.
      2:{ unshelve eapply IHq.
          * exact wl'.
          * eapply LCon_le_in_LCon ; eassumption. 
          * assumption.
          * intros.
            now eapply Pe.
      }
      eapply Pe.
      now eapply wfLCon_le_id.
Qed.

Lemma Max_Bar_le (wl : wfLCon) (n : nat)
  (P : forall wl' : wfLCon, wl' ≤ε wl -> AllInLCon n wl' -> nat)
  (Pe : forall (wl' wl'' : wfLCon)
               (τ : wl' ≤ε wl) (τ' : wl'' ≤ε wl),
      wl'' ≤ε wl' ->
      forall (ne : AllInLCon n wl') (ne' : AllInLCon n wl''),
        P wl'' τ' ne' <= P wl' τ ne)
  (wl' : wfLCon) (τ : wl' ≤ε wl) (ne : AllInLCon n wl') :
  P wl' τ ne <= Max_Bar wl n P.
Proof.
  unfold Max_Bar.
  now eapply Max_Bar_aux_le.
Qed.

Fixpoint Bar_lub_aux (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
         (Hyp : AllInLCon n wl')
         (q : list nat) :
  forall (e : q = Lack_n wl n), wfLCon.
Proof.
  refine (match q with
          | nil => _
          | cons a q' => _
          end).
  - exact (fun _ => wl).
  - intros e.
    assert (a < n).
    abstract (refine (Lack_n_minfn _ _ _ _) ;
              erewrite <- e ;
              now left).
    destruct (Hyp a H).
    + unshelve eapply Bar_lub_aux.
      * refine (wfLCons _ _ true).
        eapply Lack_n_notinLCon.
        erewrite <- e.
        now left.
      * exact wl'.
      * exact n.
      * exact q'.
      * now eapply LCon_le_in_LCon.
      * assumption.
      * symmetry.
        now eapply Lack_n_add.
    + unshelve eapply Bar_lub_aux.
      * refine (wfLCons _ _ false).
        eapply Lack_n_notinLCon.
        erewrite <- e.
        now left.
      * exact wl'.
      * exact n.
      * exact q'.
      * now eapply LCon_le_in_LCon.
      * assumption.
      * symmetry.
        now eapply Lack_n_add.
Defined.

Definition Bar_lub (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') : wfLCon.
Proof.
  eapply Bar_lub_aux ; try eassumption.
  reflexivity.
Defined.

Lemma Bar_lub_eq (wl wl' wl'' : wfLCon) (n : nat)
  (f : wl' ≤ε wl) (f' : wl'' ≤ε wl) (f'': wl'' ≤ε wl')
  (Hyp : AllInLCon n wl') (Hyp' : AllInLCon n wl'')
  (q : list nat) (e : q = Lack_n wl n) :
  (Bar_lub_aux wl wl'' n f' Hyp' q e) = (Bar_lub_aux wl wl' n f Hyp q e).
Proof.
  revert wl wl' wl'' f f' f'' Hyp Hyp' e.
  induction q ; intros.
  - reflexivity.
  - cbn.
    destruct (Hyp' a (Bar_lub_aux_subproof wl n a q e)). 
    + destruct (Hyp a (Bar_lub_aux_subproof wl n a q e)).
      * now eapply IHq.
      * exfalso.
        change (match true with | true => False | _ => True end).
        erewrite (uniqueinLCon _ i).
        2: now eapply f''.
        easy.
    + destruct (Hyp a (Bar_lub_aux_subproof wl n a q e)).
      * exfalso.
        change (match true with | true => False | _ => True end).
        erewrite <- (uniqueinLCon _ i).
        2: now eapply f''.
        easy.
      * now eapply IHq.
        Unshelve.
        all: now destruct wl''.
Qed.



Lemma Bar_lub_smaller_aux (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') (q : list nat) (e : q = Lack_n wl n):
  wl' ≤ε (Bar_lub_aux wl wl' n f Hyp q e).
Proof.
  revert wl f e.
  induction q ; intros.
  - assumption.
  - cbn.
    destruct (Hyp a (Bar_lub_aux_subproof wl n a q e)).
    + now eapply IHq.
    + now eapply IHq.
Qed.

Lemma Bar_lub_smaller (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') :
  wl' ≤ε (Bar_lub wl wl' n f Hyp).
Proof.
  unfold Bar_lub ; eapply Bar_lub_smaller_aux.
Qed.


Lemma Bar_lub_ub_aux (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') (q : list nat) (e : q = Lack_n wl n) :
  (Bar_lub_aux wl wl' n f Hyp q e) ≤ε wl.
Proof.
  revert wl f e.
  induction q ; intros.
  - now eapply wfLCon_le_id.
  - cbn.
    destruct (Hyp a (Bar_lub_aux_subproof wl n a q e)).
    + eapply wfLCon_le_trans.
      eapply IHq.
      eapply LCon_le_step.
      now eapply wfLCon_le_id.
    + eapply wfLCon_le_trans.
      eapply IHq.
      eapply LCon_le_step.
      now eapply wfLCon_le_id.
Qed.

Lemma Bar_lub_ub (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') :
  (Bar_lub wl wl' n f Hyp) ≤ε wl.
Proof.
  unfold Bar_lub ; eapply Bar_lub_ub_aux.
Qed.
  
Lemma Bar_lub_AllInLCon_aux (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') (q : list nat) (e : q = Lack_n wl n) :
  AllInLCon n (Bar_lub_aux wl wl' n f Hyp q e).
Proof.
  revert wl f e.
  induction q ; intros.
  - cbn.
    now eapply Lack_nil_AllInLCon.
  - cbn.
    destruct (Hyp a (Bar_lub_aux_subproof wl n a q e)).
    + now eapply IHq.
    + now eapply IHq.
Qed.

Lemma Bar_lub_AllInLCon
  (wl wl' : wfLCon) (n : nat) (f : wl' ≤ε wl)
  (Hyp : AllInLCon n wl') :
  AllInLCon n (Bar_lub wl wl' n f Hyp).
Proof.
  unfold Bar_lub ; eapply Bar_lub_AllInLCon_aux.
Qed.


Lemma Max_Bar_Bar_lub_aux (wl : wfLCon) (n : nat)
  (P : forall wl' : wfLCon, wl' ≤ε wl -> AllInLCon n wl' -> nat)
  (wl' : wfLCon) (τ : wl' ≤ε wl) (ne : AllInLCon n wl')
   q e f allinBar_lub :
  P (Bar_lub_aux wl wl' n τ ne q e) f allinBar_lub <= Max_Bar_aux wl n q e P.
Proof.
  revert wl P τ e f allinBar_lub.
  induction q ; intros.
  - cbn in *.
    erewrite (AllInLCon_Irrel _ _ allinBar_lub (Lack_nil_AllInLCon n wl (eq_sym e))).
    now erewrite (wfLCon_le_Irrel _ _ f (wfLCon_le_id _)).
  - cbn in *.
    destruct (ne a (Bar_lub_aux_subproof wl n a q e)).
    + etransitivity.
      2: { eapply Nat.max_lub_l.
           reflexivity.
      }
      etransitivity.
      2:{ unshelve eapply IHq.
          + now eapply LCon_le_in_LCon.
          + eapply Bar_lub_ub_aux.
          + eapply Bar_lub_AllInLCon_aux.
      }
      eapply Nat.eq_le_incl.
      unshelve erewrite (AllInLCon_Irrel _ _ allinBar_lub).
      2: erewrite (wfLCon_le_Irrel _ _ f).
      2: reflexivity.
    + etransitivity.
      2: { eapply Nat.max_lub_r.
           reflexivity.
      }
      etransitivity.
      2:{ unshelve eapply IHq.
          + now eapply LCon_le_in_LCon.
          + eapply Bar_lub_ub_aux.
          + eapply Bar_lub_AllInLCon_aux.
      }
      eapply Nat.eq_le_incl.
      erewrite (AllInLCon_Irrel _ _ allinBar_lub).
      erewrite (wfLCon_le_Irrel _ _ f).
      reflexivity.
Qed.      

Lemma Max_Bar_Bar_lub (wl : wfLCon) (n : nat)
  (P : forall wl' : wfLCon, wl' ≤ε wl -> AllInLCon n wl' -> nat)
  (wl' : wfLCon) (τ : wl' ≤ε wl) (ne : AllInLCon n wl')
  (f : Bar_lub wl wl' n τ ne ≤ε wl)
  (allinBar : AllInLCon n (Bar_lub wl wl' n τ ne)) :
  P (Bar_lub wl wl' n τ ne) f allinBar <= Max_Bar wl n P.
Proof.
  unfold Bar_lub ; unfold Max_Bar ; cbn.
  now eapply Max_Bar_Bar_lub_aux.
Qed.

