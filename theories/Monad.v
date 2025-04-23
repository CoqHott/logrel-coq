From LogRel.AutoSubst Require Import core unscoped Ast Extra.
Require Import PeanoNat.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening GenericTyping.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Definition Type_le_step (wl : wfLCon) (n : nat) (ne : not_in_LCon wl n) (b : nat)
  (P : forall wl', wl' ≤ε wl -> Type) : 
  forall wl', wl' ≤ε wl,,l (ne, b) -> Type :=
  fun wl' f => P wl' (wfLCon_le_trans f (LCon_le_step _ (wfLCon_le_id _))).
Arguments Type_le_step [_ _ _ _] _ [_] _.

Definition Pred_le_step (wl : wfLCon) (n : nat) (ne : not_in_LCon wl n) (b : nat)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)  :
  forall wl' (f : wl' ≤ε wl,,l (ne, b)), Type_le_step P f -> Type :=
  fun wl' f p => Q wl' (wfLCon_le_trans f (LCon_le_step _ (wfLCon_le_id _))) p.
Arguments Pred_le_step [_ _ _ _ _] _ [_] _.

Definition dPred_le_step (wl : wfLCon)
  (n : nat) (ne : not_in_LCon wl n) (b : nat)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> Type) :
  forall wl' (f : wl' ≤ε wl,,l (ne, b)) (p : Type_le_step P f), Pred_le_step Q f p -> Type :=
  fun wl' f p q => R wl' (wfLCon_le_trans f (LCon_le_step _ (wfLCon_le_id _))) p q.
Arguments dPred_le_step [_ _ _ _ _ _] _ [_] _.


Definition Type_le_down (wl wl' : wfLCon) (f: wl' ≤ε wl)
  (P : forall wl', wl' ≤ε wl -> Type) : 
  forall wl'', wl'' ≤ε wl' -> Type :=
  fun wl'' f' => P wl'' (wfLCon_le_trans f' f).
Arguments Type_le_down [_ _] _ _ [_] _.

Definition Pred_le_down (wl wl' : wfLCon) (f: wl' ≤ε wl)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)  :
  forall wl'' (f' : wl'' ≤ε wl'), Type_le_down f P f' -> Type :=
  fun wl'' f' p => Q wl'' (wfLCon_le_trans f' f) p.
Arguments Pred_le_down [_ _] _ [_] _ [_] _.

Definition dPred_le_down (wl wl' : wfLCon) (f: wl' ≤ε wl)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> Type) :
  forall wl'' (f' : wl'' ≤ε wl') (p : Type_le_down f P f'), Pred_le_down f Q f' p -> Type :=
  fun wl'' f' p q => R wl'' (wfLCon_le_trans f' f) p q.
Arguments dPred_le_down [_ _] _ [_ _] _ [_] _.

(*Inductive Dial@{i} (wl : wfLCon) (P : forall wl', wl' ≤ε wl -> Type@{i}) : Type@{i} :=
| eta : P wl (wfLCon_le_id _) -> Dial wl P
| ϝdig {n} {ne : not_in_LCon (pi1 wl) n} :
  Dial (wl ,,l (ne, true)) (Type_le_step P) ->
  Dial (wl ,,l (ne, false)) (Type_le_step P) ->
  Dial wl P.

Definition Dbind (wl : wfLCon) (P Q : forall wl', wl' ≤ε wl -> Type)
  (f : forall wl' (f : wl' ≤ε wl), P wl' f -> Dial wl' (Type_le_down f Q))
  (p : Dial wl P) : Dial wl Q.
Proof.
  induction p.
  - eapply f ; try eassumption.
  - unshelve eapply ϝdig.
    2: eassumption.
    + eapply IHp1.
      intros ; eapply f ; try eassumption.
    + eapply IHp2.
      intros ; eapply f ; try eassumption.
Qed.

Fixpoint BType (wl : wfLCon)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (p : Dial wl P) : Type :=
  match p with
  | eta _ _ x => Q wl (wfLCon_le_id _) x
  | ϝdig _ _ pt pf => prod (@BType _ _ (Pred_le_step Q) pt) (BType _ _ (Pred_le_step Q) pf)
  end.

Fixpoint dBType (wl : wfLCon) 
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f: wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> Type)
  (p : Dial wl P) :
  BType wl P Q p -> Type :=
  match p as p0 return BType _ _ _ p0 -> Type with
  | eta _ _ x => fun q => R wl (wfLCon_le_id _) x q
  | ϝdig _ _ pt pf => fun q => let (qt, qf) := q in
                               prod (dBType _ _ _ (dPred_le_step R) pt qt)
                                 (dBType _ _ _ (dPred_le_step R) pf qf)
  end.

Fixpoint dBType2 (wl : wfLCon) 
  (P : forall wl', wl' ≤ε wl -> Type)
  (Q : forall wl' (f : wl' ≤ε wl), P wl' f -> Type)
  (R : forall wl' (f : wl' ≤ε wl), P wl' f -> Type)
  (S : forall wl' (f : wl' ≤ε wl) (p : P wl' f), Q wl' f p -> R wl' f p -> Type)
  (p : Dial wl P) :
  BType wl P Q p -> BType wl P R p -> Type :=
  match p as p0 return BType _ _ _ p0 -> BType _ _ _ p0 -> Type with
  | eta _ _ x => fun q r => S wl (wfLCon_le_id _) x q r
  | ϝdig _ _ pt pf => fun q r => let (qt, qf) := q in
                                 let (rt, rf) := r in
                                 prod (dBType2 _ _ _ _
                                         (fun wl' f p q =>
                                            S wl' (f •ε (LCon_le_step _ (wfLCon_le_id _))) p q) pt qt rt)
                                      (dBType2 _ _ _ _
                                         (fun wl' f p q =>
                                            S wl' (f •ε (LCon_le_step _ (wfLCon_le_id _))) p q) pf qf rf)
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
*)
Inductive DTree (k : wfLCon) : Type :=
| leaf : DTree k
| ϝnode {n} {ne : not_in_LCon (pi1 k) n} :
  (forall m, DTree (k ,,l (ne, m))) ->
  DTree k.

Fixpoint DTree_bind (k : wfLCon) (F : forall k' (f : k' ≤ε k), DTree k')
  (d : DTree k) : DTree k.
Proof.
  refine (match d with
          | leaf _ => F k (wfLCon_le_id _)
          | @ϝnode _ n ne k => @ϝnode _ n ne _
          end).
  intros m ; unshelve eapply DTree_bind ; [ | now eapply k].
  intros k' f ; eapply F, wfLCon_le_trans ; [eassumption | ].
  now eapply LCon_le_step, wfLCon_le_id.
Defined.

Fixpoint DTree_Ltrans_down (k k' : wfLCon) (f : k' ≤ε k) (d : DTree k) : DTree k'.
Proof.
  refine (match d with
          | leaf _ => leaf _
          | @ϝnode _ n ne dt => _
          end).
  destruct (decidInLCon k' n) as [ m Hin | Hnotin].
  - refine (DTree_Ltrans_down (k,,l (ne, m)) k' _ (dt m)).
    now eapply LCon_le_in_LCon.
  - refine (@ϝnode _ n Hnotin _).
    + intros m ; unshelve eapply (DTree_Ltrans_down _ _ _ (dt m)).
      now eapply LCon_le_up.
Defined.

Fixpoint DTree_Ltrans_up (k k' : wfLCon) (f : k' ≤ε k) (d : DTree k') : DTree k.
Proof.
  unshelve refine (match d with
          | leaf _ => leaf _
          | @ϝnode _ n ne dt => @ϝnode _ n _ _
          end).
  - now eapply not_in_LCon_le_not_in_LCon.
  - intros m ; eapply DTree_Ltrans_up ; [ | exact (dt m)].
    now eapply LCon_le_up.
Defined.  



Fixpoint DTree_fusion (k : wfLCon) (d d' : DTree k) : DTree k.
Proof.
  refine (match d with
          | leaf _ => d'
          | @ϝnode _ n ne dt => @ϝnode _ n ne _
          end).
  - intros m ; refine (DTree_fusion _ (dt m) _).
    unshelve eapply (DTree_Ltrans_down _ _ _ d').
    eapply LCon_le_step ; now apply wfLCon_le_id.
Defined.


Fixpoint over_tree (k k' : wfLCon) (d : DTree k) : SProp :=
  match d with
  | leaf _ => k' ≤ε k
  | @ϝnode _ n ne kt =>
      match (decidInLCon k' n) with
      | or_inl m H => over_tree (k ,,l (ne, m)) k' (kt m)
      | or_notinl _ => SFalse
      end
  end.

(*Inductive over_tree (k k' : wfLCon) :
  DTree k -> SProp :=
| over_leaf : k' ≤ε k -> over_tree k k' (leaf k)
| over_nodeT {n} {ne : not_in_LCon (pi1 k) n} kt kf :
  in_LCon k' n true ->
  over_tree (k ,,l (ne, true)) k' kt ->
  over_tree k k' (ϝnode (ne := ne) k kt kf)
| over_nodeF {n} {ne : not_in_LCon (pi1 k) n} kt kf :
  in_LCon k' n false ->
  over_tree (k ,,l (ne, false)) k' kf ->
  over_tree k k' (ϝnode (ne := ne) k kt kf).
*)

Lemma over_tree_le {k k' d} : over_tree k k' d -> k' ≤ε k.
Proof.
  induction d as [ | k n ne kt IHt kf IHf] ; cbn ; intros H ; auto.
  destruct (decidInLCon k' n).
  - exact ((IHt _ H) •ε (LCon_le_step _ (wfLCon_le_id _))).
  - now inversion H.
Qed.

Lemma le_over_tree {k k' k'' d} : k'' ≤ε k' -> over_tree k k' d -> over_tree k k'' d.
Proof.
  induction d as [ | k n ne kt IHt kf IHf] ; cbn ; intros Hinf Hinf' ; auto.
  - now eapply wfLCon_le_trans.
  - destruct (decidInLCon k' n).
    + erewrite (decidInLCon_true _ (Hinf _ _ i)).
      now eapply IHt.
    + now inversion Hinf'.
Qed.
  

Lemma over_tree_Ltrans_down (k k' k'' : wfLCon) (f : k' ≤ε k) (d : DTree k) :
  over_tree k' k'' (DTree_Ltrans_down k k' f d) -> over_tree k k'' d.
Proof.
  intros Hyp ; assert (f' : k'' ≤ε k') by now eapply over_tree_le.
  revert k' k'' f f' Hyp ; induction d as [  | k n ne kt IHt ] ; cbn ; intros k' k'' f f' Hyp.
  - eapply wfLCon_le_trans ; eassumption.
  - destruct (decidInLCon k' n).
    + destruct (decidInLCon k'' n).
      * assert (H := uniqueinLCon k''.(pi2) (f' _ _ i) i0) ; subst.
        unshelve eapply IHt.
        4: eassumption.
        eassumption.
      * exfalso.
        eapply notinLConnotinLCon ; eauto.
    + cbn in * ; destruct (decidInLCon k'' n).
      * eapply IHt ; [ | eassumption].
        eapply wfLCon_le_trans ; [ eapply LCon_le_in_LCon ; eassumption | now eapply (idε _)].
      * assumption.
Qed.

Lemma Ltrans_down_over_tree (k k' k'' : wfLCon) (f : k' ≤ε k) (f' : k'' ≤ε k') (d : DTree k) :
  over_tree k k'' d -> over_tree k' k'' (DTree_Ltrans_down k k' f d).
Proof.
  revert k' k'' f f' ; induction d as [  | k n ne kt IHt kf IHf] ; intros * f' ; cbn.
  - now eauto.
  - destruct (decidInLCon k' n).
    + rewrite (decidInLCon_true _ (f' n _ i)) ; intros H.
      now eapply IHt.
    + cbn in *.
      destruct (decidInLCon k'' n) ; cbn ; intros H ; eauto.
      eapply IHt ; eauto.
      now eapply LCon_le_in_LCon ; eauto.
Qed.

Lemma over_tree_Ltrans_up {k k' k'' : wfLCon} (f : k' ≤ε k) (f' : k'' ≤ε k') (d : DTree k') :
  over_tree k k'' (DTree_Ltrans_up k k' f d) -> over_tree k' k'' d.
Proof.
  revert k k'' f f' ; induction d as [  | k n ne kt IHt kf IHf] ; cbn ; intros k' k'' f f' Hyp.
  - eassumption.
  - destruct (decidInLCon k'' n).
    + eapply IHt ; eauto.
      eapply LCon_le_in_LCon ; eassumption.
    + assumption.
Qed. 
  
      
Lemma over_tree_fusion_l k k' d d' :
  over_tree k k' (DTree_fusion k d d') ->
  over_tree k k' d.
Proof.
  revert d' ; induction d as [ | k n ne kt IHt kf IHf] ; intros d' Hov.
  - eapply over_tree_le ; eassumption.
  - cbn in * ; subst.
    destruct (decidInLCon k' n).
    + eapply IHt ; eassumption.
    + assumption.
Qed.


Lemma over_tree_fusion_r k k' d d' :
  over_tree k k' (DTree_fusion k d d') ->
  over_tree k k' d'.
Proof.
  revert d' ; induction d as [ | k n ne kt IHt kf IHf] ; intros d' Hov.
  - eassumption.
  - cbn in * ; subst.
    destruct (decidInLCon k' n).
    + eapply over_tree_Ltrans_down, IHt ; eassumption.
    + now inversion Hov.
Qed.

Arguments over_tree_fusion_l [_ _ _ _] _.
Arguments over_tree_fusion_r [_ _ _ _] _.

Fixpoint DTree_bind_over (k : wfLCon) (d : DTree k) :
  (forall k' (H : over_tree k k' d), DTree k') -> DTree k.
Proof.
  refine (match d with
          | leaf _ => fun F => _
          | @ϝnode _ n ne dt => fun F => _
          end).
  - now eapply F, wfLCon_le_id.
  - eapply (@ϝnode _ n ne).
    + intros m ; unshelve eapply DTree_bind_over ; [ exact (dt m) | ].
      intros k' f ; eapply F. cbn in *.
      now rewrite (@decidInLCon_true k' n _ (over_tree_le f _ _ (in_here_l _))).
Defined.

Lemma DTree_bind_over_over k k' d P :
  over_tree k k' (DTree_bind_over k d P) ->
  over_tree k k' d.
Proof.
  induction d ; cbn in * ; intros Hyp.
  - now eapply over_tree_le.
  - destruct (decidInLCon k' n) ; cbn in *.
    + eapply H.
      eassumption.
    + assumption.
Qed.

Fixpoint DTree_path (k k' : wfLCon) (d : DTree k) :
  over_tree k k' d -> wfLCon.
Proof.
  refine (match d with
          | leaf _ => fun H => k
          | @ϝnode _ n ne dt => _
          end).
  cbn in *.
  refine (match decidInLCon k' n with
          | or_inl m _ => _
          | or_notinl _ => _
          end).
  all: refine (fun H => _).
  1: exact (DTree_path _ _ _ H).
  now inversion H.
Defined.

Lemma DTree_path_le k k' d (Hover : over_tree k k' d) :
  (DTree_path k k' d Hover) ≤ε k.
Proof.
  induction d ; cbn.
  - now eapply wfLCon_le_id.
  - cbn in *.
    revert Hover ; destruct (decidInLCon k' n) ; intros Hover.
    + eapply wfLCon_le_trans ; [eapply H | ].
      now eapply LCon_le_step, wfLCon_le_id.
    + now destruct Hover.
Qed.
    
Fixpoint DTree_path_over k k' d :
  forall Hover : over_tree k k' d,
    over_tree k (DTree_path k k' d Hover) d.
Proof.
  refine (match d as d0 return
                forall Hover,
                  over_tree k (DTree_path k k' d0 Hover) d0
          with
          | leaf _ => fun Hover => _
          | @ϝnode _ n ne dt => _
          end).
  - now eapply wfLCon_le_id.
  - cbn in *.
     destruct (decidInLCon k' n) ; cbn in * ; intros Hover.
    + rewrite (decidInLCon_true _ (DTree_path_le _ k' (dt m) Hover _ _ (in_here_l _))).
      now eapply DTree_path_over.
    + now destruct Hover.
Defined.

Lemma DTree_path_inf k k' d Hover :
  k' ≤ε (DTree_path k k' d Hover).
Proof.
  induction d as [  | k n ne kt IHt] ; cbn in * ; [assumption | ].
  destruct (decidInLCon k' n) ; cbn in *.
  - now apply IHt.
  - now inversion Hover.
Qed.


Lemma DTree_bind_DTree_path (k k' : wfLCon) (d : DTree k)
  (P : forall k' (H : over_tree k k' d), DTree k')
  (Hover : over_tree k k' d)
  (Hover' : over_tree k k' (DTree_bind_over k d P)) :
  over_tree (DTree_path k k' d Hover) k' (P _ (DTree_path_over k k' d Hover)).
Proof.
  revert P Hover Hover'.
  induction d as [  | k n ne kt IHt kf IHf] ; cbn in * ; intros.
  - assumption.
  - destruct (decidInLCon k' n) ; cbn in *.
    + set (P' := fun (k' : wfLCon) (f : over_tree (k,,l (ne, m)) k' (kt m)) =>
                 P k'
                   (@eq_sind_r (or_inLCon k' n)
                      (@or_inl k' n _
                         (@over_tree_le (k,,l (ne, m)) k' (kt m) f n m (@in_here_l k n m)))
                      (fun o : or_inLCon k' n =>
                       match o with
                       | @or_inl _ _ m _ => over_tree (k,,l (ne, m)) k' (kt m)
                       | @or_notinl _ _ _ => SFalse
                       end) f (decidInLCon k' n)
                      (@decidInLCon_true k' n _
                         (@over_tree_le (k,,l (ne, m)) k' (kt m) f n m (@in_here_l k n m))))).
      now eapply (IHt _ P' Hover Hover').
    + now destruct Hover.
Qed.

      
Lemma split_to_over_tree 
  (P : wfLCon -> Type)
  (Pe : forall wl n (ne : not_in_LCon (pi1 wl) n),
      (forall m, P (wl ,,l (ne, m))) -> P wl)
  (wl : wfLCon)
  (d : DTree wl)
  (H : forall wl', over_tree wl wl' d -> P wl') : P wl. 
Proof.
  induction d.
  - apply H.
    now intros n b Hin.
  - apply (Pe _ n ne) ; intros m.
    + apply X.
      intros wl' Hover ; cbn in *.
      apply H.
      unshelve erewrite (decidInLCon_true _ _) ; [ |  | eassumption].
      apply (over_tree_le Hover) ; now constructor.
Qed.
(*
Lemma dsplit_to_over_tree (wl : wfLCon)
  (P : forall wl', wl' ≤ε wl -> Type)
  (Pe : forall wl' n (ne : not_in_LCon (pi1 wl') n) f ft,
      (forall m, P (wl' ,,l (ne, m)) (ft m)) -> P wl' f)
  (d : DTree wl)
  (H : forall wl' f, over_tree wl wl' d -> P wl' f) : P wl (idε _). 
Proof.
  enough (Hyp : forall wl' f, P wl' f) by apply Hyp.
  revert P Pe H.
  induction d ; intros P Pe H wl' f.
  - now apply H.
  - cbn in *.
    


    
    destruct (decidInLCon wl' n).
    + pose proof (Hinf := LCon_le_step (l := k) (b := m) ne (wfLCon_le_id _)).
      specialize (X _ (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
      cbn in *.
      assert (Hinf' : wl' ≤ε (k,,l (ne, m))).
      { now eapply LCon_le_in_LCon. }
      change (P wl' (Hinf' •ε Hinf)).
      eapply X.
      * intros wl'' n' ne' f' ft Hm.
        apply H ; cbn.
        unshelve erewrite (decidInLCon_true _ _) ; [ | now eapply f' ; econstructor| ].
        eapply ft.
        2: now eapply f; econstructor.
    + pose proof (Hinf := LCon_le_step (l := k) (b := false) ne (wfLCon_le_id _)).
      specialize (IHd2 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
      cbn in *.
      assert (Hinf' : wl' ≤ε (k,,l (ne, false))).
      { now eapply LCon_le_in_LCon. }
      change (P wl' (Hinf' •ε Hinf)).
      eapply IHd2.
      * intros ; eauto.
      * intros wl'' f' Hover.
        apply H ; cbn.
        unshelve erewrite (decidInLCon_false _) ; [ | assumption].
        now eapply f'; econstructor.
    + unshelve eapply (Pe _ _ n0).
      1,2: now eapply wfLCon_le_trans ; [ eapply LCon_le_step | eapply (idε _)].
      * pose proof (Hinf := LCon_le_step (l := k) (b := true) ne (wfLCon_le_id _)).
        specialize (IHd1 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
        cbn in *.
        pose proof (Hinf' := LCon_le_up (b := true) ne n0 f).
        change (P (wl',,l (n0, true)) (Hinf' •ε Hinf)).
        eapply IHd1 ; [now eauto |..].
        intros wl'' f' Hover.
        eapply H.
        unshelve erewrite (decidInLCon_true _) ; [ | assumption].
        now eapply f'; econstructor.
      * pose proof (Hinf := LCon_le_step (l := k) (b := false) ne (wfLCon_le_id _)).
        specialize (IHd2 (fun wl' f => P wl' (wfLCon_le_trans f Hinf))).
        cbn in *.
        pose proof (Hinf' := LCon_le_up (b := false) ne n0 f).
        change (P (wl',,l (n0, false)) (Hinf' •ε Hinf)).
        eapply IHd2 ; [now eauto |..].
        intros wl'' f' Hover.
        eapply H.
        unshelve erewrite (decidInLCon_false _) ; [ | assumption].
        now eapply f'; econstructor.
Qed.        
*)
Section Typing.

  Context `{GenericTypingProperties}.
  
  Lemma wfc_over_tree {wl Γ} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [ |- Γ ]< wl' >) ->
    [ |- Γ ]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht ; now eapply (wfc_ϝ Ht).
  Qed.

  Lemma wft_over_tree {wl Γ A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [ Γ |- A ]< wl' >) ->
    [ Γ |- A ]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht ; now eapply (wft_ϝ Ht).
  Qed.
  
  Lemma ty_over_tree {wl Γ t A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- t : A]< wl' >) ->
    [Γ |- t : A]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht ; now eapply (ty_ϝ Ht).
  Qed.

  Lemma convty_over_tree {wl Γ A B} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- A ≅ B]< wl' >) ->
    [Γ |- A ≅ B]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht ; now eapply (convty_ϝ Ht).
  Qed.

  Lemma convtm_over_tree {wl Γ t u A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- t ≅ u : A]< wl' >) ->
    [Γ |- t ≅ u : A]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht; now eapply (convtm_ϝ Ht).
  Qed.

  Lemma convneu_over_tree {wl Γ t u A} (d : DTree wl) :
    (forall wl', over_tree wl wl' d -> [Γ |- t ~ u : A]< wl' >) ->
    [Γ |-  t ~ u : A]< wl >.
  Proof.
    apply split_to_over_tree.
    intros * Ht ; now eapply (convneu_ϝ Ht).
  Qed.

End Typing.


