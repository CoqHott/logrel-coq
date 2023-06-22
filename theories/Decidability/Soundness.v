(** * LogRel.Decidability.Soundness: the implementations imply the inductive predicates. *)
From Coq Require Import Nat List Lia Arith ssrbool.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation TypeUniqueness.
From LogRel.Decidability Require Import Functions.
From PartialFun Require Import Monad PartialFun.

Import DeclarativeTypingProperties.
Import IndexedDefinitions.

Set Universe Polymorphism.


Lemma zip_ored t t' π : [t ⇒ t'] -> [zip t π ⇒ zip t' π].
Proof.
  intros Hred.
  induction π as [|[]] in t, t', Hred |- * ; cbn in *.
  1: eassumption.
  all: apply IHπ ; now econstructor.
Qed.

Lemma zip_red t t' π : [t ⇒* t'] -> [zip t π ⇒* zip t' π].
Proof.
  induction 1.
  1: reflexivity.
  econstructor ; tea.
  now eapply zip_ored.
Qed.

Section RedImplemSound.

Lemma compact_sound :
  funrect compact (fun '(t,_) => whne_list t)
    (fun '(t,π) t' => [zip t π ⇒* t'] × whne_list t').
Proof.
  intros ? ?.
  funelim (compact _).
  all: cbn ; try easy.
  - split.
    2: easy.
    assert (whne u) by eauto using whne_list_not_map.
    destruct s ; cbn.
    all: econstructor ; tea.
    all: now econstructor.
  - inversion H ; subst.
    2: now inversion H0.
    split.
    + now econstructor.
    + intros v [Hv].
      split ; tea.
      econstructor ; tea.
      eapply zip_ored.
      now econstructor.
Qed.

Lemma isType_tm_view1 t e :
  build_tm_view1 t = tm_view1_type e ->
  isType t × ~ whne t.
Proof.
  intros H.
  destruct e ; cbn.
  all: split ; [ now econstructor | intros H' ; inversion H'].
Qed.

Lemma whnf_tm_view1_nat t e :
  build_tm_view1 t = tm_view1_nat e ->
  whnf t × ~ whne t.
Proof.
  intros H.
  destruct e ; cbn.
  all: split ; [ now econstructor | intros H' ; inversion H'].
Qed.

Lemma whnf_tm_view1_list t e :
  build_tm_view1 t = tm_view1_list e ->
  whnf t × ~ whne t.
Proof.
  intros H.
  destruct e ; cbn.
  all: split ; [ now econstructor | intros H' ; inversion H'].
Qed.

Lemma red_stack_sound :
  funrect wh_red_stack (fun _ => True) (fun '(t,π) t' => [zip t π ⇒* t'] × whnf t').
Proof.
  intros ? Hty.
  funelim (wh_red_stack _).
  all: cbn; try split; try easy.
  all: match goal with | |- whnf _ => shelve | _ => idtac end.
  2: shelve.
  all: intros v [] ; split ; [..|eassumption].
  all: etransitivity ; [..|eassumption].
  all: eapply zip_red.
  1-7: econstructor ; [..|reflexivity] ; now econstructor.
  now destruct s ; cbn.
  Unshelve. 
  - eapply isType_tm_view1 in Heq as [].
    gen_typing.
  - now econstructor.
  - eapply funrect_graph in H ; cycle 1.
    + eapply compact_sound.
    + now do 2 econstructor.
    + cbn in *.
      now eapply whnf_whne_list.
  - now eapply whnf_tm_view1_nat.
  - econstructor.
  - now eapply whnf_tm_view1_list.
  - eapply funrect_graph in H ; cycle 1.
    + eapply compact_sound.
    + now do 2 econstructor.
    + now cbn in *.
Qed.

Corollary _red_sound :
  funrect wh_red (fun _ => True) (fun t t' => [t ⇒* t'] × whnf t').
Proof.
  intros ? Hty.
  funelim (wh_red _).
  cbn.
  intros ? H.
  eapply funrect_graph in H ; cycle 1.
  - apply red_stack_sound.
  - cbn.
    easy.
  - eassumption.
Qed.

(* Lemma can_red_stack :
  funrect wh_red_stack (fun '(c,π) => isCanonical c × π = [::]) (fun '(c,π) t => c = t).
Proof.
  intros ? Hcan.
  funelim (wh_red_stack _).
  all: cbn; try split; try easy.
  all: try solve [destruct Hcan as [] ; congruence].
  - destruct Hcan as [Hcan _].
    inversion Hcan.
  - destruct Hcan as [Hcan _].
    destruct s ; cbn in *.
    all: now inversion Hcan.
  - destruct Hcan as [Hcan _].
    destruct s ; cbn in *.
    all: now inversion Hcan.
Qed.

Lemma can_red c t :
  isCanonical c ->
  graph wh_red c t ->
  t = c.
Proof.
  intros Hcan Hgraph.
  enough (funrect wh_red (fun c => isCanonical c) (fun c t => c = t)).
  {
    eapply funrect_graph in Hgraph ; cycle 1 ; tea.
    cbn in *.
    now easy.
  }
  intros ? ?.
  funelim (wh_red _).
  cbn.
  intros ? Hgraph'.
  eapply funrect_graph in Hgraph' ; cycle 1.
  - eapply can_red_stack.
  - now split.
  - cbn in *.
    easy.
Qed. *)

#[universes(polymorphic)]Corollary red_sound t t' :
  graph wh_red t t' ->
  [t ⇒* t'] × whnf t'.
Proof.
  intros Hgraph.
  eapply funrect_graph in Hgraph ; cycle 1.
  + eapply _red_sound.
  + easy.
  + eassumption.
Qed.

End RedImplemSound.

Section CtxAccessCorrect.

  Lemma ctx_access_sound Γ n d :
    ctx_access Γ n = (ok d) ->
    in_ctx Γ n d.
  Proof.
    funelim (ctx_access Γ n).
    all: simp ctx_access ; cbn.
    - inversion 1.
    - inversion 1.
      now constructor.
    - destruct (ctx_access Γ n') ; cbn.
      all: inversion 1 ; subst.
      constructor.
      now apply H.
  Qed.

  Lemma ctx_access_complete Γ n d :
    in_ctx Γ n d ->
    ctx_access Γ n = ok d.
  Proof.
    induction 1.
    all: simp ctx_access ; cbn.
    - reflexivity.
    - now rewrite IHin_ctx. 
  Qed.

  Corollary ctx_access_correct Γ n d :
    in_ctx Γ n d <~> (ctx_access Γ n = ok d).
  Proof.
    split.
    - eapply ctx_access_complete.
    - eapply ctx_access_sound.
  Qed.

End CtxAccessCorrect.

Ltac funelim_conv :=
  funelim (conv _); 
    [ funelim (conv_ty _) | funelim (conv_ty_red _) | 
      funelim (conv_tm _) | funelim (conv_tm_red _) | 
      funelim (conv_ne _) | funelim (conv_ne_red _) |
      funelim (conv_ne_list _)].

Section ConversionSound.


  Lemma whnf_tm_view3_pos T m n :
    whnf T ->
    build_nf_view3 T m n = neutrals T m n ->
    isPosType T.
  Proof.
  intros [] ; simp build_nf_view3.
  all: try solve [congruence].
  - now econstructor.
  - now econstructor.
  - destruct (build_nf_view1 m), (build_nf_view1 n) ; cbn ; try solve [congruence].
    all: destruct l ; cbn ; try solve [congruence].
    all: destruct l0 ; cbn ; try solve [congruence].
  - now econstructor.
  - destruct (build_ty_view1 n0) ; cbn ; try solve [congruence].
    + destruct t0 ; cbn ; try solve [congruence].
      1-2: now econstructor.
      inversion w ; subst.
      inversion H.
    +  destruct n0.
      1: now do 2 econstructor.
      destruct s ; cbn in *.
      all: do 2 econstructor.
      all: inversion w ; subst ; now inversion H0.
  Qed.

  Import AlgorithmicTypingData.

  #[local]Existing Instance ty_errors.

  #[universes(polymorphic)]Definition conv_sound_type
    (x : conv_full_dom)
    (r : conv_full_cod x) : Type :=
  match x, r with
  | _, (error _) => True
  | (ty_state;Γ;_;T;V), (ok _) =>  [Γ |-[al] T ≅ V]
  | (ty_red_state;Γ;_;T;V), (ok _) => [Γ |-[al] T ≅h V]
  | (tm_state;Γ;A;t;u), (ok _) => [Γ |-[al] t ≅ u : A]
  | (tm_red_state;Γ;A;t;u), (ok _) => whnf t -> whnf u -> whnf A -> [Γ |-[al] t ≅h u : A]
  | (ne_state;Γ;_;m;n), (ok T) => [Γ |-[al] m ~ n ▹ T]
  | (ne_red_state;Γ;_;m;n), (ok T) => [Γ |-[al] m ~h n ▹ T] × whnf T
  | (ne_list_state;Γ;A;m;n), (ok _) => [Γ |-[al] m ~ n :List A]
  end.

  Lemma _implem_conv_sound :
    funrect conv (fun _ => True) conv_sound_type.
  Proof.
    intros x Hpre.
    funelim_conv ; cbn; try easy.
    all: intros ; simp conv_sound_type; cbn.
    all: match goal with
      | H : (_;_;_;_) = (_;_;_;_) |- _ => injection H; clear H; intros; subst 
    end.
    all: repeat match goal with
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
    end.
    all: unfold conv_full_cod, conv_cod.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : result _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => simp conv_sound_type ; intros ?
      | |- orec_ind_stepT _ _ _ (match ?t with | _ => _ end) =>
        destruct t; cbn; try easy
      | s : sort |- _ => destruct s
      end).
    all: try solve [now econstructor].
    - econstructor ; tea.
      now econstructor.
    - econstructor ; tea.
      now eapply whnf_tm_view3_pos.
    - eapply convne_meta_conv.
      2: reflexivity.
      + econstructor.
        now eapply ctx_access_correct.
      + f_equal.
        symmetry.
        now eapply Nat.eqb_eq.
    - match goal with
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      end.
      split; tea.
      now econstructor.
  Qed.

  Corollary implem_conv_sound x r :
    graph conv x r ->
    conv_sound_type x r.
  Proof.
    eapply funrect_graph.
    1: now apply _implem_conv_sound.
    easy.
  Qed.

End ConversionSound.

Ltac funelim_typing :=
  funelim (typing _); 
    [ funelim (typing_inf _) | 
      funelim (typing_check _) |
      funelim (typing_inf_red _) | 
      funelim (typing_wf_ty _) ].

Section TypingCorrect.

  Import AlgorithmicTypingData.

  #[local]Existing Instance ty_errors.

  Lemma ty_view1_small_can T n : build_ty_view1 T = ty_view1_small n -> ~ isCanonical T.
  Proof.
    destruct T ; cbn.
    all: inversion 1.
    all: inversion 1.
  Qed.

  #[universes(polymorphic)]Definition typing_sound_post
    (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term)
    (r : result (tstate_output x.π1)) : Type :=
  match x, r with
  | _, (error _) => True
  | (wf_ty_state;Γ;_;T), (ok _) => [Γ |-[al] T]
  | (inf_state;Γ;_;t), (ok T) => [Γ |-[al] t ▹ T]
  | (inf_red_state;Γ;_;t), (ok T) => [Γ |-[al] t ▹h T]
  | (check_state;Γ;T;t), (ok _) => [Γ |-[al] t ◃ T]
  end.


  Lemma _implem_typing_sound :
    funrect typing (fun _ => True) typing_sound_post.
  Proof.
    intros x ?.
    funelim_typing ; cbn.
    all: intros ; simp typing_sound_post ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- _ * _ => split ; [try easy ; shelve |..]
      | |- forall x : result _, _ => intros [|] ; simp typing_sound_post ; try easy ; cbn
      | |- _ -> _ => simp typing_sound_post ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; simp typing_sound_post ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => shelve
      | H : graph conv _ _ |- _ => shelve
      | H : ctx_access _ _ = _ |- _ => eapply ctx_access_correct in H
      | H : (build_ty_view1 _ = ty_view1_small _) |- _ => eapply ty_view1_small_can in H
      | H : (_;_;_) = (_;_;_) |- _ => injection H; clear H; intros; subst 
      end).
    all: now econstructor.
    Unshelve.
    - injection eqargs ; clear eqargs ; intros ; subst.
      eapply implem_conv_sound in H ; cbn in *.
      1: now econstructor.
    - injection eqargs ; clear eqargs ; intros ; subst.
      eapply red_sound in H as [].
      1: now econstructor.
  Qed.

  Lemma implem_typing_sound x r:
    graph typing x r ->
    typing_sound_post x r.
  Proof.
    eapply funrect_graph.
    1: now apply _implem_typing_sound.
    easy.
  Qed.

End TypingCorrect.