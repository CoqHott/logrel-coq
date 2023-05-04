(** * LogRel.Decidability.Soundness: the implementations imply the inductive predicates. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms Stacks.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation.
From LogRel.Decidability Require Import Functions.
From PartialFun Require Import Monad PartialFun.

Import DeclarativeTypingProperties.
Import IndexedDefinitions.

Set Universe Polymorphism.

Section RedImplemSound.

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

Lemma red_stack_sound :
  funrect wh_red_stack (fun _ => True) (fun '(t,π) t' => [zip t π ⇒* t']).
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; econstructor ; try eauto.
  all: intros v ?.
  all: etransitivity ; [..|eassumption].
  all: eapply zip_red.
  all: econstructor ; [..|reflexivity].
  all: now econstructor.
Qed.

Lemma red_stack_whnf :
funrect wh_red_stack (fun _ => True) (fun '(t,π) t' => whnf t').
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; try solve [constructor ; eauto].
  - now apply isType_whnf, isType_entry.
  - econstructor.
    eapply zip_whne.
    now econstructor.
  - now eapply isNat_whnf, isNat_entry.
Qed.

Corollary _red_sound :
  funrect wh_red (fun _ => True) (fun t t' => [t ⇒* t'] × whnf t').
Proof.
  intros ? _.
  funelim (wh_red _).
  cbn.
  intros ? H.
  split.
  - eapply funrect_graph in H.
    2: exact red_stack_sound. (* apply fails !? *)
    all: easy.
  - eapply funrect_graph in H.
    2: exact red_stack_whnf.
    all: easy.
Qed.

#[universes(polymorphic)]Corollary red_sound t t' :
  graph wh_red t t' ->
  [t ⇒* t'] × whnf t'.
Proof.
  intros H.
  eapply (funrect_graph wh_red _ _ _ _ _red_sound). (* weird universe inconsistency? *)
  1: easy.
  eassumption.
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
      funelim (conv_ne _) | funelim (conv_ne_red _) ].

Section ConversionSound.

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
  | (tm_red_state;Γ;A;t;u), (ok _) =>
      whnf A -> whnf t -> whnf u -> [Γ |-[al] t ≅h u : A]
  | (ne_state;Γ;_;m;n), (ok T) => [Γ |-[al] m ~ n ▹ T]
  | (ne_red_state;Γ;_;m;n), (ok T) => [Γ |-[al] m ~h n ▹ T] × whnf T
  end.

  Lemma _implem_conv_sound :
    funrect conv (fun _ => True) conv_sound_type.
  Proof.
    intros x _.
    funelim_conv ; cbn.
    all: intros ; simp conv_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : result _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => simp conv_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : (_;_;_;_) = (_;_;_;_) |- _ => injection H; clear H; intros; subst 
      end).
    all: try solve [now econstructor].
    - econstructor ; tea.
      now econstructor.
    - econstructor ; tea.
      destruct H ; simp build_nf_view3 build_ty_view1 in Heq ; try solve [inversion Heq].
      all: try now econstructor.
    - eapply convne_meta_conv.
      2: reflexivity.
      + econstructor.
        now eapply ctx_access_correct.
      + f_equal.
        symmetry.
        now eapply Nat.eqb_eq.
    - split; tea. now econstructor.
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

  #[universes(polymorphic)]Definition typing_sound_type
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
    funrect typing (fun _ => True) typing_sound_type.
  Proof.
    intros x _.
    funelim_typing ; cbn.
    all: intros ; simp typing_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : result _, _ => intros [|] ; simp typing_sound_type ; try easy ; cbn
      | |- _ -> _ => simp typing_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; simp typing_sound_type ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : graph conv _ _ |- _ => eapply implem_conv_sound in H ; simp conv_sound_type in H
      | H : ctx_access _ _ = _ |- _ => eapply ctx_access_correct in H
      | H : context [build_ty_view1] |- _ => clear H
      | H : ne_view1 _ |- _ => apply ne_view1_can in H
      | H : (_;_;_) = (_;_;_) |- _ => injection H; clear H; intros; subst 
      end).
    all: now econstructor.
  Qed.

  Lemma implem_typing_sound x r:
    graph typing x r ->
    typing_sound_type x r.
  Proof.
    eapply funrect_graph.
    1: now apply _implem_typing_sound.
    easy.
  Qed.

End TypingCorrect.