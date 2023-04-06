(** * LogRel.Decidability.Soundness: the implementations imply the inductive predicates. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation.
From LogRel.Decidability Require Import Functions.
From PartialFun Require Import Monad PartialFun.

Import DeclarativeTypingProperties.

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

Lemma stack_ne n π :
  whne n -> whne (zip n π).
Proof.
  intros Hne.
  induction π as [|[]] in n, Hne |- * ; cbn.
  1: eassumption.
  all: eapply IHπ ; now econstructor.
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

Lemma red_stack_whnf :
funrect wh_red_stack (fun _ => True) (fun '(t,π) t' => whnf t').
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; try solve [constructor ; eauto]. 
  - now eapply isType_whnf, isType_tm_view1.
  - econstructor. eapply stack_ne.
    now econstructor.
  - now eapply whnf_tm_view1_nat.
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

  #[universes(polymorphic)]Lemma ctx_access_sound :
    funrect ctx_access (fun _ => True) (fun '(Γ,n) d => in_ctx Γ n d).
  Proof.
    intros ? _.
    funelim (ctx_access _) ; cbn.
    - easy.
    - now econstructor.
    - split ; try easy.
      intros.
      now econstructor.
  Qed.

  #[universes(polymorphic)]Lemma ctx_access_complete Γ n d :
    in_ctx Γ n d ->
    graph ctx_access (Γ,n) d.
  Proof.
    induction 1.
    all: unfold graph ; simp ctx_access ; econstructor ; cbn.
    1: eassumption.
    econstructor.
  Qed.

  Corollary ctx_access_correct Γ n d :
    in_ctx Γ n d <~> graph ctx_access (Γ,n) d.
  Proof.
    split.
    - eapply ctx_access_complete.
    - intros.
      eapply (funrect_graph ctx_access (fun _ => True) (fun '(Γ,n) d => _) (Γ,n) d).
      1: eapply ctx_access_sound.
      all: easy.
  Qed.

End CtxAccessCorrect.

Section ConversionSound.

  Import AlgorithmicTypingData.

  #[local]Existing Instance ty_errors.

  #[universes(polymorphic)]Definition conv_sound_type
    (x : ∑ (c : conv_state) (_ : context) (_ : cstate_input c) (_ : term), term)
    (r : result (cstate_output x.π1)) : Type :=
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
    funelim (conv _) ; cbn.
    all: intros ; simp conv_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : result _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => simp conv_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      end).
    all: try solve [now econstructor].
    - econstructor ; tea.
      now econstructor.
    - econstructor ; tea.
      now econstructor.
    - econstructor ; tea.
      prod_hyp_splitter.
      destruct H0 ; simp build_nf_view3 in Heq ; try solve [inversion Heq].
      all: now econstructor.
    - eapply convne_meta_conv.
      2: reflexivity.
      + econstructor.
        now eapply ctx_access_correct.
      + f_equal.
        symmetry.
        now eapply Nat.eqb_eq.
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

Section TypingCorrect.

  Import AlgorithmicTypingData.

  #[local]Existing Instance ty_errors.

  Lemma ty_view1_small_can T n : build_ty_view1 T = ty_view1_small n -> ~ isCanonical T.
  Proof.
    destruct T ; cbn.
    all: inversion 1.
    all: inversion 1.
  Qed.

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

  Lemma implem_typing_sound :
    funrect typing (fun _ => True) typing_sound_type.
  Proof.
    intros x _.
    funelim (typing _) ; cbn.
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
      | H : graph ctx_access _ _ |- _ => eapply ctx_access_correct in H
      | H : (build_ty_view1 _ = ty_view1_small _) |- _ => eapply ty_view1_small_can in H
      end).
    all: now econstructor.
  Qed.

End TypingCorrect.