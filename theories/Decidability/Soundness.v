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

Equations Derive NoConfusion Subterm for term.

Section RedImplemComplete.

  #[local]Definition R_aux := lexprod term term cored term_subterm.

  #[local]Definition R (t u : term × stack) :=
    R_aux (Datatypes.pair (zip (fst t) (snd t)) (fst t)) (Datatypes.pair (zip (fst u) (snd u)) (fst u)).

  #[local]Lemma R_acc t π :
    Acc cored (zip t π) ->
    Acc R (t, π).
  Proof.
  intros h.
  eapply acc_A_B_lexprod with (leA := cored) (leB := term_subterm) (y := t) in h.
  - remember (Datatypes.pair (zip t π) t) as z eqn:e.
    induction h as [z h ih] in t, π, e |- *. subst.
    constructor. intros [v ρ] hr.
    unfold R, R_aux in hr ; cbn in *.
    eapply ih. 2: reflexivity.
    assumption.
  - eapply well_founded_term_subterm.
  - eapply well_founded_term_subterm.
  Qed.

  #[local] Lemma well_typed_acc Γ t π :
    well_typed Γ (zip t π) ->
    Acc R (t,π).
  Proof.
    intros.
    now eapply R_acc, typing_SN.
  Qed.

  Lemma well_typed_zip Γ t π :
    well_typed Γ (zip t π) ->
    ∑ T, [Γ |- t : T] × (forall u, [Γ |- t ≅ u : T] -> well_typed Γ (zip u π)).
  Proof.
    intros H.
    induction π as [|[]] in t, H |- * ; cbn.
    - destruct H as [T Hty].
      exists T ; split.
      1: eassumption.
      intros *.
      eexists.
      boundary.
    - cbn in H.
      eapply IHπ in H as (T&(?&[]&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u Htyu.
      eapply Hsubst.
      econstructor.
      1: eapply TermEmptyElimCong ; tea ; refold.
      2: eassumption.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as (T&(?&[]&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u Htyu.
      eapply Hsubst.
      econstructor.
      1: eapply TermNatElimCong ; tea ; refold.
      + now econstructor.
      + now econstructor.
      + now eapply TermRefl.
      + eassumption.
    - cbn in H.
      eapply IHπ in H as (T&(?&(?&?&[])&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u' Htyu.
      eapply Hsubst.
      econstructor.
      1: econstructor ; tea.
      2: eassumption.
      now econstructor.
  Qed.

  Lemma isType_ty Γ T t :
    [Γ |- t : T] ->
    isType t ->
    ~ whne t ->
    [Γ |- U ≅ T].
  Proof.
    intros Hty HisT Hne.
    all: inversion HisT ; subst ; clear HisT ; cycle -1.
    1: now exfalso.
    all: clear Hne.
    all: eapply termGen' in Hty as (?&[]&?); subst.
    all: eassumption.
  Qed.

  Lemma zip1_notType Γ T t π :
    isType t ->
    ~ whne t ->
    [Γ |- zip1 t π : T] ->
    False.
  Proof.
    intros Ht Ht' Hty.
    destruct π ; cbn in * ;
      eapply termGen' in Hty as (?&[]&?) ; subst ; prod_hyp_splitter ;
      match goal with H : [_ |-[de] t : _] |- _ => (unshelve eapply isType_ty, ty_conv_inj in H) end ; tea.
    all: try solve [now econstructor].
    all: now easy.
  Qed.

  Lemma wh_red_stack_complete Γ t π :
    well_typed Γ (zip t π) ->
    domain wh_red_stack (t,π).
  Proof.
    intros Hty.
    pose proof (Hacc := well_typed_acc _ _ _ Hty).
    change (zip t π) with (zip (fst (t,π)) (snd (t,π))) in *.
    set (z := (t, π)) in *. clearbody z.
    induction Hacc as [z H IH] in Hty |- *.
    apply compute_domain. funelim (wh_red_stack z).
    all: simpl.
    all: try easy.
    - cbn in * ; eapply well_typed_zip in Hty as [? [? _]] ; cbn in *.
      eapply zip1_notType ; tea.
      all: now eapply isType_tm_view1.
    - cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *.
      eapply termGen' in Hty as (?&[_ _ (?&[?[->]]&Hconv)%termGen']&?).
      unshelve eapply ty_conv_inj in Hconv.
      1-2: now econstructor.
      easy.
    - cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *.
      eapply termGen' in Hty as (?&[_ _ _ _ (?&[?[->]]&Hconv)%termGen']&?).
      unshelve eapply ty_conv_inj in Hconv.
      1-2: now econstructor.
      easy.
    - split ; [|easy].
      eapply IH.
      + red. red. cbn.
        left.
        constructor.
        eapply zip_ored.
        now econstructor.
      + cbn in *.
        eapply well_typed_zip in Hty as (?&[??Hu]).
        eapply Hu, RedConvTeC, subject_reduction ; tea.
        now do 2 econstructor.
    - cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *.
      eapply termGen' in Hty as (?&[? ? (?&->&Hconv)%termGen']&?).
      unshelve eapply ty_conv_inj in Hconv.
      1-2: now econstructor.
      easy.
  - split ; [|easy].
    eapply IH.
    + red. red. cbn.
      left.
      constructor.
      eapply zip_ored.
      now econstructor.
    + cbn in *.
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *.
    eapply termGen' in Hty as (?&(?&?&[_ (?&->&Hconv)%termGen'])&?).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now econstructor.
    easy.
  - cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *.
    eapply termGen' in Hty as (?&[_ _ (?&[->]&Hconv)%termGen']&?).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now econstructor.
    easy.
  - cbn in *.
    split ; [|easy].
    eapply IH ; cbn in *.
    + red. red. cbn.
      left.
      constructor.
      eapply zip_ored.
      now econstructor.
    + cbn in *.
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *.
    eapply termGen' in Hty as (?&(?&?&[_ (?&[->]&Hconv)%termGen'])&?).
    unshelve eapply ty_conv_inj in Hconv.
    1-2: now econstructor.
    easy.
  - cbn in *.
    split ; [|easy].
    eapply IH ; cbn in *.
    2: eassumption.
    red. red. cbn.
    right.
    econstructor.
    destruct s ; cbn ; now constructor.
  Qed.

  Corollary wh_red_complete Γ t :
    well_typed Γ t ->
    domain wh_red t.
  Proof.
    intros.
    eapply compute_domain.
    Fail rewrite wh_red_equation_1.
    (* weird, should work? probably the reason why simp also fails? *)
    rewrite (wh_red_equation_1 t).
    cbn.
    split ; [|easy].
    now eapply wh_red_stack_complete.
  Qed.
  
End RedImplemComplete.

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

Section ConversionCorrect.

  Import AlgorithmicTypingData.

  #[local]Existing Instance ty_errors.

  #[universes(polymorphic)]Equations conv_correct_type (x : ∑ (c : conv_state) (_ : context) (_ : cstate_input c) (_ : term), term)
    (r : result (cstate_output x.π1)) : Type :=
  conv_correct_type _ (error _) := True ;
  conv_correct_type (ty_state;Γ;_;T;V) (ok tt) :=  [Γ |-[al] T ≅ V] ;
  conv_correct_type (ty_red_state;Γ;_;T;V) (ok tt) := [Γ |-[al] T ≅h V] ;
  conv_correct_type (tm_state;Γ;A;t;u) (ok tt) := [Γ |-[al] t ≅ u : A] ;
  conv_correct_type (tm_red_state;Γ;A;t;u) (ok tt) :=
    ([× whnf A, whnf t & whnf u] -> [Γ |-[al] t ≅h u : A]) ;
  conv_correct_type (ne_state;Γ;_;m;n) (ok T) => [Γ |-[al] m ~ n ▹ T] ;
  conv_correct_type (ne_red_state;Γ;_;m;n) (ok T) => [Γ |-[al] m ~h n ▹ T].

  Lemma conv_correct :
    funrect conv (fun _ => True) conv_correct_type.
  Proof.
    intros x _.
    funelim (conv _) ; cbn.
    all: intros ; simp conv_correct_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : result unit, _ => intros [[]|] ; [..|easy] ; cbn
      | |- forall x : result _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => simp conv_correct_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      end).
    - econstructor ; tea.
      all: now eapply red_sound.
    - econstructor.
      4: eapply H2 ; split.
      all: now eapply red_sound.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - econstructor ; tea.
      all: now eapply red_sound.
    - destruct s, s'.
      now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - destruct s.
      now econstructor.
    - destruct s.
      now econstructor.
    - destruct s.
      now econstructor.
    - econstructor ; tea.
      now econstructor.
    - econstructor ; tea.
      all: now prod_hyp_splitter.
    - now econstructor.
    - now econstructor.
    - econstructor ; tea.
      prod_hyp_splitter.
      destruct w ; simp build_nf_view3 in Heq ; try solve [inversion Heq].
      all: now econstructor.
    - eapply convne_meta_conv.
      2: reflexivity.
      + econstructor.
        now eapply ctx_access_correct.
      + f_equal.
        symmetry.
        now eapply Nat.eqb_eq.
  Qed.