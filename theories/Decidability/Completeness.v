(** * LogRel.Decidability.Completeness: the inductive predicates imply the implementation answer positively. *)
From Coq Require Import Nat List Lia Arith ssrbool.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Notations UntypedReduction DeclarativeTyping DeclarativeInstance GenericTyping NormalForms.
From LogRel Require Import Validity LogicalRelation Fundamental DeclarativeSubst TypeConstructorsInj AlgorithmicTyping BundledAlgorithmicTyping Normalisation AlgorithmicTypingProperties TypeUniqueness.
From LogRel.Decidability Require Import Functions Soundness.
From PartialFun Require Import Monad PartialFun.

Set Universe Polymorphism.

Import DeclarativeTypingProperties.
Import IndexedDefinitions.

Equations Derive NoConfusion Subterm for term.

(* The combinator rec throws in a return branch with a type 
  necessarily convertible to the result type, but the syntactic 
  mismatch between the 2 types prevents `rec_graph` from `apply`ing.
  This tactic fixes the type in the return branch to what's expected
  syntactically. *)
Ltac patch_rec_ret :=
  try (unfold rec;
  match goal with 
  | |- orec_graph _ (_rec _ (fun _ : ?Bx => _)) ?hBa => 
    let Ba := type of hBa in change Bx with Ba
  end).

Definition typed_stack Γ A t B (π : stack) :=
  forall u, [Γ |- t ≅ u : A] -> [Γ |- (zip u π) : B].

Definition well_typed_stack Γ A t (π : stack) :=
  forall u, [Γ |- t ≅ u : A] -> well_typed Γ (zip u π).

Lemma typed_stack_conv_in Γ A A' t B (π : stack) :
  typed_stack Γ A t B π ->
  [Γ |- A ≅ A'] ->
  typed_stack Γ A' t B π.
Proof.
  unfold typed_stack.
  intros Hπ Hconv u Hu.
  eapply Hπ.
  now econstructor.
Qed.
  
Lemma typed_zip Γ B t π :
  [Γ |- zip t π : B] ->
  ∑ A, [Γ |- t : A] × typed_stack Γ A t B π.
Proof.
intros Hty.
induction π as [|[]] in t, B, Hty |- * ; cbn.
- exists B ; split.
  1: eassumption.
  intros u ** ; cbn.
  boundary.
- unfold typed_stack in * ; cbn in *.
  eapply IHπ in Hty as (T&(?&[]&?)%termGen'&Hstack) ; subst.
  eexists ; split ; tea.
  intros u Htyu.
  eapply Hstack.
  econstructor.
  1: eapply TermEmptyElimCong ; tea ; refold.
  2: eassumption.
  now econstructor.
- unfold typed_stack in * ; cbn in *.
  eapply IHπ in Hty as (T&(?&[]&?)%termGen'&Hstack) ; subst.
  eexists ; split ; tea.
  intros u Htyu.
  eapply Hstack.
  econstructor.
  1: eapply TermNatElimCong ; tea ; refold.
  + now econstructor.
  + now econstructor.
  + now eapply TermRefl.
  + eassumption.
- unfold typed_stack in * ; cbn in *.
  eapply IHπ in Hty as (T&(?&(?&?&[])&?)%termGen'&Hstack) ; subst.
  eexists ; split ; tea.
  intros u' Htyu.
  eapply Hstack.
  econstructor.
  1: econstructor ; tea.
  2: eassumption.
  now econstructor.
- unfold typed_stack in * ; cbn in *.
  eapply IHπ in Hty as [T [[?[[?[?[->]]]]]%termGen' Hstack]].
  eexists; split; tea.
  intros; eapply Hstack.
  eapply TermConv; refold; tea.
  now econstructor.
- unfold typed_stack in * ; cbn in *.
  eapply IHπ in Hty as [T [[?[[?[?[->]]]]]%termGen' Hstack]].
  eexists; split; tea.
  intros; eapply Hstack.
  eapply TermConv; refold; tea.
  now econstructor.
- unfold typed_stack in * ; cbn in *.
  eapply IHπ in Hty as [T [[?[[]]]%termGen' Hstack]]; subst.
  eexists; split; tea.
  intros; eapply Hstack.
  eapply TermConv; refold; tea.
  econstructor; tea; now (eapply TypeRefl + eapply TermRefl).
Qed.

Lemma well_typed_zip Γ t π :
  well_typed Γ (zip t π) ->
  ∑ A, [Γ |- t : A] × well_typed_stack Γ A t π.
Proof.
  intros [? [? []]%typed_zip].
  eexists ; split ; tea.
  now eexists.
Qed.
  
Lemma zip_app t π π' : zip t (π ++ π') = zip (zip t π) π'.
Proof.
  induction π in t |- * ; cbn ; eauto.
Qed.
  
Lemma typed_zip_app Γ A t B π π' :
  [Γ |- t : A] ->
  typed_stack Γ A t B (π ++ π') ->
  ∑ T, typed_stack Γ A t T π × typed_stack Γ T (zip t π) B π'.
Proof.
  intros Ht Hπ.
  unshelve epose proof (Hπ t _) as Hzip.
  1: now econstructor.
  rewrite zip_app in Hzip.
  eapply typed_zip in Hzip as [T [Hzip]].
  eapply typed_zip in Hzip as [A' []].
  eexists ; split ; tea.
  eapply typed_stack_conv_in ; tea.
  now eapply typing_unique.
Qed.
  
Corollary typed_zip_cons Γ A t B s π :
  [Γ |- t : A] ->
  typed_stack Γ A t B (s :: π) ->
  ∑ T, [Γ |- zip1 t s : T] × typed_stack Γ T (zip1 t s) B π.
Proof.
  intros Ht Hty.
  change (s :: π) with ([:: s] ++ π) in Hty.
  eapply typed_zip_app in Hty as [? [Hts]] ; tea.
  cbn in *.
  eexists ; split ; tea.
  eapply Hts.
  now econstructor.
Qed.
  
Definition nomap_stack π :=
  forallb (fun s => match s with | sMap _ _ _ => false | _ => true end) π.

Definition ismap_stack π :=
  forallb (fun s => match s with | sMap _ _ _ => true | _ => false end) π.

Lemma stack_ne n π :
  nomap_stack π -> whne n -> whne (zip n π).
Proof.
  intros Hπ Hne.
  induction π as [|[]] in n, Hne, Hπ |- * ; cbn.
  1: eassumption.
  1-5: cbn in * ; eapply IHπ ; tea ; now econstructor.
  cbn in * ; congruence.
Qed.

Lemma list_stack_ismap Γ A t B (π : stack) :
  [Γ |- t : tList A] ->
  typed_stack Γ (tList A) t B π ->
  ismap_stack π.
Proof.
  intros Ht Hπ.
  induction π as [|[] π] in A, t, B, Ht, Hπ |- * ; cbn.
  - easy.
  - eapply typed_zip_cons in Hπ as [? [(?&[[-> ? Ht']])%termGen']] ; subst ; tea.
    unshelve eapply typing_unique, ty_conv_inj in Ht ; last first ; tea.
    2-3: now econstructor.
    now cbn in *.
  - eapply typed_zip_cons in Hπ as [? [(?&[[-> ? Ht']])%termGen']] ; subst ; tea.
    unshelve eapply typing_unique, ty_conv_inj in Ht ; last first ; tea.
    2-3: now econstructor.
    now cbn in *.
  - eapply typed_zip_cons in Hπ as [? [(?&[(?&?&[->])])%termGen']] ; subst ; tea.
    unshelve eapply typing_unique, ty_conv_inj in Ht ; last first ; tea.
    2-3: now econstructor.
    now cbn in *.
  - eapply typed_zip_cons in Hπ as [? [(?&[(?&?&[->])])%termGen']] ; subst ; tea.
    unshelve eapply typing_unique, ty_conv_inj in Ht ; last first ; tea.
    2-3: now econstructor.
    now cbn in *.
  - eapply typed_zip_cons in Hπ as [? [(?&[(?&?&[->])])%termGen']] ; subst ; tea.
    unshelve eapply typing_unique, ty_conv_inj in Ht ; last first ; tea.
    2-3: now econstructor.
    now cbn in *.
  - eapply typed_zip_cons in Hπ as [? [[? [[] Hconv]]%termGen' Hstack]] ; subst ; tea.
    eapply typed_stack_conv_in in Hstack.
    2: now symmetry.
    eapply IHπ.
    2: eassumption.
    now econstructor.
Qed.
  
Lemma typed_stack_good Γ A t B (π : stack) :
  [Γ |- t : A] ->
  typed_stack Γ A t B π ->
  ∑ π' π'', [× π = π' ++ π'', nomap_stack π' & ismap_stack π''].
Proof.
  intros Ht Hty.
  induction π as [|[]] in A, t, B, Ht, Hty |- *.
  - exists [::], [::] ; split ; eauto.
  - eapply typed_zip_cons in Hty as [? [? (π'&π''&[])%IHπ]] ; subst ; tea.
    eexists (sEmptyElim _ :: π'), _ ; split.
    1: reflexivity.
    all: eassumption.
  - eapply typed_zip_cons in Hty as [? [? (π'&π''&[])%IHπ]] ; subst ; tea.
    eexists (sNatElim _ _ _ :: π'), _ ; split.
    1: reflexivity.
    all: eassumption.
  - eapply typed_zip_cons in Hty as [? [? (π'&π''&[])%IHπ]] ; subst ; tea.
    eexists (sApp _ :: π'), _ ; split.
    1: reflexivity.
    all: eassumption.
  - eapply typed_zip_cons in Hty as [? [? (π'&π''&[])%IHπ]] ; subst ; tea.
    eexists (sFst :: π'), _ ; split.
    1: reflexivity.
    all: eassumption.
  - eapply typed_zip_cons in Hty as [? [? (π'&π''&[])%IHπ]] ; subst ; tea.
    eexists (sSnd :: π'), _ ; split.
    1: reflexivity.
    all: eassumption.
  - eexists [::], _ ; split.
    1-2: reflexivity.
    pose proof Hty as [? [(?&[->]&?)%termGen' ?]]%typed_zip_cons ; tea.
    eapply list_stack_ismap.
    2: eapply typed_stack_conv_in ; tea.
    2: now eapply typing_unique.
    eassumption.
Qed.

Section CompactImplemComplete.


  Lemma stack_compact_nomap n π :
    whne n -> nomap_stack π -> graph compact (n,π) (zip n π).
  Proof.
  intros Hne Hπ.
  unfold graph.
  induction π as [|s π] in n, Hne, Hπ |- * ; cbn in * ; try fold (nomap_stack π) in Hπ.
  all: simp compact. 
  1: now constructor.
  destruct (Map.into_view n) ; cbn.
  1: inversion Hne.
  destruct s ; cbn in * ; try solve [congruence].
  all: unfold rec ; econstructor ; [eapply IHπ|..] ; tea ; now econstructor.
  Qed.

  Lemma stack_compact_map n π :
    whne_list n -> ismap_stack π -> domain compact (n,π).
  Proof.
  intros Hne Hπ.
  unfold domain, graph.
  induction π as [|s π] in n, Hne, Hπ |- * ; cbn in * ; try fold (ismap_stack π) in Hπ.
  all: simp compact. 
  1: eexists ; now constructor.
  destruct (Map.into_view n) ; cbn.
  - destruct s ; cbn in * ; try solve [congruence].
    edestruct (IHπ (tMap A B0 (comp A f0 f) l)) ; tea.
    1: inversion Hne ; subst ; [..|inversion H] ; now econstructor.
    eexists.
    unfold rec.
    econstructor ; tea.
    now econstructor.
  - destruct s ; cbn in * ; try solve [congruence].
    assert (whne u) by eauto using whne_list_not_map.
    edestruct (IHπ (tMap A B f u)) ; tea.
    1: now econstructor.
    eexists.
    unfold rec.
    econstructor ; tea.
    now econstructor.
  Qed.

  Lemma compact_app t π' π'' v :
    graph compact (t,π') v ->
    domain compact (v,π'') ->
    domain compact (t,π'++π'').
  Proof.
    intros Hπ' Hπ''.
    unfold domain, graph in *.
    induction π' as [|s π] in t, Hπ' |- * ; cbn in *.
    - simp compact in Hπ'.
      inversion Hπ' ; subst.
      eassumption.
    - simp compact in *.
      destruct (Map.into_view t) ; cbn in *.
      + destruct s ; cbn in *.
        1-5: now inversion Hπ'.
        inversion Hπ' ; subst ; clear Hπ'.
        inversion H3 ; subst ; clear H3.
        eapply IHπ in H1 as [].
        eexists.
        unfold rec.
        econstructor ; tea.
        now econstructor.
      + inversion Hπ' ; subst ; clear Hπ'.
        inversion H3 ; subst ; clear H3.
        eapply IHπ in H1 as [].
        eexists.
        unfold rec.
        econstructor ; tea.
        now econstructor.
  Qed.

  Theorem compact_complete Γ t π :
    whne t ->
    well_typed Γ (zip t π) ->
    domain compact (t,π).
  Proof.
    intros Hne [A (?&?&Hstack)%typed_zip].
    eapply typed_stack_good in Hstack as (π'&π''&[->]) ; tea.
    eapply compact_app.
    - now eapply stack_compact_nomap.
    - eapply stack_compact_map ; tea.
      econstructor.
      now eapply stack_ne.
  Qed.

End CompactImplemComplete.

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
    well_formed Γ (zip t π) ->
    Acc R (t,π).
  Proof.
    intros.
    now eapply R_acc, typing_SN.
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

  Ltac termInvContradiction Hty := 
    eapply termGen' in Hty; cbn in Hty; prod_hyp_splitter; subst;
    now match goal with 
    | [H : [_ |-[de] _ : _] |- _] =>
      eapply termGen' in H; cbn in H; prod_hyp_splitter; subst;
      now match goal with
      | [H : [_ |-[de] _ ≅ _] |- _] => unshelve eapply ty_conv_inj in H; first [constructor | easy]
      end
    end.

  Ltac termInvContradictionList Hty := 
    eapply termGen' in Hty; cbn in Hty; prod_hyp_splitter; subst;
    now match goal with 
    | [H : [_ |-[de] _ : tList _] |- _] =>
      eapply termGen' in H; cbn in H; prod_hyp_splitter; subst;
      now match goal with
      | [H : [_ |-[de] _ ≅ tList _] |- _] => unshelve eapply ty_conv_inj in H; first [constructor | easy]
      end
    end.

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
    all: try solve [ cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *; termInvContradiction Hty + termInvContradictionList Hty].
    - cbn in * ; eapply well_typed_zip in Hty as [? [? _]] ; cbn in *.
      eapply zip1_notType ; tea.
      all: now eapply isType_tm_view1.
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
    - split ; [|easy].
      unfold pdomain ; cbn.
      eapply compact_complete ; tea.
      econstructor.
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
    - cbn in *; split; [|easy].
      eapply IH.
      + do 2 red; cbn.
        left; constructor; eapply zip_ored; constructor.
      + cbn. 
        eapply well_typed_zip in Hty as (?&[??Hu]).
        eapply Hu, RedConvTeC, subject_reduction ; tea.
        now do 2 econstructor.
    - cbn in *; split; [|easy].
      eapply IH.
      + do 2 red; cbn.
        left; constructor; eapply zip_ored; constructor.
      + cbn. 
        eapply well_typed_zip in Hty as (?&[??Hu]).
        eapply Hu, RedConvTeC, subject_reduction ; tea.
        now do 2 econstructor.
    - cbn in *; split ; [| easy].
      eapply IH; cbn.
      + do 2 red; cbn.
        left; constructor; eapply zip_ored; constructor.
      + eapply well_typed_zip in Hty as [? [? Hu]].
        eapply Hu, RedConvTeC, subject_reduction; tea.
        now do 2 econstructor.
    - cbn in *; split; [|easy].
      eapply IH; cbn.
      + do 2 red; cbn.
        left; constructor; eapply zip_ored; constructor.
      + eapply well_typed_zip in Hty as [? [? Hu]].
        eapply Hu, RedConvTeC, subject_reduction; tea.
        now do 2 econstructor.
    - cbn in *.
      split ; [|easy].
      eapply IH ; cbn in *.
      2: eassumption.
      red. red. cbn.
      right.
      do 2 econstructor.
    - cbn in *.
      split ; [|easy].
      eapply IH ; cbn in *.
      2: now destruct s.
      red. red. cbn.
      destruct s ; cbn.
      all: right ; do 2 econstructor.
  Qed.

  Corollary wh_red_complete Γ t :
    well_formed Γ t ->
    domain wh_red t.
  Proof.
    intros [|w]%well_formed_well_typed.
    all: eapply compute_domain; simp wh_red; cbn.
    all: split ; [|easy].
    - eapply wh_red_stack_complete ; tea.
    - inversion w ; subst ; clear w; cycle -1.
      1: eapply wh_red_stack_complete ; now econstructor.
      all: econstructor ; cbn ; red.
      all: simp wh_red_stack ; cbn.
      all: now econstructor.
  Qed.

  Corollary wh_red_complete_whnf_class Γ K t t' :
  [Γ |- t ⇒* t' ∈ K] ->
  whnf t' ->
  graph wh_red t t'.
  Proof.
    intros [] ? ; refold.
    assert (domain wh_red t) as h.
    {
      eapply (wh_red_complete Γ).
      destruct K as [|A] ; unshelve econstructor ; [left|right|..] ; cbn.
      2-3: eassumption.
    }
    replace t' with (def wh_red t h).
    1: eapply def_graph_sound.
    eapply whred_det ; tea.
    all: now eapply red_sound, def_graph_sound.
  Qed.
  
  Corollary wh_red_complete_whnf_ty Γ A A' :
  [Γ |-[de] A] ->
  [A ⇒* A'] ->
  whnf A' ->
  graph wh_red A A'.
  Proof.
    intros ? Hred ?.
    eapply subject_reduction_type in Hred ; tea.
    now eapply wh_red_complete_whnf_class.
  Qed.
  
  Corollary wh_red_complete_whnf_tm Γ A t t' :
  [Γ |-[de] t : A] ->
  [t ⇒* t'] ->
  whnf t' ->
  graph wh_red t t'.
  Proof.
    intros ? Hred ?.
    eapply subject_reduction in Hred ; tea.
    now eapply wh_red_complete_whnf_class.
  Qed.

End RedImplemComplete.

Section ConversionComplete.

Let PTyEq (Γ : context) (A B : term) :=
  forall v, graph conv (ty_state;Γ;v;A;B) (ok tt).
Let PTyRedEq (Γ : context) (A B : term) :=
  forall v, graph conv (ty_red_state;Γ;v;A;B) (ok tt).
Let PNeEq (Γ : context) (A t u : term) :=
  forall v, graph conv (ne_state;Γ;v;t;u) (ok A).
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall v, graph conv (ne_red_state;Γ;v;t;u) (ok A).
Let PNeListEq (Γ : context) (A t u : term) := 
  graph conv (ne_list_state;Γ;A;t;u) (ok tt).
Let PTmEq (Γ : context) (A t u : term) := 
  graph conv (tm_state;Γ;A;t;u) (ok tt).
Let PTmRedEq (Γ : context) (A t u : term) :=
  graph conv (tm_red_state;Γ;A;t;u) (ok tt).

Definition whne_ne_view1 {N} (w : whne N) : ne_view1 N :=
  match w with
  | whne_tRel => ne_view1_rel _
  | whne_tApp _ => ne_view1_dest _ (eApp _)
  | whne_tNatElim _ => ne_view1_dest _ (eNatElim _ _ _)
  | whne_tEmptyElim _ => ne_view1_dest _ (eEmptyElim _)
  | whne_tFst _ => ne_view1_dest _ eFst
  | whne_tSnd _ => ne_view1_dest _ eSnd
  end.

Lemma whne_ty_view1 {N} (w : whne N) : build_ty_view1 N = ty_view1_small (whne_ne_view1 w).
Proof.
  now destruct w.
Qed.

Lemma whne_nf_view1 {N} (w : whne N) : build_nf_view1 N = nf_view1_ne (whne_ne_view1 w).
Proof.
  now destruct w.
Qed.

Lemma whne_ty_view2 {M N} (wM : whne M) (wN : whne N) : build_nf_ty_view2 M N = ty_neutrals M N.
Proof.
  simp build_nf_ty_view2.
  unshelve erewrite ! whne_ty_view1 ; tea.
  now reflexivity.
Qed.

Lemma whne_ty_view2_l {M N} (wM : whne M) (wN : isType N):
  (whne N × build_nf_ty_view2 M N = ty_neutrals M N) + (build_nf_ty_view2 M N = ty_mismatch _ _ ).
Proof.
  simp build_nf_ty_view2.
  unshelve erewrite whne_ty_view1 ; tea.
  destruct wN as [| | | | | | ] ; cbn.
  1-6: now right.
  unshelve erewrite (whne_ty_view1 _) ; tea.
  now left.
Qed.

Lemma whne_nf_view3 P m n (wP : isPosType P) (wm : whne m) (wn : whne n) :
  build_nf_view3 P m n =
    (match wP with
    | UnivPos => types _ (ty_neutrals m n)
    | _ => neutrals _ m n
    end).
Proof.
  simp build_nf_view3.
  destruct wP ; cbn.
  - rewrite whne_ty_view2 ; cbn ; tea.
    reflexivity.
  - unshelve erewrite whne_nf_view1 ; tea.
    cbn.
    now rewrite (whne_nf_view1 wn).
  - unshelve erewrite whne_nf_view1 ; tea.
    cbn.
    now rewrite (whne_nf_view1 wn).
  - unshelve erewrite whne_ty_view1 ; tea.
    reflexivity.
Qed.

Lemma whne_list_view3 A m n (wm : whne_list m) (wn : whne_list n) :
  build_nf_view3 (tList A) m n = neutral_lists A m n.
Proof.
  simp build_nf_view3.
  destruct wm, wn ; cbn in *.
  1: reflexivity.
  all: unshelve erewrite !(whne_nf_view1 _) ; tea ; cbn.
  all: reflexivity.
Qed.

Arguments PFun_instance_1 : simpl never.

Lemma implem_conv_complete :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq.
  apply BundledConvInduction.
  - intros * ?? Hconv [IH] **.
    unfold graph.
    simp conv conv_ty ; cbn.
    repeat (match goal with |- orec_graph _ _ _ => econstructor end) ; cbn.
    + eapply wh_red_complete_whnf_ty ; tea.
      eapply algo_conv_wh in Hconv as [].
      gen_typing.
    + eapply wh_red_complete_whnf_ty ; tea.
      eapply algo_conv_wh in Hconv as [].
      gen_typing.
    + exact (IH tt). (* eapply fails with universe issues? *)
    + cbn; econstructor.
  - intros * HA [IHA] HB [IHB] ** ; cbn in *.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.  1: exact (IHA tt).
    cbn; patch_rec_ret; econstructor.
    1: exact (IHB tt).
    now econstructor.
  - intros ; cbn in *.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
  - intros.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
  - intros.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
  - intros * HA [IHA] HB [IHB] **; cbn in *.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    econstructor.
    1: exact (IHA tt).
    cbn; patch_rec_ret; econstructor.
    1: exact (IHB tt).
    now econstructor.
  - intros * HA [IHA] **; cbn in *.
    unfold graph; simp conv conv_ty_red; cbn.
    patch_rec_ret; econstructor.
    1: exact (IHA tt).
    now econstructor.
  - intros * HM [IHM []] **.
    unfold graph.
    simp conv conv_ty_red ; cbn.
    rewrite whne_ty_view2.
    2-3: now eapply algo_conv_wh in HM as [].
    cbn.
    econstructor.
    1: now exact (IHM tt).
    now constructor.
  - intros **.
    unfold graph.
    simp conv conv_ne.
    rewrite Nat.eqb_refl ; cbn.
    erewrite ctx_access_complete ; tea ; cbn.
    now econstructor.
  - intros * Hm [IHm []] Ht [IHt] **.
    unfold graph.
    simp conv conv_ne ; cbn.
    econstructor.
    1: exact (IHm tt).
    cbn.
    econstructor.
    1: exact IHt.
    now constructor.
  - intros * ? [IHn []] ? [IHP] ? [IHz] ? [IHs] **.
    unfold graph.
    simp conv conv_ne ; cbn.
    econstructor.
    1: exact (IHn tt).
    econstructor.
    1: exact (IHP tt).
    econstructor.
    1: exact IHz.
    econstructor.
    1: exact IHs.
    now econstructor.
  - intros * ? [IHe []] ? [IHP] **.
    unfold graph.
    simp conv conv_ne ; cbn.
    econstructor.
    1: exact (IHe tt).
    econstructor.
    1: exact (IHP tt).
    now econstructor.
  - intros * ? [IH []] **.
    unfold graph.
    simp conv conv_ne; cbn.
    econstructor.
    1: exact (IH tt).
    econstructor.
  - intros * ? [IH []] **.
    unfold graph.
    simp conv conv_ne; cbn.
    econstructor.
    1: exact (IH tt).
    econstructor.
  - intros * ? [IHm []] **.
    unfold graph.
    simp conv conv_ne_red ; cbn.
    econstructor.
    1: exact (IHm tt).
    econstructor.
    2: now econstructor.
    eapply wh_red_complete_whnf_ty ; tea.
    boundary.
  - intros * hlst [conv_lst []] hfn [conv_fn] **.
    unfold graph.
    simp conv conv_ne_list ; cbn.
    econstructor.
    + specialize (conv_lst tt).
      exact conv_lst.
    + cbn.
      patch_rec_ret.
      econstructor ; tea.
      now econstructor.
  - intros * ??? []%algo_conv_wh [IHt'] **.
    unfold graph.
    simp conv conv_tm ; cbn -[PFun_instance_1].
    repeat (match goal with |- orec_graph _ _ _ => econstructor end) ; cbn -[PFun_instance_1].
    + eapply wh_red_complete_whnf_ty ; tea.
      1: boundary.
      now gen_typing.
    + now eapply wh_red_complete_whnf_tm.
    + now eapply wh_red_complete_whnf_tm.
    + exact IHt'.
    + cbn; econstructor.
  - intros * ? [IHA] ? [IHB] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    econstructor.
    1: exact IHA.
    cbn; patch_rec_ret; econstructor.
    1: exact IHB.
    now constructor.
  - intros.
    unfold graph.
    simp conv conv_tm_red.
    constructor.
  - intros.
    unfold graph.
    simp conv conv_tm_red.
    constructor.
  - intros * ? [IHt] **.
    unfold graph.
    simp conv conv_tm_red; cbn.
    patch_rec_ret; econstructor.
    1: exact IHt.
    now constructor.
  - intros.
    unfold graph.
    simp conv conv_tm_red.
    now constructor.
  - intros * ?? ? [IHf] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    patch_rec_ret; econstructor.
    1: exact IHf.
    now constructor.
  - intros * ? [IHA] ? [IHB] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    econstructor.
    1: exact IHA.
    cbn; patch_rec_ret; econstructor.
    1: exact IHB.
    now constructor.
  - intros * ??? [ihFst] ? [ihSnd] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    econstructor.
    1: exact ihFst.
    cbn; patch_rec_ret; econstructor.
    1: exact ihSnd.
    now constructor.
  - intros * ? [ihA] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    patch_rec_ret; econstructor.
    1: exact ihA.
    now constructor.
  - intros; unfold graph.
    simp conv conv_tm_red; cbn.
    now constructor.
  - intros * ? [ihhd] ? [ihtl] **.
    unfold graph; simp conv conv_tm_red; cbn.
    patch_rec_ret; econstructor; [exact ihhd|].
    patch_rec_ret; econstructor; [exact ihtl|].
    now constructor.
  - intros * ? [IHm] **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    unshelve erewrite whne_list_view3.
    2-3: now eapply algo_conv_wh in H as [].
    cbn.
    patch_rec_ret ; econstructor ; tea.
    now constructor.
  - intros * ? [IHm []] wP **.
    unfold graph.
    simp conv conv_tm_red ; cbn.
    unshelve erewrite whne_nf_view3 ; tea.
    2-3: now eapply algo_conv_wh in H as [].
    destruct wP ; cbn.
    all: now econstructor ; [exact (IHm tt)|constructor].
Qed.

End ConversionComplete.

Section TypingComplete.

Definition isCanonical_ty_view1 Γ t (c : ~ isCanonical t) : [Γ |- t : U] -> ne_view1 t.
Proof.
revert c.
case t ; intros.
all: try solve [case c ; constructor].
- constructor.
- eapply (ne_view1_dest _ (eApp _)).
- eapply (ne_view1_dest _ (eNatElim _ _ _)).
- eapply (ne_view1_dest _ (eEmptyElim _)).
- eapply (ne_view1_dest _ eFst).
- eapply (ne_view1_dest _ eSnd).
- eapply termGen' in H as [? [[->] Hconv]].
  unshelve eapply ty_conv_inj in Hconv.
  1-2: econstructor.
  now cbn in *.
Defined.

Lemma can_ty_view1_small Γ T (c : ~ isCanonical T) (h : [Γ |- T : U]) :
  build_ty_view1 T = ty_view1_small (isCanonical_ty_view1 Γ T c h).
Proof.
  destruct T ; cbn ; try reflexivity.
  all: try solve [case c ; constructor].
  exfalso.
  eapply termGen' in h as [? [[->] Hconv]].
  unshelve eapply ty_conv_inj in Hconv.
  1-2: econstructor.
  now cbn in *.  
Qed.

Let PTy Γ A := forall v, graph typing (wf_ty_state;Γ;v;A) (ok tt).
Let PInf Γ A t := forall v, graph typing (inf_state;Γ;v;t) (ok A).
Let PInfRed Γ A t := forall v, whnf A -> graph typing (inf_red_state;Γ;v;t) (ok A).
Let PCheck Γ A t := graph typing (check_state;Γ;A;t) (ok tt).

Theorem typing_complete : BundledTypingInductionConcl PTy PInf PInfRed PCheck.
Proof.
  subst PTy PInf PInfRed PCheck.
  apply BundledTypingInduction.
  all: intros.
  all: prod_hyp_splitter.
  all: unfold graph in *.
  (* dispatch the simplifications as needed *)
  Time all: lazymatch goal with
    | |- context [wf_ty_state] => simp typing typing_wf_ty
    | |- context [inf_state] => simp typing typing_inf
    | |- context [inf_red_state] => simp typing typing_inf_red
    | |- context [check_state] => simp typing typing_check
  end.
  (* Time all: simp typing typing_inf typing_wf_ty typing_inf_red typing_check.
  Time all: simp typing typing_inf typing_wf_ty typing_inf_red typing_check ; cbn. *)
  (* Well formed types *)
  1-6:repeat match goal with | |- orec_graph typing _ _ => patch_rec_ret ; econstructor ; try eauto ; cbn end.
  - unshelve erewrite can_ty_view1_small ; tea.
    cbn.
    econstructor.
    1: exact (g tt whnf_tSort).
    now econstructor.
  (* Infer *)
  - repeat match goal with | |- orec_graph typing _ _ => econstructor ; try eauto ; cbn end.
    erewrite ctx_access_complete ; tea ; cbn.
    now econstructor.
  - econstructor.
    1: exact (g0 tt whnf_tSort).
    econstructor.
    1: exact (g tt whnf_tSort).
    cbn.
    now econstructor.
  - econstructor.
    1: exact (g0 tt).
    cbn.
    econstructor.
    1: exact (g tt).
    now constructor.
  - econstructor.
    1: exact (g0 tt whnf_tProd).
    cbn.
    econstructor.
    1: exact g.
    now constructor.
  - now constructor.
  - now constructor.
  - econstructor.
    1: exact (g tt whnf_tNat).
    now constructor.
  - econstructor.
    1: exact (g2 tt whnf_tNat).
    econstructor.
    1: exact (g1 tt).
    econstructor.
    1: exact g0.
    econstructor.
    1: exact g.
    now constructor.
  - now constructor.
  - econstructor.
    1: exact (g0 tt whnf_tEmpty).
    econstructor.
    1: exact (g tt).
    now constructor.
  - econstructor.
    1: exact (g0 tt whnf_tSort).
    cbn; econstructor.
    1: exact (g tt whnf_tSort).
    cbn; econstructor.
  - econstructor.
    1: exact (g2 tt).
    cbn; econstructor.
    1: exact (g1 tt).
    cbn; econstructor.
    1: exact g0.
    cbn; econstructor.
    1: exact g.
    cbn ; econstructor.
  - econstructor.
    1: exact (g tt whnf_tSig).
    econstructor.
  - econstructor.
    1: exact (g tt whnf_tSig).
    econstructor.
  - econstructor.
    1: exact (g tt whnf_tSort).
    econstructor.
  - econstructor.
    1: exact (g tt).
    constructor.
  - econstructor; [exact (g1 tt)|].
    econstructor; [exact g0|].
    econstructor; [exact g|].
    constructor.
  - econstructor; [exact (g2 tt)|].
    econstructor; [exact (g1 tt)|].
    econstructor; [exact g0|].
    econstructor; [exact g|].
    constructor.
  - econstructor.
    1: exact (g v).
    cbn.
    econstructor.
    2: econstructor.
    eapply wh_red_complete_whnf_ty ; tea.
    boundary.
  - econstructor.
    1: exact (g tt).
    cbn.
    econstructor.
    2: econstructor.
    eapply implem_conv_complete.
    split ; tea.
    now boundary.
  Qed.

End TypingComplete.