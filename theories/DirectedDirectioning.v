(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations DirectedDirections DirectedContext GenericTyping.
From Coq Require Import CRelationClasses.

Set Primitive Projections.


(* Import DeclarativeTypingData. *)
(* Import DeclarativeTypingProperties. *)
(* Import Notations. *)

Reserved Notation "[ δ |- t ◃ d ]" (at level 0, δ, d, t at level 50, only parsing).
Reserved Notation "[ δ |- t ▹ d ]" (at level 0, δ, d, t at level 50, only parsing).

Notation "d1 ≦ d2" := (dir_leq d1 d2) (at level 70).

Definition max_dir_opt d1 d2 : option direction :=
  match d1, d2 with
  | Discr, d => Some d
  | Fun, Cofun => None
  | Cofun, Fun => None
  | d1, d2 => Some d1
  end.

Definition max_dir d1 d2 d3 := max_dir_opt d1 d2 = Some d3.

Module MaxDirProp.
Section MaxDirProp.

  Lemma max_exists d1 d2 d : d1 ≦ d -> d2 ≦ d -> ∑ d', max_dir d1 d2 d'.
  Proof.
    destruct d, d1, d2; cbn; try easy.
    all: intros _ _; eexists; unfold max_dir; cbn; reflexivity.
  Qed.

  Context (d1 d2 d3 : direction) (e : max_dir_opt d1 d2 = Some d3).

  Lemma upper_bound1 : d1 ≦ d3.
  Proof. 
    destruct d1, d2, d3; cbn in *; try easy.
    all: try injection e; discriminate.
  Qed.

  Lemma upper_bound2 : d2 ≦ d3.
  Proof. 
    destruct d1, d2, d3; cbn in *; try easy.
    all: try injection e; discriminate.
  Qed.

  Lemma max_least d : d1 ≦ d -> d2 ≦ d -> d3 ≦ d.
  Proof.
    destruct d, d1, d2, d3; try easy + discriminate.
  Qed.
  
End MaxDirProp.
End MaxDirProp.


(* TODO [TL]: note this is a "declarative" version, but we could also go algorithmic *)
Inductive DirInfer (δ : list direction) : direction -> term -> Type :=
| dirU : [ δ |- U ▹ Discr ]
| dirVar {d n} :
  List.nth_error δ n = Some d ->
  [ δ |- tRel n ▹ d ]
| dirProd {d d' d'' A B} :
  [ δ |- A ▹ d ] ->
  [ cons Discr δ |- B ▹ d' ] ->
  max_dir (dir_op d) d' d'' ->
  [ δ |- tProd A B ▹ d'' ]
| dirLam {d A t} :
  [ cons Discr δ |- t ▹ d ] ->
  [ δ |- tLambda A t ▹ d ]
| dirApp {d f a} :
  [ δ |- f ▹ d ] ->
  [ δ |- a ◃ Discr ] ->
  [ δ |- tApp f a ▹ d ]
with DirCheck (δ : list direction) : direction -> term -> Type :=
| dirLeq {d d' t}: [δ |- t ▹ d] -> dir_leq d d' -> [δ |- t ◃ d']
where "[ δ |- t ▹ d ]" := (DirInfer δ d t)
and "[ δ |- t ◃ d ]" := (DirCheck δ d t).

Scheme DirInfer_mut_rect := Induction for DirInfer Sort Type with
    DirCheck_mut_rect := Induction for DirCheck Sort Type.

Combined Scheme DirInferCheck_rect from
  DirInfer_mut_rect,
  DirCheck_mut_rect.

Definition dir_ren (ρ : nat -> nat) (δ γ : list direction) :=
  forall n d, List.nth_error γ n = Some d -> 
  ∑ d', (List.nth_error δ (ρ n) = Some d') × dir_leq d' d.

Lemma dir_leq_trans d1 d2 d3 : dir_leq d1 d2 -> dir_leq d2 d3 -> dir_leq d1 d3.
Proof.  destruct d1,d2, d3; easy. Qed.

#[global]
Instance: Transitive dir_leq := dir_leq_trans.


Lemma dir_ren_up_discr {γ δ ρ} : dir_ren ρ δ γ -> dir_ren (up_ren ρ) (Discr :: δ) (Discr :: γ). 
Proof.
  intros hρ [|n] d ; cbn.
  - intros [= <-]; exists Discr; now split.
  - intros [d' [-> ]]%hρ; exists d'; now split.
Qed.

Lemma dir_op_mon d1 d2 : d1 ≦ d2 -> dir_op d1 ≦ dir_op d2.
Proof. destruct d1, d2; easy. Qed.

Lemma dir_infer_check_ren γ 
  (Pinfer:= fun γ d t _ => forall δ ρ , dir_ren ρ δ γ -> ∑ d', [δ |- t⟨ρ⟩ ▹ d'] * dir_leq d' d)
  (Pcheck := fun γ d t _ => forall δ ρ , dir_ren ρ δ γ -> [δ |- t⟨ρ⟩ ◃ d])
:
  (forall d t (der : [γ |- t ▹ d]), Pinfer γ d t der)
  * (forall d t (der : [γ |- t ◃ d]), Pcheck γ d t der).
Proof.
  apply DirInferCheck_rect.
  all: unfold Pinfer, Pcheck.
  6:{
    intros * ? ih **; edestruct ih as [? []]; tea; econstructor; tea.
    now etransitivity.
  }
  - econstructor; split; econstructor.
  - intros * e * hρ. 
    destruct (hρ _ _ e) as [? []].
    econstructor; split.
    1: now econstructor.
    tea.
  - intros * dirA ihA dirB ihB ? * hρ.
    destruct (ihA _ _ hρ) as [d1 [dirA' leq1]].
    destruct (ihB _ _ (dir_ren_up_discr hρ)) as [d2 [dirB' leq2]].
    assert (dir_op d1 ≦ d''). 
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ≦ d''). 
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - admit.
  - admit.
Admitted.


Inductive DirDecl : list direction -> direction -> term -> Type :=
| dirU {δ d} : [ δ |- U @ d ]
| dirVar {δ d d' n} :
  List.nth_error δ n = Some d ->
  dir_leq d d' ->
  [ δ |- tRel n @ d' ]
| dirProd {δ d A B} :
  [ δ |- A @ dir_op d ] ->
  [ cons Discr δ |- B @ d ] ->
  [ δ |- tProd A B @ d ]
| dirLam {δ d A t} :
  [ cons Discr δ |- t @ d ] ->
  [ δ |- tLambda A t @ d ]
| dirApp {δ d f a} :
  [ δ |- f @ d ] ->
  [ δ |- a @ Discr ] ->
  [ δ |- tApp f a @ d ]
where "[ δ |- t @ d ]" := (DirDecl δ d t).



(* TODO: check substitution lemmata for typing *)
(* Lemma DirSubst {δ dB B da a} : *)
(*   [ δ |- a @ da ] -> [ cons da δ |- B @ dB ] -> [ δ |- B[a..] @ dB ]. *)
(* Proof. *)
(*   intros wda wdB. *)
(*   induction wdB. *)
(*   - constructor. *)
(*   - admit. *)
(*   - cbn. *)


Reserved Notation "[ |-( ) Γ ]" (at level 0, Γ at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ]" (at level 0, Γ, d, A at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t : A @( dA ) ]" (at level 0, Γ, dt, t, A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅ t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).
(* Reserved Notation "[ Γ |-( dt ) t ⤳* u ∈ A @( dA ) ]" (at level 0, Γ, dt, t, u, A, dA at level 50). *)

Fixpoint WfCtx (ctx: context) : Type :=
  match ctx with
  | nil => unit
  | cons {| ty := A ; ty_dir := dA ; dir := _ |} Θ =>
      [ |-( ) Θ ] × [ List.map ty Θ |- A ] × [ List.map dir Θ |- A @ dA ]
  end
    where "[ |-( ) Θ ]" := (WfCtx Θ).


Lemma WfCtx_erased {Θ: context} : [ |-( ) Θ ] -> [ |- List.map ty Θ ].
Proof.
  induction Θ.
  - intros. constructor.
  - intros [wfΘ [? ?]]. now constructor.
Qed.

Definition WfType (Θ: context) (d: direction) (A: term) : Type :=
  [ |-( ) Θ ] × [ List.map ty Θ |- A ] × [ List.map dir Θ |- A @ d ].
Notation "[ Θ |-( d ) A ]" := (WfType Θ d A).

Lemma WfCtx_in_ctx {Θ d dA A} :
  [ |-( ) Θ ] -> forall n, in_ctx Θ n {| ty := A; ty_dir := dA; dir := d |} ->
  ([ List.map ty Θ |- A ] × [ List.map dir Θ |- A @ dA ]).
Proof.
Admitted.

Lemma wfTypeU {Θ d} : [ |-( ) Θ ] -> [ Θ |-( d ) U ].
Proof.
  intros wfΘ.
  constructor ; [ now trivial | split ].
  - constructor. now eapply WfCtx_erased.
  - constructor.
Qed.

Lemma wfTypeProd {Γ d} {A B} :
  [ Γ |-( dir_op d ) A ] ->
  [Γ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B ] ->
  [ Γ |-( d ) tProd A B ].
Proof.
  intros [wfA [? ?]] [wfB [? ?]].
  constructor ; [ now trivial | split ].
  all: now constructor.
Qed.

Definition Typing (Θ: context) (dt: direction) (T: term) (dT: direction) (t: term) :=
  [ Θ |-( dT ) T ] × [ List.map ty Θ |- t : T ] × [ List.map dir Θ |- t @ dt ].
Notation "[ Γ |-( dt ) t : T @( dT ) ]" := (Typing Γ dt T dT t).

Lemma wfTypeUniv {Θ d} {A} :
  [ Θ |-( d ) A : U @( Discr ) ] ->
  [ Θ |-( d ) A ].
Proof.
  intros [[wfθ ?] [wtA wdA]].
  constructor ; [ now trivial | split ].
  - now apply wfTypeUniv.
  - assumption.
Qed.


Lemma wfVar {Θ d'} {n d T dT} :
  [ |-( ) Θ ] ->
  in_ctx Θ n {| ty := T; ty_dir := dT; dir := d |} ->
  dir_leq d d' ->
  [ Θ |-( d' ) tRel n : T @( dT ) ].
Proof.
  intros wfΘ inΘ dleq.
  split.
  - constructor ; [ now trivial | split ].
    + eapply WfCtx_in_ctx; tea.
    + eapply WfCtx_in_ctx; tea.
  - split.
    + constructor.
      * now apply WfCtx_erased.
      * admit.
    + eapply dirVar; tea.
      clear wfΘ dleq d'.
      revert Θ T dT d inΘ.
      induction n.
      * intros Θ T dT d inΘ. inversion inΘ; subst. reflexivity.
      * intros Θ T dT d inΘ. inversion inΘ; subst; cbn.
        now eapply IHn.
Admitted.

Lemma wfTermProd {Θ d} {A B} :
  [ Θ |-( dir_op d ) A : U @( Discr ) ] ->
  [ Θ ,, {| ty := A ; ty_dir := dir_op d ; dir := Discr |} |-( d ) B : U @( Discr ) ] ->
  [ Θ |-( d ) tProd A B : U @( Discr ) ].
Proof.
  intros [[wfΘ ?] [wtA wdA]] [? [wtB wdB]].
  split.
  - constructor ; [ now trivial | split ].
    all: now trivial.
  - split.
    1-2: now constructor.
Qed.


Lemma wfTermLam {Θ d} {dT A B t} :
  [ Θ |-( dir_op dT ) A ] ->
  [ Θ ,, {| ty := A ; ty_dir := dir_op dT ; dir := Discr |} |-( d ) t : B @( dT ) ] ->
  [ Θ |-( d ) tLambda A t : tProd A B @( dT ) ].
Proof.
  intros [wfΘ [wtA wdA]] [[? [wtB wdB]] [wtt wdt]].
  split.
  - apply wfTypeProd. all: now constructor.
  - split. all: now constructor.
Qed.


Lemma wfTermApp {Θ d} {dT f a A B} :
  [ Θ |-( d ) f : tProd A B @( dT ) ] ->
  [ Θ |-( Discr ) a : A @( dir_op dT ) ] ->
  [ Θ |-( d ) tApp f a : B[a..] @( dT ) ].
Proof.
  intros [[wfΘ [wfProd wdProd]] [wtf wdf]] [[wfΘ' [wfA wdA]] [wta wda]].
  split.
  - constructor ; [ now trivial | split ].
    + admit.
    + (* will need substitution lemma *)
      admit.
  - split.
    + now econstructor.
    + now constructor.
Admitted.
