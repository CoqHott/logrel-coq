(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations DirectedDirections Weakening Context.
From Coq Require Import CRelationClasses.

Set Primitive Projections.

Reserved Notation "[ δ |- t ◃ d ]" (at level 0, δ, d, t at level 50, only parsing).
Reserved Notation "[ δ |- t ▹ d ]" (at level 0, δ, d, t at level 50, only parsing).


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

(* TODO: use × instead of * *)
Scheme DirInfer_mut_rect := Induction for DirInfer Sort Type with
    DirCheck_mut_rect := Induction for DirCheck Sort Type.

Combined Scheme DirInferCheck_rect from
  DirInfer_mut_rect,
  DirCheck_mut_rect.

Definition dirU' {δ d} : [ δ |- U ◃ d ].
Proof.
  econstructor. 1: econstructor.
  cbn; easy.
Defined.

Definition dirVar' {δ n d d'} :
  List.nth_error δ n = Some d ->
  d ⪯ d' -> [δ |- tRel n ◃ d'].
Proof.
  econstructor. 1: econstructor. all: tea.
Defined.

Definition dirProd' {δ d A B} :
  [ δ |- A ◃ (dir_op d) ] -> [ cons Discr δ |- B ◃ d ] -> [ δ |- tProd A B ◃ d ].
Proof.
  intros hA hB. inversion hA; subst. inversion hB; subst.
  assert (dir_op d0 ⪯ d) by (destruct d0, d; easy).
  unshelve eassert (max := (MaxDirProp.max_exists (dir_op d0) d1 d _ _)); tea.
  destruct max as [max ?].
  econstructor. 1: econstructor.
  1,2,3: tea.
  eapply MaxDirProp.max_least; tea.
Defined.

Definition dirLam' {δ d A t} :
  [ cons Discr δ |- t ◃ d ] ->
  [ δ |- tLambda A t ◃ d ].
Proof.
  intros ht; inversion ht; subst.
  econstructor. 1: econstructor.
  all: tea.
Defined.

Definition dirApp' {δ d f a} :
  [ δ |- f ◃ d ] ->
  [ δ |- a ◃ Discr ] ->
  [ δ |- tApp f a ◃ d ].
Proof.
  intros hf ha; inversion hf; subst.
  econstructor. 1: econstructor.
  all: tea.
Defined.

Definition dir_ren (ρ : nat -> nat) (δ γ : list direction) :=
  forall n d, List.nth_error γ n = Some d ->
  ∑ d', (List.nth_error δ (ρ n) = Some d') × dir_leq d' d.


Lemma dir_ren_up_discr {γ δ ρ} : dir_ren ρ δ γ -> dir_ren (up_ren ρ) (Discr :: δ) (Discr :: γ).
Proof.
  intros hρ [|n] d ; cbn.
  - intros [= <-]; exists Discr; now split.
  - intros [d' [-> ]]%hρ; exists d'; now split.
Qed.

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
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * dirt iht ? * hρ.
    destruct (iht _ _ (dir_ren_up_discr hρ)) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * dirf ihf dira iha ? * hρ.
    destruct (ihf _ _ hρ) as [d1 [dirf' leq1]].
    eexists; split; tea.
    constructor; tea.
    now apply iha.
Qed.

Definition dir_subst {Γ Δ} (ρ : Γ ≤ Δ) (δ γ : list direction) :=
  forall n d, List.nth_error γ n = Some d ->
  ∑ d', (List.nth_error δ (ρ n) = Some d') × dir_leq d' d.

Lemma dir_wk_up_discr {Γ Δ A γ δ} (ρ : Γ ≤ Δ) : dir_subst ρ δ γ -> dir_subst (wk_up A ρ) (Discr :: δ) (Discr :: γ).
Proof.
  intros hρ [|n] d ; cbn.
  - intros [= <-]; exists Discr; now split.
  - intros [d' [-> ]]%hρ; exists d'; now split.
Qed.


Lemma dir_infer_check_subst γ
  (Pinfer:= fun γ d t _ => forall Γ Δ δ (ρ : Γ ≤ Δ) , dir_subst ρ δ γ -> ∑ d', [δ |- t⟨ρ⟩ ▹ d'] * dir_leq d' d)
  (Pcheck := fun γ d t _ => forall Γ Δ δ (ρ : Γ ≤ Δ) , dir_subst ρ δ γ -> [δ |- t⟨ρ⟩ ◃ d])
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
    destruct (ihA _ _ _ _ hρ) as [d1 [dirA' leq1]].
    destruct (ihB _ _ _ _ (dir_wk_up_discr _ hρ (A:=A))) as [d2 [dirB' leq2]].
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * dirt iht ? * hρ.
    destruct (iht _ _ _ _ (dir_wk_up_discr _ hρ (A:=A))) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * dirf ihf dira iha ? * hρ.
    destruct (ihf _ _ _ _ hρ) as [d1 [dirf' leq1]].
    eexists; split; tea.
    constructor; tea.
    now apply iha.
Qed.

Lemma dir_subst_Discr {δ d B a} :
  [ δ |- a ◃ Discr ] -> [ cons Discr δ |- B ◃ d ] -> [ δ |- B[a..] ◃ d ].
Proof.
Admitted.

Inductive dir_ctx : context -> list direction -> list direction -> Type :=
| dirNil : dir_ctx nil nil nil
| dirCons {Γ δ δty A d dA} : DirCheck δ dA A -> dir_ctx (cons A Γ) (cons d δ) (cons dA δty).

Lemma dir_ctx_nth_ty {Γ δ δT n T dT} :
  dir_ctx Γ δ δT ->
  in_ctx Γ n T ->
  List.nth_error δT n = Some dT ->
  [δ |- T ◃ dT].
Proof.
  intros dΓ inΓ.
  induction inΓ.
  - inversion dΓ; subst.
    cbn.
    admit.
Admitted.
