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
Reserved Notation "[ δ |-s σ ◃ γ ]" (at level 0, δ, γ, σ at level 50, only parsing).


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


Lemma dir_ren_up {γ δ d ρ} : dir_ren ρ δ γ -> dir_ren (up_ren ρ) (d :: δ) (d :: γ).
Proof.
  intros hρ [|n] d' ; cbn.
  - intros [= <-]; exists d; now split.
  - intros [d'' [-> ]]%hρ; exists d''; now split.
Qed.

Lemma dir_ren1 {δ d} : dir_ren ↑ (d :: δ) δ.
Proof.
  intros [|n] d' ; cbn.
  - destruct δ; intro h; inversion h; subst.
    eexists; split; tea.
    reflexivity.
  - destruct δ; intro h; inversion h; subst.
    eexists; split; tea.
    reflexivity.
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
    destruct (ihB _ _ (dir_ren_up hρ)) as [d2 [dirB' leq2]].
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * dirt iht ? * hρ.
    destruct (iht _ _ (dir_ren_up hρ)) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * dirf ihf dira iha ? * hρ.
    destruct (ihf _ _ hρ) as [d1 [dirf' leq1]].
    eexists; split; tea.
    constructor; tea.
    now apply iha.
Qed.

Definition dir_wk {Γ Δ} (ρ : Γ ≤ Δ) (δ γ : list direction) :=
  forall n d, List.nth_error γ n = Some d ->
  ∑ d', (List.nth_error δ (ρ n) = Some d') × dir_leq d' d.

Lemma dir_wk_up {Γ Δ A γ δ d} (ρ : Γ ≤ Δ) : dir_wk ρ δ γ -> dir_wk (wk_up A ρ) (d :: δ) (d :: γ).
Proof.
  intros hρ [|n] d' ; cbn.
  - intros [= <-]; exists d; now split.
  - intros [d'' [-> ]]%hρ; exists d''; now split.
Qed.


Lemma dir_infer_check_wk γ
  (Pinfer:= fun γ d t _ => forall Γ Δ δ (ρ : Γ ≤ Δ) , dir_wk ρ δ γ -> ∑ d', [δ |- t⟨ρ⟩ ▹ d'] * dir_leq d' d)
  (Pcheck := fun γ d t _ => forall Γ Δ δ (ρ : Γ ≤ Δ) , dir_wk ρ δ γ -> [δ |- t⟨ρ⟩ ◃ d])
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
    destruct (ihB _ _ _ _ (dir_wk_up _ hρ (A:=A))) as [d2 [dirB' leq2]].
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * dirt iht ? * hρ.
    destruct (iht _ _ _ _ (dir_wk_up _ hρ (A:=A))) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * dirf ihf dira iha ? * hρ.
    destruct (ihf _ _ _ _ hρ) as [d1 [dirf' leq1]].
    eexists; split; tea.
    constructor; tea.
    now apply iha.
Qed.


(* Inductive DirSubst (δ: list direction) : list direction -> (nat -> term) -> Type:= *)
(* | dirSEmpty {σ} : [ δ |-s σ ◃ nil ] *)
(* | dirSCons {σ γ d} : *)
(*   [ δ |-s ↑ >> σ ◃ γ ] -> *)
(*   [ δ |- σ var_zero ◃ d ] -> *)
(*   [ δ |-s σ ◃ cons d γ ] *)
(* where "[ δ '|-s' σ ◃ γ ]" := (DirSubst δ γ σ). *)


Definition DirSubst (δ γ : list direction) (σ: nat -> term) :=
  forall n d, List.nth_error γ n = Some d -> [ δ |- σ n ◃ d ].
Notation "[ δ '|-s' σ ◃ γ ]" := (DirSubst δ γ σ).


Lemma dir_subst_up {δ γ d σ} :
  [ δ |-s σ ◃ γ ] ->
  [ cons d δ |-s σ⟨↑⟩ ◃ γ ].
Proof.
  intros H n d' eq.
  change [(d :: δ) |- (σ n)⟨↑⟩ ◃ d'].
  eapply (Datatypes.snd (dir_infer_check_ren _)).
  1: now apply H.
  exact dir_ren1.
Qed.

Lemma dir_subst_up_term_term {δ γ d σ} :
  [ δ |-s σ ◃ γ ] -> [ (d :: δ) |-s up_term_term σ ◃ (d :: γ) ].
Proof.
  intros H [|n] d'.
  - cbn. intros [=->].
    econstructor. 1: constructor; reflexivity. reflexivity.
  - cbn. intros eq. now eapply dir_subst_up.
Qed.

Lemma dir_id_subst {δ} :
  [δ |-s tRel ◃ δ].
Proof.
  intros n d eq. econstructor.
  1: now constructor.  reflexivity.
Qed.

Lemma dir_subst_var {δ γ n d σ} :
  List.nth_error γ n = Some d -> [δ |-s σ ◃ γ] -> [δ |- (tRel n)[σ] ◃ d].
Proof.
  intros nth H.
  now apply H.
Qed.

Lemma dir_infer_check_subst γ
  (Pinfer:= fun γ d t _ => forall δ σ, [ δ |-s σ ◃ γ ] -> ∑ d', [δ |- t[σ] ▹ d'] * dir_leq d' d)
  (Pcheck := fun γ d t _ => forall δ σ, [ δ |-s σ ◃ γ ] -> [δ |- t[σ] ◃ d])
:
  (forall d t (der : [γ |- t ▹ d]), Pinfer γ d t der)
  * (forall d t (der : [γ |- t ◃ d]), Pcheck γ d t der).
Proof.
  apply DirInferCheck_rect.
  all: unfold Pinfer, Pcheck.
  - econstructor; split; constructor.
  - intros.
    unshelve epose (Y := dir_subst_var _ _). 6,7: tea. inversion Y; subst.
    eexists; split; tea.
  - intros * dirA ihA dirB ihB ? * hσ.
    destruct (ihA _ _ hσ) as [d1 [dirA' leq1]].
    destruct (ihB _ _ (dir_subst_up_term_term hσ)) as [d2 [dirB' leq2]].
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * dirt iht ? * hσ.
    destruct (iht _ _ (dir_subst_up_term_term hσ)) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * dirf ihf dira iha ? * hσ.
    destruct (ihf _ _ hσ) as [d1 [dirf' leq1]].
    eexists; split; tea.
    constructor; tea.
    now apply iha.
  - intros * ? ih **; edestruct ih as [? []]; tea; econstructor; tea.
    now etransitivity.
Qed.

Lemma dir_subst1 {δ d d' B a} :
  [ δ |- a ◃ d' ] -> [ cons d' δ |- B ◃ d ] -> [ δ |- B[a..] ◃ d ].
Proof.
  intros.
  eapply dir_infer_check_subst; tea.
  intros [|n] d''.
  - cbn. now intros [=->]. (* TODO: lemma for subst cons *)
  - intros eq. inversion eq. cbv.
    econstructor.
    1: now constructor.
    reflexivity.
Qed.

Inductive DirCtx : context -> list direction -> list direction -> Type :=
| dirNil : DirCtx nil nil nil
| dirCons {Γ δ δty A d dA} : DirCheck δ dA A -> DirCtx Γ δ δty -> DirCtx (cons A Γ) (cons d δ) (cons dA δty).

Lemma dir_ctx_nth_ty {Γ δ δT} :
  DirCtx Γ δ δT ->
  forall n T dT, in_ctx Γ n T ->
  List.nth_error δT n = Some dT ->
  [δ |- T ◃ dT].
Proof.
  induction 1.
  - intros []; inversion 2.
  - intros [|n].
    + intros T dT H eq; inversion H; inversion eq; subst.
      eapply dir_infer_check_ren; tea.
      apply dir_ren1.
    + intros T dT H eq; inversion H; inversion eq; subst.
      eapply dir_infer_check_ren.
      * eapply IHX; tea.
      * eapply dir_ren1.
Qed.
