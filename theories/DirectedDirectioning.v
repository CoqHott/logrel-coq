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
  [ δ |- a ▹ Discr ] ->
  [ δ |- tApp f a ▹ d ]
where "[ δ |- t ▹ d ]" := (DirInfer δ d t).

Definition DirCheck (δ : list direction) (d: direction) (t: term) : Type :=
  ∑ d', [δ |- t ▹ d'] × dir_leq d' d.
Notation "[ δ |- t ◃ d ]" := (DirCheck δ d t).

Definition dirU' {δ d} : [ δ |- U ◃ d ].
Proof.
  repeat econstructor.
Defined.

Definition dirVar' {δ n d d'} :
  List.nth_error δ n = Some d ->
  d ⪯ d' -> [δ |- tRel n ◃ d'].
Proof.
  repeat econstructor.
  all: tea.
Defined.

Definition dirProd' {δ d A B} :
  [ δ |- A ◃ (dir_op d) ] -> [ cons Discr δ |- B ◃ d ] -> [ δ |- tProd A B ◃ d ].
Proof.
  intros [dA []] [dB []].
  assert (dir_op dA ⪯ d) by (destruct dA, d; easy).
  unshelve eassert (max := (MaxDirProp.max_exists (dir_op dA) dB d _ _)); tea.
  destruct max as [max ?].
  repeat econstructor.
  1,2,3: tea.
  eapply MaxDirProp.max_least; tea.
Defined.

Definition dirLam' {δ d A t} :
  [ cons Discr δ |- t ◃ d ] ->
  [ δ |- tLambda A t ◃ d ].
Proof.
  intros [dt []].
  repeat econstructor.
  all: tea.
Defined.

Definition dirApp' {δ d f a} :
  [ δ |- f ◃ d ] ->
  [ δ |- a ◃ Discr ] ->
  [ δ |- tApp f a ◃ d ].
Proof.
  intros [df []] [da [? H]]. destruct da; inversion H.
  repeat econstructor.
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

Lemma dir_infer_ren {γ d t} :
  [γ |- t ▹ d] -> forall ρ δ, dir_ren ρ δ γ -> ∑ d', [δ |- t⟨ρ⟩ ▹ d'] × dir_leq d' d.
Proof.
  induction 1.
  - econstructor; split; econstructor.
  - intros * hρ.
    destruct (hρ _ _ e) as [? []].
    econstructor; split.
    1: now econstructor.
    tea.
  - intros * hρ.
    destruct (IHDirInfer1 _ _ hρ) as [d1 [dirA' leq1]].
    destruct (IHDirInfer2 _ _ (dir_ren_up hρ)) as [d2 [dirB' leq2]].
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * hρ.
    destruct (IHDirInfer _ _ (dir_ren_up hρ)) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * hρ.
    destruct (IHDirInfer1 _ _ hρ) as [d1 [dirf' leq1]].
    destruct (IHDirInfer2 _ _ hρ) as [d2 [dira' leq2]].
    eexists; split; tea.
    constructor; tea.
    now destruct d2; inversion leq2.
Qed.

Lemma dir_check_ren {γ d t} :
  [γ |- t ◃ d] -> forall ρ δ, dir_ren ρ δ γ -> [δ |- t⟨ρ⟩ ◃ d].
Proof.
  intros [d' [dirt leq]] * dren.
  epose (inf := dir_infer_ren dirt _ _ dren).
  repeat econstructor. 1: apply inf.π2.
  etransitivity; tea. apply inf.π2.
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


(* Lemma dir_infer_check_wk γ *)
(*   (Pinfer:= fun γ d t _ => forall Γ Δ δ (ρ : Γ ≤ Δ) , dir_wk ρ δ γ -> ∑ d', [δ |- t⟨ρ⟩ ▹ d'] * dir_leq d' d) *)
(*   (Pcheck := fun γ d t _ => forall Γ Δ δ (ρ : Γ ≤ Δ) , dir_wk ρ δ γ -> [δ |- t⟨ρ⟩ ◃ d]) *)
(* : *)
(*   (forall d t (der : [γ |- t ▹ d]), Pinfer γ d t der) *)
(*   * (forall d t (der : [γ |- t ◃ d]), Pcheck γ d t der). *)
(* Proof. *)
(*   apply DirInferCheck_rect. *)
(*   all: unfold Pinfer, Pcheck. *)
(*   6:{ *)
(*     intros * ? ih **; edestruct ih as [? []]; tea; econstructor; tea. *)
(*     now etransitivity. *)
(*   } *)
(*   - econstructor; split; econstructor. *)
(*   - intros * e * hρ. *)
(*     destruct (hρ _ _ e) as [? []]. *)
(*     econstructor; split. *)
(*     1: now econstructor. *)
(*     tea. *)
(*   - intros * dirA ihA dirB ihB ? * hρ. *)
(*     destruct (ihA _ _ _ _ hρ) as [d1 [dirA' leq1]]. *)
(*     destruct (ihB _ _ _ _ (dir_wk_up _ hρ (A:=A))) as [d2 [dirB' leq2]]. *)
(*     assert (dir_op d1 ⪯ d''). *)
(*     by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1). *)
(*     assert (d2 ⪯ d''). *)
(*     by (etransitivity; tea; now eapply MaxDirProp.upper_bound2). *)
(*     unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea. *)
(*     exists d3; split. *)
(*     1: now econstructor. *)
(*     eapply MaxDirProp.max_least; tea. *)
(*   - intros * dirt iht ? * hρ. *)
(*     destruct (iht _ _ _ _ (dir_wk_up _ hρ (A:=A))) as [d1 [dirt' leq1]]. *)
(*     eexists; split; tea. *)
(*     now econstructor. *)
(*   - intros * dirf ihf dira iha ? * hρ. *)
(*     destruct (ihf _ _ _ _ hρ) as [d1 [dirf' leq1]]. *)
(*     eexists; split; tea. *)
(*     constructor; tea. *)
(*     now apply iha. *)
(* Qed. *)


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
  eapply dir_check_ren.
  1: now apply H.
  exact dir_ren1.
Qed.

Lemma dir_subst_up_term_term {δ γ d σ} :
  [ δ |-s σ ◃ γ ] -> [ (d :: δ) |-s up_term_term σ ◃ (d :: γ) ].
Proof.
  intros H [|n] d'.
  - cbn. intros [=->].
    repeat econstructor.
    reflexivity.
  - cbn. intros eq. now eapply dir_subst_up.
Qed.

Lemma dir_id_subst {δ} :
  [δ |-s tRel ◃ δ].
Proof.
  intros n d eq. repeat econstructor; tea.
  reflexivity.
Qed.

Lemma dir_subst_var {δ γ n d σ} :
  List.nth_error γ n = Some d -> [δ |-s σ ◃ γ] -> [δ |- (tRel n)[σ] ◃ d].
Proof.
  intros nth H.
  now apply H.
Qed.

Lemma dir_infer_subst {γ d t} :
  [γ |- t ▹ d] -> forall δ σ, [ δ |-s σ ◃ γ ] -> ∑ d', [δ |- t[σ] ▹ d'] × dir_leq d' d.
Proof.
  induction 1.
  - econstructor; split; constructor.
  - intros.
    unshelve epose (Y := dir_subst_var _ _). 6,7: tea. (* inversion Y; subst. *)
    repeat econstructor.
    all: apply Y.π2.
  - intros * hσ.
    destruct (IHDirInfer1 _ _ hσ) as [d1 [dirA' leq1]].
    destruct (IHDirInfer2 _ _ (dir_subst_up_term_term hσ)) as [d2 [dirB' leq2]].
    assert (dir_op d1 ⪯ d'').
    by (etransitivity; try apply dir_op_mon; tea; now eapply MaxDirProp.upper_bound1).
    assert (d2 ⪯ d'').
    by (etransitivity; tea; now eapply MaxDirProp.upper_bound2).
    unshelve epose proof (MaxDirProp.max_exists (dir_op d1) d2 d'' _ _) as [d3]; tea.
    exists d3; split.
    1: now econstructor.
    eapply MaxDirProp.max_least; tea.
  - intros * hσ.
    destruct (IHDirInfer _ _ (dir_subst_up_term_term hσ)) as [d1 [dirt' leq1]].
    eexists; split; tea.
    now econstructor.
  - intros * hσ.
    destruct (IHDirInfer1 _ _ hσ) as [d1 [dirf' leq1]].
    destruct (IHDirInfer2 _ _ hσ) as [d2 [dira' leq2]].
    eexists; split; tea.
    constructor; tea.
    now destruct d2; inversion leq2.
Qed.

Lemma dir_check_subst {γ d t} :
  [γ |- t ◃ d] -> forall δ σ, [ δ |-s σ ◃ γ ] -> [δ |- t[σ] ◃ d].
Proof.
  intros [d' [dirt leq]] * dren.
  epose (inf := dir_infer_subst dirt _ _ dren).
  repeat econstructor. 1: apply inf.π2.
  etransitivity; tea. apply inf.π2.
Qed.

Lemma dir_subst1 {δ d d' B a} :
  [ δ |- a ◃ d' ] -> [ cons d' δ |- B ◃ d ] -> [ δ |- B[a..] ◃ d ].
Proof.
  intros.
  eapply dir_check_subst; tea.
  intros [|n] d''.
  - cbn. now intros [=->]. (* TODO: lemma for subst cons *)
  - intros eq. inversion eq. cbv.
    repeat econstructor; tea.
    destruct d''; easy.
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
      eapply dir_check_ren; tea.
      apply dir_ren1.
    + intros T dT H eq; inversion H; inversion eq; subst.
      eapply dir_check_ren.
      * eapply IHX; tea.
      * eapply dir_ren1.
Qed.

