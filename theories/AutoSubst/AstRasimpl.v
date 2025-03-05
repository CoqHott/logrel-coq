(** AST support for rasimpl **)

From Coq Require Import List.
From LogRel.AutoSubst Require Export core unscoped Ast RAsimpl Extra.
From LogRel Require Import Utils.
From LogRel.Syntax Require Import BasicAst Context WeakeningDef.
From Coq Require Import Setoid Morphisms Relation_Definitions.
Import ListNotations.

(** Weakenings **)

Inductive quoted_wk : forall (Γ Δ : context), Γ ≤ Δ -> Type :=
| qwk_atom {Γ Δ} (ρ : Γ ≤ Δ) : quoted_wk Γ Δ ρ
| qwk_comp {Γ Δ Ξ ρr ρq} (r : quoted_wk Γ Δ ρr) (q : quoted_wk Δ Ξ ρq) : quoted_wk Γ Ξ (ρr ∘w ρq)
| qwk_step A {Γ Δ ρq} (q : quoted_wk Γ Δ ρq) : quoted_wk (Γ,, A) Δ (wk_step A ρq)
| qwk_up A {Γ Δ ρq} (q : quoted_wk Γ Δ ρq) : quoted_wk (Γ,, A⟨ρq⟩) (Δ,, A) (wk_up A ρq)
| qwk_emp : quoted_wk ε ε wk_empty
| qwk_id Γ : quoted_wk Γ Γ (@wk_id Γ)
| qwk1 Γ A : quoted_wk (Γ,,A) Γ (@wk1 Γ A).

Definition quoted_wk_packed := ∑& Γ Δ (ρ : Γ ≤ Δ), quoted_wk Γ Δ ρ.
Definition pack_quoted_wk {Γ Δ} {ρ : Γ ≤ Δ} : quoted_wk Γ Δ ρ -> quoted_wk_packed :=
  fun r => (& Γ ; Δ ; ρ ; r).
Definition unquote_wk (p : quoted_wk_packed) := dfst (dsnd (dsnd p)).
Definition unpack_quoted_wk (p : quoted_wk_packed) := dsnd (dsnd (dsnd p)).

Fixpoint quoted_wk_to_quoted_ren {Γ Δ ρ} (q: quoted_wk Γ Δ ρ) : quoted_ren :=
  match q with
  | qwk_atom ρ => qren_atom (wk_to_ren ρ)
  | qwk_comp r q => qren_comp (quoted_wk_to_quoted_ren r) (quoted_wk_to_quoted_ren q)
  | qwk_step _ ρ => qren_comp  qren_shift (quoted_wk_to_quoted_ren ρ)
  | qwk_up _ q => qren_cons q0 (qren_comp  qren_shift (quoted_wk_to_quoted_ren q))
  | qwk_emp => qren_id
  | qwk_id _ => qren_id
  | qwk1 _ _ => qren_comp qren_shift qren_id
  end.

Lemma quoted_wk_to_ren {Γ Δ ρ} (q : quoted_wk Γ Δ ρ) : ρ =1 unquote_ren (quoted_wk_to_quoted_ren q).
Proof.
  induction q; cbn.
  - reflexivity.
  - now rewrite <-IHq1, <-IHq2, <-wk_compose_compose.
  - now rewrite IHq.
  - rewrite <-IHq; reflexivity.
  - reflexivity.
  - now rewrite wk_to_ren_id.
  - now rewrite wk_to_ren_id.
Qed.

Lemma eval_quoted_wk {Γ Δ ρ} (q : quoted_wk Γ Δ ρ) :
  ρ =1 unquote_ren (eval_ren (quoted_wk_to_quoted_ren q)).
Proof.
  now rewrite (quoted_wk_to_ren q), eval_ren_sound.
Qed.

Lemma apply_wk_sound {Γ Δ ρ} (r : quoted_wk Γ Δ ρ) n :
    unquote_nat (apply_ren (quoted_wk_to_quoted_ren r) n) = ρ (unquote_nat n).
Proof.
  induction r in n |- *; cbn.
  all: try reflexivity.
  - rewrite wk_compose_compose; destruct n; cbn.
    + now rewrite <- 2!quoted_wk_to_ren.
    + now rewrite IHr1, IHr2.
    + now rewrite IHr1, IHr2.
  - destruct n; cbn.
    + now rewrite <-quoted_wk_to_ren.
    + now rewrite IHr.
    + now rewrite IHr.
  - destruct n as [|  | n]; cbn.
    + now rewrite <- quoted_wk_to_ren.
    + reflexivity.
    + destruct n; cbn.
      * now rewrite <- quoted_wk_to_ren.
      * now rewrite IHr.
      * now rewrite IHr.
  - now rewrite wk_to_ren_id.
  - rewrite wk_to_ren_id; destruct n; cbn; reflexivity.
Qed.



Inductive quoted_subst :=
| qsubst_atom (σ : nat-> term)
| qsubst_comp (s t : quoted_subst)
| qsubst_compr (s : quoted_subst) (r : quoted_ren)
| qsubst_compw (s : quoted_subst) (r : quoted_wk_packed)
| qsubst_rcomp (r : quoted_ren) (s : quoted_subst)
| qsubst_wcomp (r : quoted_wk_packed) (s : quoted_subst)
| qsubst_cons (t : quoted_term) (s : quoted_subst)
| qsubst_id
| qsubst_ren (r : quoted_ren)
| qsubst_wk (r : quoted_wk_packed)

with quoted_term :=
| qatom (t : term)
| qren (r : quoted_ren) (t : quoted_term)
| qwk (r : quoted_wk_packed) (t : quoted_term)
| qsubst (s : quoted_subst) (t : quoted_term).

Fixpoint unquote_subst q :=
  match q with
  | qsubst_atom σ => σ
  | qsubst_comp s t => funcomp (subst_term (unquote_subst s)) (unquote_subst t)
  | qsubst_compr s r => funcomp (unquote_subst s) (unquote_ren r)
  | qsubst_compw s r => funcomp (unquote_subst s) (wk_to_ren (unquote_wk r))
  | qsubst_rcomp r s => funcomp (ren_term (unquote_ren r)) (unquote_subst s)
  | qsubst_wcomp r s => funcomp (Ren1_well_wk (unquote_wk r)) (unquote_subst s)
  | qsubst_cons t s => scons (unquote_term t) (unquote_subst s)
  | qsubst_id => tRel
  | qsubst_ren r => funcomp tRel (unquote_ren r)
  | qsubst_wk r => funcomp tRel (wk_to_ren (unquote_wk r))
  end

with unquote_term q :=
  match q with
  | qatom t => t
  | qren r t => ren_term (unquote_ren r) (unquote_term t)
  | qwk r t => Ren1_well_wk (unquote_wk r) (unquote_term t)
  | qsubst s t => subst_term (unquote_subst s) (unquote_term t)
  end.

(** Evaluation **)

Inductive eval_subst_comp_view : quoted_subst -> quoted_subst -> Type :=
| es_id_l s : eval_subst_comp_view qsubst_id s
| es_id_r s : eval_subst_comp_view s qsubst_id
| es_comp_r s u v : eval_subst_comp_view s (qsubst_comp u v)
| es_compr_r s x y : eval_subst_comp_view s (qsubst_compr x y)
| es_compw_r s x y : eval_subst_comp_view s (qsubst_compw x y)
| es_rcomp_r s x y : eval_subst_comp_view s (qsubst_rcomp x y)
| es_wcomp_r s x y : eval_subst_comp_view s (qsubst_wcomp x y)
| es_cons_r s t s' : eval_subst_comp_view s (qsubst_cons t s')
| es_ren_l r s : eval_subst_comp_view (qsubst_ren r) s
| es_wk_l r s : eval_subst_comp_view (qsubst_wk r) s
| es_ren_r s r : eval_subst_comp_view s (qsubst_ren r)
| es_wk_r s r : eval_subst_comp_view s (qsubst_wk r)
| es_other u v : eval_subst_comp_view u v.

Definition eval_subst_comp_c u v : eval_subst_comp_view u v :=
  match u, v with
  | qsubst_id, v => es_id_l v
  | u, qsubst_id => es_id_r u
  | u, qsubst_comp x y => es_comp_r u x y
  | u, qsubst_compr x y => es_compr_r u x y
  | u, qsubst_compw x y => es_compw_r u x y
  | u, qsubst_rcomp x y => es_rcomp_r u x y
  | u, qsubst_wcomp x y => es_wcomp_r u x y
  | u, qsubst_cons t s => es_cons_r u t s
  | qsubst_ren r, s => es_ren_l r s
  | qsubst_wk r, s => es_wk_l r s
  | u, qsubst_ren r => es_ren_r u r
  | u, qsubst_wk r => es_wk_r u r
  | u, v => es_other u v
  end.

Inductive eval_subst_compr_view : quoted_subst -> quoted_ren -> Type :=
| esr_id_l r : eval_subst_compr_view qsubst_id r
| esr_id_r s : eval_subst_compr_view s qren_id
| esr_comp_r s x y : eval_subst_compr_view s (qren_comp x y)
| esr_cons_r s n r : eval_subst_compr_view s (qren_cons n r)
| esr_ren_l s r : eval_subst_compr_view (qsubst_ren s) r
| esr_cons_shift t s : eval_subst_compr_view (qsubst_cons t s) qren_shift
| esr_other s r : eval_subst_compr_view s r.

Definition eval_subst_compr_c s r : eval_subst_compr_view s r :=
  match s, r with
  | qsubst_id, r => esr_id_l r
  | s, qren_id => esr_id_r s
  | s, qren_comp x y => esr_comp_r s x y
  | s, qren_cons n r => esr_cons_r s n r
  | qsubst_ren s, r => esr_ren_l s r
  | qsubst_cons t s, qren_shift => esr_cons_shift t s
  | s, r => esr_other s r
  end.

Inductive eval_subst_rcomp_view : quoted_ren -> quoted_subst -> Type :=
| ers_id_l s : eval_subst_rcomp_view qren_id s
| ers_id_r r : eval_subst_rcomp_view r qsubst_id
| ers_comp_r r x y : eval_subst_rcomp_view r (qsubst_comp x y)
| ers_compr_r r x y : eval_subst_rcomp_view r (qsubst_compr x y)
| ers_rcomp_r r x y : eval_subst_rcomp_view r (qsubst_rcomp x y)
| ers_cons_r r t s : eval_subst_rcomp_view r (qsubst_cons t s)
| ers_ren_r r s : eval_subst_rcomp_view r (qsubst_ren s)
| ers_other r s : eval_subst_rcomp_view r s.

Definition eval_subst_rcomp_c r s : eval_subst_rcomp_view r s :=
  match r, s with
  | qren_id, s => ers_id_l s
  | r, qsubst_id => ers_id_r r
  | r, qsubst_comp x y => ers_comp_r r x y
  | r, qsubst_compr x y => ers_compr_r r x y
  | r, qsubst_rcomp x y => ers_rcomp_r r x y
  | r, qsubst_cons t s => ers_cons_r r t s
  | r, qsubst_ren s => ers_ren_r r s
  | r, s => ers_other r s
  end.

Inductive qsubst_ren_id_view : quoted_subst -> Type :=
| is_qsubst_ren r : qsubst_ren_id_view (qsubst_ren r)
| is_qsubst_id : qsubst_ren_id_view qsubst_id
| not_qsubst_ren_id s : qsubst_ren_id_view s.

Definition test_qsubst_ren_id s : qsubst_ren_id_view s :=
  match s with
  | qsubst_ren r => is_qsubst_ren r
  | qsubst_id => is_qsubst_id
  | s => not_qsubst_ren_id s
  end.

(* TODO Could be improved like apply_ren *)
Fixpoint apply_subst (s : quoted_subst) (n : quoted_nat) : quoted_term :=
  match s, n with
  | qsubst_atom s, _ => qatom (s (unquote_nat n))
  | qsubst_id, _ => qatom (tRel (unquote_nat n))
  | _, qnat_atom n => qatom (unquote_subst s n)
  | qsubst_comp s1 s2, _ => qsubst s1 (apply_subst s2 n)
  | qsubst_compr s r, _ => apply_subst s (apply_ren r n)
  | qsubst_compw s r, _ => apply_subst s (apply_ren (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) n)
  | qsubst_rcomp r s, _ => qren r (apply_subst s n)
  | qsubst_wcomp r s, _ => qwk r (apply_subst s n)
  | qsubst_cons t s, q0 => t
  | qsubst_cons t s, qS n => apply_subst s n
  | qsubst_ren r, n => qatom (tRel (unquote_nat (apply_ren r n)))
  | qsubst_wk r, n => qatom (tRel (unquote_nat (apply_ren (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) n)))
  end.

Definition eval_subst_compr s r :=
  match eval_subst_compr_c s r with
  | esr_id_l r => qsubst_ren r
  | esr_id_r s => s
  | esr_comp_r s x y => qsubst_compr (qsubst_compr s x) y
  | esr_cons_r s n r => qsubst_cons (apply_subst s n) (qsubst_compr s r)
  | esr_ren_l s r => qsubst_ren (qren_comp s r)
  | esr_cons_shift t s => s
  | esr_other s r => qsubst_compr s r
  end.

Definition eval_subst_rcomp r s :=
  match eval_subst_rcomp_c r s with
  | ers_id_l s => s
  | ers_id_r r => qsubst_ren r
  | ers_comp_r r x y => qsubst_comp (qsubst_rcomp r x) y
  | ers_compr_r r x y => qsubst_compr (qsubst_rcomp r x) y
  | ers_rcomp_r r x y => qsubst_rcomp (qren_comp r x) y
  | ers_cons_r r t s => qsubst_cons (qren r t) (qsubst_rcomp r s)
  | ers_ren_r r s => qsubst_ren (qren_comp r s)
  | ers_other r s => qsubst_rcomp r s
  end.

Definition eval_ren_term r t :=
  match t with
  | qsubst s t => qsubst (eval_subst_rcomp r s) t
  | qren r' t => qren (eval_ren (qren_comp r r')) t
  | qwk r' t => qren (eval_ren (qren_comp r (quoted_wk_to_quoted_ren (unpack_quoted_wk r')))) t
  | qatom _ =>
    match test_qren_id r with
    | is_qren_id => t
    | not_qren_id r => qren r t
    end
  end.

Fixpoint eval_subst (s : quoted_subst) : quoted_subst :=
  match s with
  | qsubst_comp u v =>
    let u := eval_subst u in
    let v := eval_subst v in
    match eval_subst_comp_c u v with
    | es_id_l v => v
    | es_id_r u => u
    | es_comp_r u x y => qsubst_comp (qsubst_comp u x) y
    | es_compr_r u x y => qsubst_compr (qsubst_comp u x) y
    | es_compw_r u x y => qsubst_compr (qsubst_comp u x) (quoted_wk_to_quoted_ren (unpack_quoted_wk y))
    | es_rcomp_r u x y => qsubst_comp (qsubst_compr u x) y
    | es_wcomp_r u x y => qsubst_comp (qsubst_compr u (quoted_wk_to_quoted_ren (unpack_quoted_wk x))) y
    | es_cons_r u t s => qsubst_cons (qsubst u t) (qsubst_comp u s)
    | es_ren_l r s => qsubst_rcomp r s
    | es_wk_l r s => qsubst_rcomp (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) s
    | es_ren_r u r => qsubst_compr u r
    | es_wk_r u r => qsubst_compr u (quoted_wk_to_quoted_ren (unpack_quoted_wk r))
    | es_other u v => qsubst_comp u v
    end
  | qsubst_compr s r =>
    let s := eval_subst s in
    let r := eval_ren r in
    eval_subst_compr s r
  | qsubst_compw s r =>
    let s := eval_subst s in
    let r := eval_ren (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) in
    eval_subst_compr s r
  | qsubst_rcomp r s =>
    let r := eval_ren r in
    let s := eval_subst s in
    eval_subst_rcomp r s
  | qsubst_wcomp r s =>
    let r := eval_ren (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) in
    let s := eval_subst s in
    eval_subst_rcomp r s
  | qsubst_cons t s =>
    let t := eval_term t in
    let s := eval_subst s in
    qsubst_cons t s
  | qsubst_ren r =>
    let r := eval_ren r in
    match test_qren_id r with
    | is_qren_id => qsubst_id
    | not_qren_id r => qsubst_ren r
    end
  | qsubst_wk r =>
    let r := eval_ren (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) in
    match test_qren_id r with
    | is_qren_id => qsubst_id
    | not_qren_id r => qsubst_ren r
    end
  | qsubst_id => s
  | qsubst_atom _ => s
  end

with eval_term (t : quoted_term) : quoted_term :=
  match t with
  | qren r t =>
    let r := eval_ren r in
    let t := eval_term t in
    eval_ren_term r t
  | qwk r t =>
    let r := eval_ren (quoted_wk_to_quoted_ren (unpack_quoted_wk r)) in
    let t := eval_term t in
    eval_ren_term r t
  | qsubst s t =>
    let s := eval_subst s in
    let t := eval_term t in
    match t with
    | qsubst s' t => qsubst (qsubst_comp s s') t
    | qren r t => qsubst (qsubst_compr s r) t
    | _ =>
      match test_qsubst_ren_id s with
      | is_qsubst_ren r => qren r t
      | is_qsubst_id => t
      | not_qsubst_ren_id s => qsubst s t
      end
    end
  | qatom _ => t
  end.

(** Correctness **)

Lemma apply_subst_sound :
  forall s n,
    unquote_term (apply_subst s n) = unquote_subst s (unquote_nat n).
Proof.
  intros s n.
  induction s in n |- *.
  all: try reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHs2. reflexivity.
    + cbn. rewrite IHs2. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + rewrite IHs. rewrite apply_ren_sound. reflexivity.
    + cbn. rewrite IHs. rewrite apply_ren_sound. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + rewrite IHs. rewrite apply_wk_sound. reflexivity.
    + cbn. rewrite IHs. rewrite apply_wk_sound. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHs. reflexivity.
    + cbn. rewrite IHs. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite IHs. reflexivity.
    + cbn. rewrite IHs. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + reflexivity.
    + cbn. rewrite IHs. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite apply_ren_sound. reflexivity.
    + cbn. rewrite apply_ren_sound. reflexivity.
  - cbn. destruct n.
    + reflexivity.
    + cbn. rewrite apply_wk_sound. reflexivity.
    + cbn. rewrite apply_wk_sound. reflexivity.
Qed.

Ltac set_eval_subst na :=
  lazymatch goal with
  | eval_subst_sound : forall s : quoted_subst, _ |- context [ eval_subst ?s ] =>
    let IH := fresh "IH" in
    pose proof (eval_subst_sound s) as IH ;
    set (na := eval_subst s) in * ;
    clearbody na
  end.


Lemma eval_term_no_qwk {t} : forall r t', eval_term t = qwk r t' -> False.
Proof.
  induction t; cbn; unfold eval_ren_term; intros ??.
  - intros [=].
  - destruct (eval_term t) eqn:et; try now intros [=].
    match goal with
    |  [|- match ?u with | _ => _ end = _ -> False] => destruct u
    end; intros [=].
  - destruct (eval_term t) eqn:et; try now intros [=].
    match goal with
    |  [|- match ?u with | _ => _ end = _ -> False] => destruct u
    end; intros [=].
  - destruct (eval_term t) eqn:et; try now intros [=].
    match goal with
    |  [|- match ?u with | _ => _ end = _ -> False] => destruct u
    end; intros [=].
Qed.


Lemma eval_subst_compr_sound r es :
  unquote_ren r >> unquote_subst es =1 unquote_subst (eval_subst_compr es (eval_ren r)).
Proof.
  intros n; cbn.
  unfold eval_subst_compr.
  remember (eval_ren _) as er eqn:e; unfold eval_subst_compr.
  destruct eval_subst_compr_c.
  + subst; cbn; now rewrite <- eval_ren_sound.
  + now rewrite eval_ren_sound, <- e.
  + now rewrite eval_ren_sound, <- e.
  + rewrite eval_ren_sound, <- e. cbn.
    destruct n. 2: reflexivity.
    cbn. now rewrite apply_subst_sound.
  + subst. cbn. now rewrite <- eval_ren_sound.
  + now rewrite eval_ren_sound, <- e.
  + subst; cbn. now rewrite <- eval_ren_sound.
Qed.

Lemma eval_subst_rcomp_sound es r :
  unquote_subst es >> ren_term (unquote_ren r) =1  unquote_subst (eval_subst_rcomp (eval_ren r) es).
Proof.
  intros n.
  remember (eval_ren _) as er eqn:e; unfold eval_subst_rcomp.
  destruct eval_subst_rcomp_c.
  + unfold funcomp.
    erewrite ren_term_morphism. 3: reflexivity.
    2:{ intro. rewrite eval_ren_sound, <- e. reflexivity. }
    cbn. asimpl. auto.
  + subst. unfold funcomp.  cbn. rewrite eval_ren_sound.
    reflexivity.
  + subst. unfold funcomp. cbn. unfold funcomp.
    rewrite substRen_term. apply subst_term_morphism. 2: reflexivity.
    intro. unfold funcomp. apply ren_term_morphism. 2: reflexivity.
    intro. rewrite <- eval_ren_sound. reflexivity.
  + subst. unfold funcomp. cbn. unfold funcomp.
    apply ren_term_morphism. 2: reflexivity.
    intro. rewrite <- eval_ren_sound. reflexivity.
  + subst. unfold funcomp. cbn. unfold funcomp.
    rewrite renRen_term. apply ren_term_morphism. 2: reflexivity.
    intro. rewrite <- eval_ren_sound. reflexivity.
  + subst. unfold funcomp. cbn.
    destruct n.
    * cbn. apply ren_term_morphism. 2: reflexivity.
      intro. rewrite eval_ren_sound. reflexivity.
    * cbn. unfold funcomp. apply ren_term_morphism. 2: reflexivity.
      intro. rewrite eval_ren_sound. reflexivity.
  + subst. unfold funcomp. cbn. unfold funcomp.
    rewrite <- eval_ren_sound. reflexivity.
  + subst. cbn. unfold funcomp.
    apply ren_term_morphism. 2: reflexivity.
    intro. rewrite eval_ren_sound. reflexivity.
Qed.

Lemma eval_ren_term_sound {r t} :
  unquote_term t = unquote_term (eval_term t) ->
  ren_term (unquote_ren r) (unquote_term t) = unquote_term (eval_ren_term (eval_ren r) (eval_term t)).
Proof.
  intros eval_term_sound.
  rewrite eval_ren_sound, eval_term_sound.
  unfold eval_ren_term.
  remember (eval_term _) as et eqn:e in *; destruct et.
  + cbn; remember (eval_ren _) as rr eqn:er; destruct test_qren_id.
    * cbn; now asimpl.
    * subst. now cbn.
  + cbn -[eval_ren].
    rewrite <-(eval_ren_sound (qren_comp _ _)).
    cbn; now rewrite renRen_term.
  + destruct (eval_term_no_qwk _ _ (symmetry e)).
  + cbn -[eval_subst_rcomp].
    now rewrite <- eval_subst_rcomp_sound, substRen_term, <-eval_ren_sound.
Qed.

Fixpoint eval_subst_sound s :
    pointwise_relation _ eq (unquote_subst s) (unquote_subst (eval_subst s))
with eval_term_sound t :
    unquote_term t = unquote_term (eval_term t).
Proof.
  {
    intros n.
    destruct s.
    all: try reflexivity.
    - cbn. set_eval_subst es1. set_eval_subst es2.
      destruct eval_subst_comp_c.
      + cbn in *. unfold funcomp. rewrite IH, IH0.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp. rewrite IH, IH0.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        rewrite <-quoted_wk_to_ren; now rewrite IH, IH0.
      + cbn in *. unfold funcomp in *.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. reflexivity.
      + cbn in *. unfold funcomp in *.
        symmetry; erewrite subst_term_morphism; [| | reflexivity].
        2: intros ?; rewrite <-quoted_wk_to_ren; reflexivity.
        rewrite IH, IH0; unfold Ren1_well_wk; cbn; asimpl.
        reflexivity.
      + cbn in *. unfold funcomp.
        erewrite subst_term_morphism. 2,3: eauto.
        asimpl. destruct n. all: reflexivity.
      + cbn in *. unfold funcomp in *.
        rewrite IH, IH0.
        rewrite rinstInst'_term. reflexivity.
      + cbn in *. unfold funcomp.
        rewrite <-quoted_wk_to_ren, IH, IH0.
        rewrite <-rinstInst'_term. reflexivity.
      + cbn in *. unfold funcomp in *.
        rewrite IH, IH0. reflexivity.
      + cbn in *. unfold funcomp in *.
        rewrite <-quoted_wk_to_ren, IH, IH0. reflexivity.
      + cbn in *. unfold funcomp. rewrite IH, IH0. reflexivity.
    - cbn. set_eval_subst es; now rewrite IH, eval_subst_compr_sound.
    - cbn. set_eval_subst es; unfold funcomp.
      rewrite IH, <-eval_subst_compr_sound .
      now rewrite <-quoted_wk_to_ren.
    - cbn. set_eval_subst es.
      now rewrite IH, eval_subst_rcomp_sound.
    - cbn. set_eval_subst es.
      now rewrite IH, <-eval_subst_rcomp_sound, <-quoted_wk_to_ren.
    - cbn. erewrite scons_morphism. 2,3: eauto.
      reflexivity.
    - cbn. remember (eval_ren _) as er eqn:e.
      destruct test_qren_id.
      + cbn. unfold funcomp. rewrite eval_ren_sound, <- e.
        reflexivity.
      + subst. cbn. unfold funcomp. rewrite <- eval_ren_sound.
        reflexivity.
    - cbn. remember (eval_ren _) as er eqn:e.
      destruct test_qren_id.
      + cbn. unfold funcomp.
        now rewrite (eval_quoted_wk (unpack_quoted_wk r)), <-e.
      + subst. cbn. unfold funcomp.
        now rewrite <- eval_quoted_wk.
  }
  {
    destruct t.
    - reflexivity.
    - cbn; now rewrite eval_ren_term_sound.
    - cbn; rewrite <- eval_ren_term_sound; cbn; [|eauto].
      rewrite (eval_quoted_wk (unpack_quoted_wk r)).
      now rewrite <- eval_ren_sound.
    - cbn. remember (eval_term _) as et eqn:e in *.
      destruct et.
      + remember (eval_subst _) as ss eqn:es in *.
        rewrite eval_term_sound, <- e. cbn.
        destruct test_qsubst_ren_id.
        * cbn. erewrite subst_term_morphism. 3: reflexivity.
          2:{ intro. rewrite eval_subst_sound, <- es. reflexivity. }
          cbn. rewrite rinstInst'_term. reflexivity.
        * cbn. erewrite subst_term_morphism. 3: reflexivity.
          2:{ intro. rewrite eval_subst_sound, <- es. reflexivity. }
          cbn. asimpl. reflexivity.
        * subst. cbn.
          eapply subst_term_morphism. 2: reflexivity.
          intro. apply eval_subst_sound.
      + cbn. rewrite eval_term_sound, <- e. cbn. rewrite renSubst_term.
        apply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp. rewrite <- eval_subst_sound. reflexivity.
      + destruct (eval_term_no_qwk _ _ (symmetry e)).
      + cbn. rewrite eval_term_sound, <- e. cbn. rewrite substSubst_term.
        eapply subst_term_morphism. 2: reflexivity.
        intro. unfold funcomp.
        eapply subst_term_morphism. 2: reflexivity.
        intro. rewrite <- eval_subst_sound. reflexivity.
  }
Qed.


(** Quoting **)

Ltac quote_wk r :=
  lazymatch r with
  | wk_well_wk_compose ?r ?r' =>
    let q := quote_wk r in
    let q' := quote_wk r' in
    constr:(qwk_comp q q')
  | @wk_id ?γ =>
    constr:(qwk_id γ)
  | @wk1 ?γ ?a =>
    constr:(qwk1 γ a)
  | wk_up ?a ?r =>
    let q := quote_wk r in
    constr:(qwk_up a q)
  | wk_step ?a ?q =>
    let q := quote_wk q in
    constr:(qwk_step a q)
  | _ => constr:(qwk_atom r)
  end.


Ltac quote_subst s :=
  lazymatch s with
  | funcomp tRel (wk_to_ren (wk (Γ:=?Γ) (Δ:=?Δ) ?r)) =>
    let q := quote_wk r in
    constr:(qsubst_wk (& Γ; Δ; r; q))
  | funcomp tRel ?r =>
    let q := quote_ren r in
    constr:(qsubst_ren q)
  | funcomp (subst_term ?s) ?t =>
    let q := quote_subst s in
    let q' := quote_subst t in
    constr:(qsubst_comp q q')
  | funcomp (ren_term ?r) ?s =>
    let qr := quote_ren r in
    let qs := quote_subst s in
    constr:(qsubst_rcomp qr qs)
  | funcomp (Ren1_well_wk (Γ:=?Γ) (Δ:=?Δ) ?r) ?s =>
    let qr := quote_wk r in
    let qs := quote_subst s in
    constr:(qsubst_wcomp (& Γ; Δ; r; qr) qs)
  | funcomp  ?s (wk_to_ren (wk (Γ:=?Γ) (Δ:=?Δ) ?r)) =>
    let qs := quote_subst s in
    let qr := quote_wk r in
    constr:(qsubst_compw qs (& Γ; Δ; r; qr))
  | funcomp (Y := nat) ?s ?r =>
    let qs := quote_subst s in
    let qr := quote_ren r in
    constr:(qsubst_compr qs qr)
  | scons ?t ?s =>
    let qt := quote_term t in
    let q := quote_subst s in
    constr:(qsubst_cons qt q)
  | ids => constr:(qsubst_id)
  | tRel => constr:(qsubst_id)
  (* Instead of minimize *)
  | fun x => ?g (?f x) =>
    let t := constr:(funcomp g f) in
    quote_subst t
  | fun x => ?f x =>
    let t := constr:(f) in
    quote_subst t
  | _ => constr:(qsubst_atom s)
  end

with quote_term t :=
  lazymatch t with
  | Ren1_well_wk (Γ:=?Γ) (Δ:=?Δ) ?r ?t =>
    let qr := quote_wk r in
    let qt := quote_term t in
    constr:(qwk (& Γ ; Δ; r; qr) qt)
  | ren_term ?r ?t =>
    let qr := quote_ren r in
    let qt := quote_term t in
    constr:(qren qr qt)
  | subst_term ?s ?t =>
    let qs := quote_subst s in
    let qt := quote_term t in
    constr:(qsubst qs qt)
  | _ => constr:(qatom t)
  end.


(** Results markings *)

Definition subst_term' := subst_term.
Definition ren_term' := ren_term.

Ltac mark_result t :=
  lazymatch t with
  | subst_term ?σ ?t => constr:(subst_term' σ t)
  | ren_term ?ρ ?t => constr:(ren_term' ρ t)
  | _ => t
  end.

Hint Unfold subst_term' : asimpl_post_unfold.
Hint Unfold ren_term' : asimpl_post_unfold.

(** Unfoldings **)

#[export] Hint Unfold
  VarInstance_term Ren_term Up_term_term Up_term up_term Subst_term
  upRen_term_term up_term_term
  : asimpl_unfold.

Class TermSimplification (t s : term) := MkSimplTm {
  autosubst_simpl_term : t = s
}.

Arguments autosubst_simpl_term t {s _}.

Hint Mode TermSimplification + - : typeclass_instances.

Declare Reduction asimpl_cbn_term :=
  cbn [
    unquote_term eval_term test_qren_id test_qsubst_ren_id
    unquote_ren eval_ren eval_ren_term apply_ren eval_ren_comp_c
    unquote_subst eval_subst eval_subst_compr_c eval_subst_comp_c
    eval_subst_rcomp_c apply_subst quoted_wk_to_quoted_ren
    unquote_nat dfst dsnd unpack_quoted_wk unquote_wk pack_quoted_wk
    ren_term subst_term ren_term' subst_term' scons
    eval_subst_compr eval_subst_rcomp
  ].

Declare Reduction asimpl_unfold_term :=
  unfold upRen_term_term, up_ren, up_term_term, var_zero.

#[export] Hint Extern 10 (TermSimplification ?t _) =>
  let q := quote_term t in
  let s := eval asimpl_cbn_term in (unquote_term (eval_term q)) in
  let s := eval asimpl_unfold_term in s in
  first [
    constr_eq_strict t s ;
    let s := mark_result s in
    exact (MkSimplTm t s eq_refl) |
    exact (MkSimplTm t s (eval_term_sound q)) ]
  : typeclass_instances.

Class SubstSimplification (r s : nat -> term) := MkSimplSubst {
  autosubst_simpl_csubst : pointwise_relation _ eq r s
}.

Arguments autosubst_simpl_csubst r {s _}.

Hint Mode SubstSimplification + - : typeclass_instances.

#[export] Hint Extern 10 (SubstSimplification ?r _) =>
  let r := eval unfold subst_term', ren_term' in r in
  let q := quote_subst r in
  let s := eval asimpl_cbn_term in (unquote_subst (eval_subst q)) in
  let s := eval asimpl_unfold_term in s in
  exact (MkSimplSubst r s (eval_subst_sound q))
  : typeclass_instances.


Lemma autosubst_simpl_term_wk Γ Δ r t s :
    TermSimplification (@Ren1_well_wk  Γ Δ r t) s ->
    @Ren1_well_wk Γ Δ r t = s.
Proof.
  intros H.
  apply autosubst_simpl_term, _.
Qed.

Lemma autosubst_simpl_term_ren :
  forall r t s,
    TermSimplification (ren_term r t) s ->
    ren_term r t = s.
Proof.
  intros r t s H.
  apply autosubst_simpl_term, _.
Qed.

Lemma autosubst_simpl_term_subst :
  forall r t s,
    TermSimplification (subst_term r t) s ->
    subst_term r t = s.
Proof.
  intros r t s H.
  apply autosubst_simpl_term, _.
Qed.

(** Triggers **)

#[export] Hint Rewrite -> autosubst_simpl_term_wk : asimpl.
#[export] Hint Rewrite -> autosubst_simpl_term_ren : asimpl.
#[export] Hint Rewrite -> autosubst_simpl_term_subst : asimpl.

(* Trying to get automatic simplification of weakenings, breaks some stuff, TODO debug *)
(* Could use the structures in RAsimpl up to reducing quoted_wk_to_quoted_ren et al.
Class WkSimplification Γ Δ (t : Γ ≤ Δ) (s : nat -> nat) := MkSimplWk {
  autosubst_simpl_wk : wk_to_ren t = s
}.

Arguments autosubst_simpl_wk Γ Δ t {s _}.

Hint Mode WkSimplification + + + - : typeclass_instances.

#[export] Hint Extern 10 (WkSimplification _ _ ?t _) =>
  let q := quote_wk t in
  let s := eval asimpl_cbn_term in (unquote_ren (eval_ren (quoted_wk_to_quoted_ren q))) in
  let s := eval asimpl_unfold_term in s in
  exact (MkSimplWk t s (eval_quoted_wk q))
  : typeclass_instances.

Lemma autosubst_simpl_ren_wk :
  forall Γ Δ t s,
    WkSimplification Γ Δ t s ->
    wk_to_ren (wk t) = s.
Proof.
  intros Γ Δ t s H.
  apply autosubst_simpl_wk, _.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_ren_wk : asimpl. *)

Ltac debug_term_simplification_hint :=
  match goal with
  | |- TermSimplification ?t _ =>
    let q := quote_term t in
    let q0 := fresh "q" in pose (q0 := q) ;
    let s := eval asimpl_cbn_term in (unquote_term (eval_term q)) in
    let s := eval asimpl_unfold_term in s in
    first [
      constr_eq_strict t s ;
      let s := mark_result s in
      let result0 := fresh "res" in
      try pose (result0 := MkSimplTm t s eq_refl) |
      let result0 := fresh "res" in
      try pose (result0 := MkSimplTm t s (eval_term_sound q)) ]
  end.

