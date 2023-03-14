From Coq Require Import Lia ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped UntypedReduction.

Inductive weakening : Set :=
  | _wk_id : weakening
  | _wk_step (w : weakening) : weakening
  | _wk_up (w : weakening) : weakening.

(* Transforms an (intentional) weakening into a renaming *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | _wk_id => id
    | _wk_step ρ' => (wk_to_ren ρ') >> S
    | _wk_up ρ' => up_ren (wk_to_ren ρ')
  end.

Coercion wk_to_ren : weakening >-> Funclass.

Fixpoint is_canonical_wk (ρ : weakening) {struct ρ} : bool :=
  match ρ with
  | _wk_id => true
  | _wk_up (_wk_id) => false
  | _wk_up ρ => is_canonical_wk ρ
  | _wk_step ρ => is_canonical_wk ρ
  end.

Inductive well_weakening : weakening -> context -> context -> Type :=
  | well_id {Γ} :  well_weakening _wk_id Γ Γ
  | well_step {Γ Δ : context} (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (_wk_step ρ) (Γ,,vass na A) Δ
  | well_up {Γ Δ : context} (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (_wk_up ρ) (Γ,,vass na (ren_term ρ A)) (Δ,, vass na A).

Fixpoint wk_compose (ρ ρ' : weakening) : weakening :=
  match ρ, ρ' with
    | _wk_id , _ => ρ'
    | _wk_step ν , _ => _wk_step (wk_compose ν ρ')
    | _wk_up ν, _wk_id => ρ
    | _wk_up ν, _wk_step ν' => _wk_step (wk_compose ν ν')
    | _wk_up ν, _wk_up ν' => _wk_up (wk_compose ν ν')
  end.

Lemma wk_compose_compose (ρ ρ' : weakening) : wk_to_ren (wk_compose ρ ρ') =1 ρ' >> ρ.
Proof.
  induction ρ in ρ' |- *.
  - reflexivity.
  - cbn.
    rewrite IHρ.
    now fsimpl.
  - destruct ρ'.
    + reflexivity.
    + cbn.
      rewrite IHρ.
      now asimpl.
    + cbn.
      asimpl.
      rewrite IHρ.
      now asimpl.
Qed.

Lemma well_wk_compose {ρ ρ' : weakening} {Δ Δ' Δ'' : context} :
  well_weakening ρ Δ Δ' -> well_weakening ρ' Δ' Δ'' -> well_weakening (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - eassumption.
  - econstructor. auto.
  - inversion H' as [| | ? ? na' A' ν']; subst ; clear H'.
    1: econstructor; auto.
    1: now econstructor ; auto.
    asimpl.
    replace (ren_term (ν' >> ν) A') with (ren_term (wk_compose ν ν') A')
      by now rewrite wk_compose_compose.
    econstructor ; auto.
Qed.

#[projections(primitive)]Record wk_well_wk {Γ Δ : context} :=
  { wk :> weakening ; well_wk :> well_weakening wk Γ Δ ; can_wk : is_canonical_wk wk }.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).

Definition wk_empty : (ε ≤ ε) := {| wk := _wk_id ; well_wk := well_id ; can_wk := eq_refl |}.

Definition wk_step {Γ Δ} na A (ρ : Γ ≤ Δ) : (Γ,, vass na A) ≤ Δ :=
  {| wk := _wk_step ρ ; well_wk := well_step na A ρ ρ ; can_wk := ρ.(can_wk) |}.

Definition wk_id {Γ} : Γ ≤ Γ :=
  {| wk := _wk_id ; well_wk := well_id ; can_wk := eq_refl |}.

Lemma well_id_ext {Γ Δ} na A : well_weakening _wk_id Γ Δ ->
  well_weakening _wk_id (Γ ,, vass na A⟨wk_to_ren _wk_id⟩) (Δ ,, vass na A).
Proof.
  intro h; inversion h.
  cbn; asimpl.
  constructor.
Qed.

Definition wk_up_aux {Γ Δ} na A (ρ : weakening) :
  well_weakening ρ Γ Δ ->
  is_canonical_wk ρ ->
  (Γ,, vass na A⟨wk_to_ren ρ⟩) ≤ (Δ ,, vass na A) :=
  match ρ with
  | _wk_id => fun wellwk _ => 
    {| wk := _wk_id ; well_wk := well_id_ext na A wellwk ; can_wk := eq_refl |}
  | _wk_step ρ' => 
    fun wellwk iscan => 
    let ρ0 := _wk_step ρ' in  
    {| wk := _wk_up ρ0 ; well_wk := well_up na A ρ0 wellwk ; can_wk := iscan |}
  | _wk_up ρ' => 
    fun wellwk iscan => 
    let ρ0 := _wk_up ρ' in  
    {| wk := _wk_up ρ0 ; well_wk := well_up na A ρ0 wellwk ; can_wk := iscan |}
  end.

Definition wk_up {Γ Δ} na A (ρ : Γ ≤ Δ) : (Γ,, vass na A⟨wk_to_ren ρ⟩) ≤ (Δ ,, vass na A) :=
  wk_up_aux na A ρ.(wk) ρ.(well_wk) ρ.(can_wk).

#[global] Hint Resolve well_wk : core.

#[global] Instance Ren1_wk {Y Z : Type} `(ren : Ren1 (nat -> nat) Y Z) :
  (Ren1 weakening Y Z) := fun ρ t => t⟨wk_to_ren ρ⟩.

#[global] Instance Ren1_well_wk {Y Z : Type} `{Ren1 (nat -> nat) Y Z} {Γ Δ : context} :
  (Ren1 (Γ ≤ Δ) Y Z) :=
  fun ρ t => t⟨wk_to_ren ρ.(wk)⟩.

Arguments Ren1_wk {_ _ _} _ _/.
Arguments Ren1_well_wk {_ _ _ _ _} _ _/.

Ltac fold_wk_ren :=
  change ?t⟨wk_to_ren ?ρ⟩ with t⟨ρ⟩ in * ;
  change ?t⟨wk_to_ren ?ρ.(wk)⟩ with t⟨ρ⟩ in *.

Smpl Add fold_wk_ren : refold.

Lemma can_wk_compose{Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') :
  is_canonical_wk (wk_compose ρ.(wk) ρ'.(wk)).
Proof.
  destruct ρ as [ρ ? can], ρ' as [ρ' ? can']; cbn; clear -can can'.
  induction ρ in can, ρ', can' |- *; cbn; tea.
  1: auto.
  destruct ρ'; tea; cbn in *.
  - apply IHρ; tea. destruct ρ; tea; discriminate.
  - pose proof (ih := fun h => IHρ h ρ').
    set (ρ'' := wk_compose _ _) in ih |- *.
    destruct ρ, ρ'; try discriminate; destruct ρ'' eqn: E; try discriminate.
    all: now apply ih.
Qed.

Definition wk_well_wk_compose {Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' :=
  {| wk := wk_compose ρ.(wk) ρ'.(wk) ;
     well_wk := well_wk_compose ρ.(well_wk) ρ'.(well_wk) ; can_wk := can_wk_compose ρ ρ' |}.
Notation "ρ ∘w ρ'" := (wk_well_wk_compose ρ ρ').

Lemma well_length {Γ Δ : context} (ρ : Γ ≤ Δ) : #|Δ| <= #|Γ|.
Proof.
  destruct ρ as [ρ wellρ _].
  induction wellρ.
  all: cbn ; lia.
Qed.

Definition wk_id_conv {Γ} : wk_to_ren (@wk_id Γ) = id := eq_refl.

Lemma is_canonical_wk_up ρ : 
  is_canonical_wk (_wk_up ρ) -> is_canonical_wk ρ.
Proof.
  destruct ρ; cbn; try discriminate + trivial.
Qed.

(* Testing that the definitions are right *)
Lemma id_ren (Γ : context) (ρ : Γ ≤ Γ) : ρ =1 id.
Proof.
  destruct ρ as [ρ wellρ canρ].
  cbn in *.
  pose proof (@eq_refl _ #|Γ|) as eΓ.
  revert eΓ wellρ.
  generalize Γ at 2 4.
  intros Δ e wellρ.
  induction wellρ in e, canρ |- *.
  all: cbn.
  - reflexivity.
  - pose proof (well_length {| wk := ρ ; well_wk := wellρ ; can_wk := canρ|}).
    now cbn in * ; lia.
  - asimpl.
    setoid_rewrite IHwellρ.
    + now intros [] ; reflexivity.
    + now apply is_canonical_wk_up. 
    + now cbn in * ; lia.
Qed.


Definition wk1 {Γ} nA A : Γ,, vass nA A ≤ Γ := wk_step nA A (wk_id (Γ := Γ)).

Lemma wk1_ren {Γ nA A} : @wk1 Γ nA A =1 ↑.
Proof. reflexivity. Qed.

Lemma wk_up_ren {Γ Δ nA A} (ρ : Δ ≤ Γ) : 
  wk_up nA A ρ =1 upRen_term_term  ρ.
Proof.
  intros; cbn; asimpl.
  destruct ρ as [[] ??]; cbn; now intros [].
Qed.

Lemma map_decl_lift (ρ : weakening) d :
  map_decl (ren_term (up_ren ρ)) (map_decl (ren_term shift) d) =
  map_decl (ren_term shift) (map_decl (ren_term ρ) d).
Proof.
  rewrite ! compose_map_decl.
  eapply map_decl_ext.
  intros t.
  asimpl.
  reflexivity.
Qed.

Lemma in_ctx_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
  in_ctx Γ n decl ->
  in_ctx Δ (ρ n) (map_decl (ren_term ρ) decl).
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ canρ] ; cbn. clear canρ.
  induction wfρ in n, decl, Hdecl |- *.
  - cbn.
    rewrite map_decl_id.
    1: eassumption.
    now asimpl.
  - cbn.
    change ((?ρ >> S) n) with (S (ρ n)).
    replace (map_decl _ _) with (map_decl (ren_term shift) (map_decl (ren_term ρ) decl))
      by (now rewrite compose_map_decl ; asimpl).
    now econstructor.
  - destruct n ; cbn.
    + cbn.
      inversion Hdecl ; subst ; clear Hdecl.
      cbn -[map_decl].
      rewrite map_decl_lift.
      now constructor.
    + inversion Hdecl ; subst ; cbn in *.
      rewrite map_decl_lift.
      now econstructor.
  Qed.

Section RenWlWhnf.

  Context {Γ Δ} (ρ : Δ ≤ Γ).

  Lemma whne_ren_wl t : whne t -> whne (t⟨ρ⟩).
  Proof.
    apply whne_ren.
  Qed.

  Lemma whnf_ren_wl t : whnf t -> whnf (t⟨ρ⟩).
  Proof.
    apply whnf_ren.
  Qed.
  
  Lemma isType_ren_wl A : isType A -> isType (A⟨ρ⟩).
  Proof.
    apply isType_ren.
  Qed.
  
  Lemma isFun_ren_wl f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    apply isFun_ren.
  Qed.

End RenWlWhnf.

#[global] Hint Resolve whne_ren_wl whnf_ren_wl isType_ren_wl isFun_ren_wl : gen_typing.

Lemma wk_id_ren_on Γ (H : term) : H⟨@wk_id Γ⟩ = H.
Proof. cbv -[ren_term]; now asimpl. Qed.


Lemma wk1_ren_on Γ nF F (H : term) : H⟨@wk1 Γ nF F⟩ = H⟨↑⟩.
Proof. reflexivity. Qed.
  
Lemma wk_up_ren_on Γ Δ (ρ : Γ ≤ Δ) nF F (H : term) : H⟨wk_up nF F ρ⟩ = H⟨upRen_term_term ρ⟩.
Proof. now rewrite <- (@wk_up_ren _ _ nF F ρ). Qed.

Lemma wk_up_wk1_ren_on Γ nF F nG G (H : term) : H⟨wk_up nF F (@wk1 Γ nG G)⟩ = H⟨upRen_term_term ↑⟩.
Proof. reflexivity. Qed.

Lemma prod_wk {Γ Δ na dom cod} {ρ : Γ ≤ Δ} : tProd na dom⟨ρ⟩ cod⟨wk_up na dom ρ⟩ = (tProd na dom cod)⟨ρ⟩.
Proof.  now rewrite wk_up_ren_on. Qed.

Lemma arr_wk {Γ Δ A B} (ρ : Γ ≤ Δ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof.  cbn; now asimpl. Qed.

Lemma app_eta_wk {Γ Δ nA A f} (ρ : Γ ≤ Δ) :
 tApp f⟨ρ⟩⟨shift⟩ (tRel 0) = (tApp f⟨shift⟩ (tRel 0))⟨wk_up nA A ρ⟩.
Proof.
  cbn; asimpl; rewrite wk_up_ren; now asimpl.
Qed.

(* Adaptation of Autosubst asimpl to well typed weakenings *)
Ltac bsimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress setoid_rewrite wk_compose_compose
                 | progress setoid_rewrite id_ren
                 | progress setoid_rewrite wk1_ren
                 | progress setoid_rewrite wk_up_ren
                 | progress unfold up_term_term, upRen_term_term, up_ren, wk_well_wk_compose, wk_id, wk_step, wk_up, wk_empty 
                 | progress cbn[subst_term ren_term wk wk_to_ren]
                 | progress fsimpl ]).

Ltac bsimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  Ren1_subst, Ren1_wk, Ren1_well_wk, Ren_decl
                  in *; bsimpl'; minimize.

