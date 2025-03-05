(** * LogRel.Weakening: definition of well-formed weakenings, and some properties. *)
From Coq Require Import Lia ssrbool RelationClasses.
From LogRel Require Import Utils AutoSubst.Extra AutoSubst.RAsimpl AutoSubst.AstRasimpl.
From LogRel.Syntax Require Import BasicAst Notations Context NormalForms WeakeningDef.

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

  Lemma isPosType_ren_wl A : isPosType A -> isPosType (A⟨ρ⟩).
  Proof.
    apply isPosType_ren.
  Qed.

  Lemma isFun_ren_wl f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    apply isFun_ren.
  Qed.

  Lemma isPair_ren_wl f : isPair f -> isPair (f⟨ρ⟩).
  Proof.
    apply isPair_ren.
  Qed.

  Lemma isCanonical_ren_wl t : isCanonical t <~> isCanonical (t⟨ρ⟩).
  Proof.
    symmetry.
    apply isCanonical_ren.
  Qed.

End RenWlWhnf.

#[global] Hint Resolve whne_ren_wl whnf_ren_wl isType_ren_wl isPosType_ren_wl isFun_ren_wl isCanonical_ren_wl : gen_typing.


(** ** Weakenings play well with context access *)

Lemma in_ctx_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
  in_ctx Γ n decl ->
  in_ctx Δ (ρ n) (decl⟨ρ⟩).
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ] ; cbn in *.
  induction wfρ in n, decl, Hdecl |- *.
  - inversion Hdecl.
  - cbn.
    replace (decl⟨_⟩) with (decl⟨ρ⟩⟨↑⟩) by now rasimpl.
    now econstructor.
  - destruct n ; cbn.
    + inversion Hdecl ; subst ; clear Hdecl.
      replace (A⟨↑⟩⟨_⟩) with (A⟨ρ⟩⟨↑⟩) by now (rasimpl;cbn; rasimpl).
      now constructor.
    + inversion Hdecl ; subst ; cbn in * ; refold.
      replace (d⟨_⟩⟨_⟩) with (d⟨ρ⟩⟨↑⟩) by now (rasimpl; cbn; rasimpl).
      now econstructor.
Qed.

Lemma in_ctx_str (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
  in_ctx Δ (ρ n) decl ->
  ∑ decl', decl = decl'⟨ρ⟩ × in_ctx Γ n decl'.
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ] ; cbn in *.
  induction wfρ in n, decl, Hdecl |- *.
  - inversion Hdecl.
  - cbn in *.
    inversion Hdecl ; subst.
    edestruct IHwfρ as [? []]; tea ; subst.
    eexists ; split ; tea.
    now rasimpl.
  - destruct n ; cbn in *.
  + inversion Hdecl ; subst ; clear Hdecl.
    eexists ; split.
    2: now constructor.
    rasimpl; cbn; now rasimpl.
  + inversion Hdecl ; subst ; clear Hdecl ; cbn in *.
    edestruct IHwfρ as [? []]; tea ; subst.
    eexists ; split.
    2: now econstructor.
    rasimpl; cbn; now rasimpl.
Qed.



(** Subst lemmas *)

Lemma arr_ren1 {A B} (ρ : nat -> nat) : (arr A B)⟨ρ⟩ = arr A⟨ρ⟩ B⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma subst_arr A B σ : (arr A B)[σ] = arr A[σ] B[σ].
Proof. now rasimpl. Qed.

Lemma subst_prod X Y σ : (tProd X Y)[σ] = tProd X[σ] Y[up_term_term σ].
Proof. now rasimpl. Qed.

Lemma subst_sig X Y σ : (tSig X Y)[σ] = tSig X[σ] Y[up_term_term σ].
Proof. now rasimpl. Qed.

Lemma shift_up_eq {t σ} : t⟨↑⟩[up_term_term σ] = t[σ]⟨↑⟩.
Proof. now rasimpl. Qed.

Lemma shift_one_eq t a : t⟨↑⟩[a..] = t.
Proof. now rasimpl. Qed.

Lemma up_single_subst {t σ u} : t[up_term_term σ][u..] = t[u .:  σ].
Proof.  now rasimpl. Qed.

Lemma eta_up_single_subst A σ : A[up_term_term (↑ >> σ)][(σ var_zero)..] = A[σ].
Proof. rasimpl; now rewrite scons_eta'. Qed.

Lemma subst_rel t : t[tRel] = t.
Proof. now rasimpl. Qed.

Lemma singleSubstComm G t σ : G[t..][σ] = G[t[σ] .: σ].
Proof. now rasimpl. Qed.

Lemma singleSubstComm' G t σ : G[t..][σ] = G[up_term_term σ][t[σ]..].
Proof. now rasimpl. Qed.


Lemma up_liftSubst_eq {σ t u} : t[up_term_term σ][u]⇑ = t[u .: ↑ >> up_term_term σ].
Proof. now rasimpl. Qed.

Lemma liftSubst_scons_eq {t u v: term} σ : t[u]⇑[v .: σ] = t[u[v .: σ] .: σ].
Proof. now rasimpl. Qed.




(** Lemmas for easier rewriting *)


Lemma subst_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P⟨wk_up A ρ⟩[n⟨ρ⟩..].
Proof.
  now rasimpl.
Qed.

Lemma subst1_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ) : P[n .: ρ >> tRel] = P⟨wk_up A ρ⟩[n..].
Proof. now rasimpl. Qed.

Lemma subst_ren_wk_up2 {Γ Δ P A B a b} (ρ : Γ ≤ Δ):
  P[a .: b..]⟨ρ⟩ = P⟨wk_up A (wk_up B ρ)⟩[a⟨ρ⟩ .: b⟨ρ⟩..].
Proof. now rasimpl. Qed.

Lemma subst_ren_subst_mixed {Γ Δ P n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P[n⟨ρ⟩ .: ρ >> tRel].
Proof. now rasimpl. Qed.

Lemma subst_ren_subst_mixed2 {Γ Δ P a b} (ρ : Γ ≤ Δ): P[a .: b..]⟨ρ⟩ = P[a⟨ρ⟩ .: (b⟨ρ⟩ .: ρ >> tRel)].
Proof. now rasimpl. Qed.


Lemma wk_up_ren_subst {Γ Δ Ξ P A n}  (ρ : Γ ≤ Δ) (ρ' : Δ ≤ Ξ) :
  P[n .: ρ ∘w ρ' >> tRel] = P⟨wk_up A ρ'⟩[n .: ρ >> tRel].
Proof. now rasimpl. Qed.

Lemma shift_subst_scons {B a Γ Δ} (ρ : Δ ≤ Γ) : B⟨↑⟩[a .: ρ >> tRel] = B⟨ρ⟩.
Proof. rasimpl; now rewrite rinstInst'_term. Qed.

Lemma shift_subst1 {B a} : B⟨↑⟩[a..] = B.
Proof. now rasimpl. Qed.

Lemma shift_upRen ρ t : t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨upRen_term_term ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_comp_ren_on {Γ Δ Ξ} (H : term) (ρ1 : Γ ≤ Δ) (ρ2 : Δ ≤ Ξ) :
  H⟨ρ2⟩⟨ρ1⟩ = H⟨ρ1 ∘w ρ2⟩.
Proof. now rasimpl. Qed.

Lemma wk_id_ren_on Γ (H : term) : H⟨@wk_id Γ⟩ = H.
Proof. now rasimpl. Qed.

Lemma wk1_ren_on Γ F (H : term) : H⟨@wk1 Γ F⟩ = H⟨↑⟩.
Proof. now rasimpl. Qed.

Lemma wk_up_ren_on Γ Δ (ρ : Γ ≤ Δ) F (H : term) : H⟨wk_up F ρ⟩ = H⟨upRen_term_term ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_up_wk1_ren_on Γ F G (H : term) : H⟨wk_up F (@wk1 Γ G)⟩ = H⟨upRen_term_term ↑⟩.
Proof. now rasimpl. Qed.

Lemma wk_arr {A B Γ Δ} (ρ : Δ ≤ Γ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_elimSuccHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimSuccHypTy P⟨wk_up A ρ⟩ = (elimSuccHypTy P)⟨ρ⟩.
Proof.
  unfold elimSuccHypTy; cbn; f_equal; now rasimpl.
Qed.

Lemma wk_prod {A B Γ Δ} (ρ : Δ ≤ Γ) : tProd A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tProd A B)⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_lam {A t Γ Δ} (ρ : Δ ≤ Γ) : tLambda A⟨ρ⟩ t⟨wk_up A ρ⟩ = (tLambda A t)⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_sig {A B Γ Δ} (ρ : Δ ≤ Γ) : tSig A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tSig A B)⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_pair {A B a b Γ Δ} (ρ : Δ ≤ Γ) : tPair A⟨ρ⟩ B⟨wk_up A ρ⟩ a⟨ρ⟩ b⟨ρ⟩ = (tPair A B a b)⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_fst {p Γ Δ} (ρ : Δ ≤ Γ) : tFst p⟨ρ⟩ = (tFst p)⟨ρ⟩.
Proof. now cbn. Qed.

Lemma wk_snd {p Γ Δ} (ρ : Δ ≤ Γ) : tSnd p⟨ρ⟩ = (tSnd p)⟨ρ⟩.
Proof. now cbn. Qed.

Lemma wk_comp {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp A f g)⟨ρ⟩ = comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_Id {A x y Γ Δ} (ρ : Δ ≤ Γ) : tId A⟨ρ⟩ x⟨ρ⟩ y⟨ρ⟩ = (tId A x y)⟨ρ⟩.
Proof. now cbn. Qed.

Lemma wk_refl {A x Γ Δ} (ρ : Δ ≤ Γ) : tRefl A⟨ρ⟩ x⟨ρ⟩ = (tRefl A x)⟨ρ⟩.
Proof. now cbn. Qed.


Lemma wk_step_wk1 {A t Γ Δ} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟩ = t⟨wk_step A ρ⟩.
Proof. now rasimpl. Qed.

Lemma wk_up_wk1 {A t Γ Δ} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟨ρ⟩⟩ = t⟨@wk1 Γ A⟩⟨wk_up A ρ⟩.
Proof. now rasimpl. Qed.


Lemma wk_idElim {A x P hr y e Δ Γ} (ρ : Δ ≤ Γ) :
  tIdElim A⟨ρ⟩ x⟨ρ⟩ P⟨wk_up (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) (wk_up A ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩ = (tIdElim A x P hr y e)⟨ρ⟩.
Proof.  now cbn. Qed.


(* TODO: fix the triggers in rasimpl to solve these cases as well *)
Ltac solve_wk_eq :=
  aunfold ;
  lazymatch goal with | |- wk_to_ren (wk ?r) =1 wk_to_ren (wk ?r') =>
    let qr := quote_wk r in
    let qr' := quote_wk r' in
    simple refine (transitivity (eval_quoted_wk qr) (transitivity _ (symmetry (eval_quoted_wk qr'))));
    cbn
  end.

Lemma wk_comp_lunit {Γ Δ} (ρ : Δ ≤ Γ) : wk_id ∘w ρ =1 ρ.
Proof. now solve_wk_eq. Qed.

Lemma wk_comp_runit {Γ Δ} (ρ : Δ ≤ Γ) : ρ ∘w wk_id =1 ρ.
Proof. now solve_wk_eq. Qed.

Lemma wk_comp_assoc {Γ Δ Ξ ζ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) (ρ'' : ζ ≤ Ξ) :
  (ρ'' ∘w ρ') ∘w ρ =1 ρ'' ∘w (ρ' ∘w ρ).
Proof. now solve_wk_eq. Qed.

Lemma wk1_irr {Γ Γ' A A' t} : t⟨@wk1 Γ A⟩ = t⟨@wk1 Γ' A'⟩.
Proof. now rasimpl. Qed.

Lemma var0_wk1_id {Γ A t} : t[tRel 0 .: @wk1 Γ A >> tRel] = t.
Proof. rasimpl;  rewrite scons_eta'. now rasimpl. Qed.

Lemma eq_subst_scons {Γ} a B : B[a..] = B[a⟨@wk_id Γ⟩ .: @wk_id Γ >> tRel].
Proof. now rasimpl. Qed.

Lemma wk1_subst A Γ F σ : (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ].
Proof. now rasimpl. Qed.

Lemma ren_subst  {Γ Δ} A (ρ : Γ ≤ Δ) σ : A⟨ρ⟩[σ] = A[ ρ >> σ].
Proof.
  now rasimpl.
Qed.

Lemma liftSubstComm Γ F G t σ : G[t]⇑[σ] = G[t[σ] .: @wk1 Γ F >> σ].
Proof. now rasimpl. Qed.