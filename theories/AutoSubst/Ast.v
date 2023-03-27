From LogRel.AutoSubst Require Import core unscoped.
From LogRel Require Import BasicAst.
Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive term : Type :=
  | tRel : nat -> term
  | tSort : sort -> term
  | tProd : term -> term -> term
  | tLambda : term -> term -> term
  | tApp : term -> term -> term
  | tNat : term
  | tZero : term
  | tSucc : term -> term
  | tNatElim : term -> term -> term -> term -> term
  | tEmpty : term
  | tEmptyElim : term -> term -> term.

Lemma congr_tSort {s0 : sort} {t0 : sort} (H0 : s0 = t0) :
  tSort s0 = tSort t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tSort x) H0)).
Qed.

Lemma congr_tProd {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tProd s0 s1 = tProd t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tProd x s1) H0))
         (ap (fun x => tProd t0 x) H1)).
Qed.

Lemma congr_tLambda {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tLambda s0 s1 = tLambda t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tLambda x s1) H0))
         (ap (fun x => tLambda t0 x) H1)).
Qed.

Lemma congr_tApp {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tApp s0 s1 = tApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tApp x s1) H0))
         (ap (fun x => tApp t0 x) H1)).
Qed.

Lemma congr_tNat : tNat = tNat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tZero : tZero = tZero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tSucc {s0 : term} {t0 : term} (H0 : s0 = t0) :
  tSucc s0 = tSucc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tSucc x) H0)).
Qed.

Lemma congr_tNatElim {s0 : term} {s1 : term} {s2 : term} {s3 : term}
  {t0 : term} {t1 : term} {t2 : term} {t3 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  tNatElim s0 s1 s2 s3 = tNatElim t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans eq_refl (ap (fun x => tNatElim x s1 s2 s3) H0))
               (ap (fun x => tNatElim t0 x s2 s3) H1))
            (ap (fun x => tNatElim t0 t1 x s3) H2))
         (ap (fun x => tNatElim t0 t1 t2 x) H3)).
Qed.

Lemma congr_tEmpty : tEmpty = tEmpty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tEmptyElim {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tEmptyElim s0 s1 = tEmptyElim t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tEmptyElim x s1) H0))
         (ap (fun x => tEmptyElim t0 x) H1)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | tRel s0 => tRel (xi_term s0)
  | tSort s0 => tSort s0
  | tProd s0 s1 =>
      tProd (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  | tLambda s0 s1 =>
      tLambda (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  | tApp s0 s1 => tApp (ren_term xi_term s0) (ren_term xi_term s1)
  | tNat => tNat
  | tZero => tZero
  | tSucc s0 => tSucc (ren_term xi_term s0)
  | tNatElim s0 s1 s2 s3 =>
      tNatElim (ren_term (upRen_term_term xi_term) s0) (ren_term xi_term s1)
        (ren_term xi_term s2) (ren_term xi_term s3)
  | tEmpty => tEmpty
  | tEmptyElim s0 s1 =>
      tEmptyElim (ren_term (upRen_term_term xi_term) s0)
        (ren_term xi_term s1)
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (tRel var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} : 
term :=
  match s with
  | tRel s0 => sigma_term s0
  | tSort s0 => tSort s0
  | tProd s0 s1 =>
      tProd (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1)
  | tLambda s0 s1 =>
      tLambda (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1)
  | tApp s0 s1 => tApp (subst_term sigma_term s0) (subst_term sigma_term s1)
  | tNat => tNat
  | tZero => tZero
  | tSucc s0 => tSucc (subst_term sigma_term s0)
  | tNatElim s0 s1 s2 s3 =>
      tNatElim (subst_term (up_term_term sigma_term) s0)
        (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3)
  | tEmpty => tEmpty
  | tEmptyElim s0 s1 =>
      tEmptyElim (subst_term (up_term_term sigma_term) s0)
        (subst_term sigma_term s1)
  end.

Lemma upId_term_term (sigma : nat -> term)
  (Eq : forall x, sigma x = tRel x) :
  forall x, up_term_term sigma x = tRel x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = tRel x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | tRel s0 => Eq_term s0
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 => congr_tSucc (idSubst_term sigma_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
        (idSubst_term sigma_term Eq_term s1)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | tRel s0 => ap (tRel) (Eq_term s0)
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 => congr_tSucc (extRen_term xi_term zeta_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | tRel s0 => Eq_term s0
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 => congr_tSucc (ext_term sigma_term tau_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
        (ext_term sigma_term tau_term Eq_term s1)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | tRel s0 => ap (tRel) (Eq_term s0)
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 =>
      congr_tSucc (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | tRel s0 => Eq_term s0
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | tLambda s0 s1 =>
      congr_tLambda
        (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | tApp s0 s1 =>
      congr_tApp (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 =>
      congr_tSucc (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s0) (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s0) (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_term (sigma_term : nat -> term)
(zeta_term : nat -> nat) (theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | tRel s0 => Eq_term s0
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 =>
      congr_tSucc
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_term (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | tRel s0 => Eq_term s0
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 =>
      congr_tSucc
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  end.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (tRel) xi x = sigma x) :
  forall x, funcomp (tRel) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (tRel) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | tRel s0 => Eq_term s0
  | tSort s0 => congr_tSort (eq_refl s0)
  | tProd s0 s1 =>
      congr_tProd (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | tLambda s0 s1 =>
      congr_tLambda (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | tApp s0 s1 =>
      congr_tApp (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tNat => congr_tNat
  | tZero => congr_tZero
  | tSucc s0 => congr_tSucc (rinst_inst_term xi_term sigma_term Eq_term s0)
  | tNatElim s0 s1 s2 s3 =>
      congr_tNatElim
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
  | tEmpty => congr_tEmpty
  | tEmptyElim s0 s1 =>
      congr_tEmptyElim
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  end.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (tRel) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (tRel) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (tRel) s = s.
Proof.
exact (idSubst_term (tRel) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise :
  pointwise_relation _ eq (subst_term (tRel)) id.
Proof.
exact (fun s => idSubst_term (tRel) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (tRel x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (tRel))
    sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (tRel x) = tRel (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (tRel))
    (funcomp (tRel) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

#[global] Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global] Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global] Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global] Instance VarInstance_term : (Var _ _) := @tRel.

Notation "[ sigma_term ]" := (subst_term sigma_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__term" := up_term (only printing) : subst_scope.

Notation "↑__term" := up_term_term (only printing) : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_term xi_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := tRel ( at level 1, only printing) : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
  ( at level 5, format "x __term", only printing) : subst_scope.

Notation "x '__term'" := (tRel x) ( at level 5, format "x __term") :
  subst_scope.

#[global] Instance subst_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global] Instance subst_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global] Instance ren_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global] Instance ren_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
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
                 | progress unfold up_term_term, upRen_term_term, up_ren
                 | progress cbn[subst_term ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term.

End Core.

Module Allfv.

Import
Core.

Lemma upAllfv_term_term (p : nat -> Prop) : nat -> Prop.
Proof.
exact (up_allfv p).
Defined.

Fixpoint allfv_term (p_term : nat -> Prop) (s : term) {struct s} : Prop :=
  match s with
  | tRel s0 => p_term s0
  | tSort s0 => and True True
  | tProd s0 s1 =>
      and (allfv_term p_term s0)
        (and (allfv_term (upAllfv_term_term p_term) s1) True)
  | tLambda s0 s1 =>
      and (allfv_term p_term s0)
        (and (allfv_term (upAllfv_term_term p_term) s1) True)
  | tApp s0 s1 =>
      and (allfv_term p_term s0) (and (allfv_term p_term s1) True)
  | tNat => True
  | tZero => True
  | tSucc s0 => and (allfv_term p_term s0) True
  | tNatElim s0 s1 s2 s3 =>
      and (allfv_term (upAllfv_term_term p_term) s0)
        (and (allfv_term p_term s1)
           (and (allfv_term p_term s2) (and (allfv_term p_term s3) True)))
  | tEmpty => True
  | tEmptyElim s0 s1 =>
      and (allfv_term (upAllfv_term_term p_term) s0)
        (and (allfv_term p_term s1) True)
  end.

Lemma upAllfvTriv_term_term {p : nat -> Prop} (H : forall x, p x) :
  forall x, upAllfv_term_term p x.
Proof.
exact (fun x => match x with
                | S n' => H n'
                | O => I
                end).
Qed.

Fixpoint allfvTriv_term (p_term : nat -> Prop) (H_term : forall x, p_term x)
(s : term) {struct s} : allfv_term p_term s :=
  match s with
  | tRel s0 => H_term s0
  | tSort s0 => conj I I
  | tProd s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj
           (allfvTriv_term (upAllfv_term_term p_term)
              (upAllfvTriv_term_term H_term) s1) I)
  | tLambda s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj
           (allfvTriv_term (upAllfv_term_term p_term)
              (upAllfvTriv_term_term H_term) s1) I)
  | tApp s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  | tNat => I
  | tZero => I
  | tSucc s0 => conj (allfvTriv_term p_term H_term s0) I
  | tNatElim s0 s1 s2 s3 =>
      conj
        (allfvTriv_term (upAllfv_term_term p_term)
           (upAllfvTriv_term_term H_term) s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3) I)))
  | tEmpty => I
  | tEmptyElim s0 s1 =>
      conj
        (allfvTriv_term (upAllfv_term_term p_term)
           (upAllfvTriv_term_term H_term) s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  end.

Lemma upAllfvImpl_term_term {p : nat -> Prop} {q : nat -> Prop}
  (H : forall x, p x -> q x) :
  forall x, upAllfv_term_term p x -> upAllfv_term_term q x.
Proof.
exact (fun x => match x with
                | S n' => H n'
                | O => fun Hp => Hp
                end).
Qed.

Fixpoint allfvImpl_term (p_term : nat -> Prop) (q_term : nat -> Prop)
(H_term : forall x, p_term x -> q_term x) (s : term) {struct s} :
allfv_term p_term s -> allfv_term q_term s :=
  match s with
  | tRel s0 => fun HP => H_term s0 HP
  | tSort s0 => fun HP => conj I I
  | tProd s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term (upAllfv_term_term p_term)
              (upAllfv_term_term q_term) (upAllfvImpl_term_term H_term) s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | tLambda s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term (upAllfv_term_term p_term)
              (upAllfv_term_term q_term) (upAllfvImpl_term_term H_term) s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | tApp s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | tNat => fun HP => I
  | tZero => fun HP => I
  | tSucc s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | tNatElim s0 s1 s2 s3 =>
      fun HP =>
      conj
        (allfvImpl_term (upAllfv_term_term p_term) (upAllfv_term_term q_term)
           (upAllfvImpl_term_term H_term) s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end)
           (conj
              (allfvImpl_term p_term q_term H_term s2
                 match HP with
                 | conj _ HP =>
                     match HP with
                     | conj _ HP => match HP with
                                    | conj HP _ => HP
                                    end
                     end
                 end)
              (conj
                 (allfvImpl_term p_term q_term H_term s3
                    match HP with
                    | conj _ HP =>
                        match HP with
                        | conj _ HP =>
                            match HP with
                            | conj _ HP =>
                                match HP with
                                | conj HP _ => HP
                                end
                            end
                        end
                    end) I)))
  | tEmpty => fun HP => I
  | tEmptyElim s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term (upAllfv_term_term p_term) (upAllfv_term_term q_term)
           (upAllfvImpl_term_term H_term) s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_term p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  end.

Lemma upAllfvRenL_term_term (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
  upAllfv_term_term p (upRen_term_term xi x) ->
  upAllfv_term_term (funcomp p xi) x.
Proof.
exact (fun x => match x with
                | S n' => fun i => i
                | O => fun H => H
                end).
Qed.

Fixpoint allfvRenL_term (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : term) {struct s} :
allfv_term p_term (ren_term xi_term s) ->
allfv_term (funcomp p_term xi_term) s :=
  match s with
  | tRel s0 => fun H => H
  | tSort s0 => fun H => conj I I
  | tProd s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvImpl_term _ _ (upAllfvRenL_term_term p_term xi_term) s1
              (allfvRenL_term (upAllfv_term_term p_term)
                 (upRen_term_term xi_term) s1
                 match H with
                 | conj _ H => match H with
                               | conj H _ => H
                               end
                 end)) I)
  | tLambda s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvImpl_term _ _ (upAllfvRenL_term_term p_term xi_term) s1
              (allfvRenL_term (upAllfv_term_term p_term)
                 (upRen_term_term xi_term) s1
                 match H with
                 | conj _ H => match H with
                               | conj H _ => H
                               end
                 end)) I)
  | tApp s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tNat => fun H => I
  | tZero => fun H => I
  | tSucc s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tNatElim s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvImpl_term _ _ (upAllfvRenL_term_term p_term xi_term) s0
           (allfvRenL_term (upAllfv_term_term p_term)
              (upRen_term_term xi_term) s0 match H with
                                           | conj H _ => H
                                           end))
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenL_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenL_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end) I)))
  | tEmpty => fun H => I
  | tEmptyElim s0 s1 =>
      fun H =>
      conj
        (allfvImpl_term _ _ (upAllfvRenL_term_term p_term xi_term) s0
           (allfvRenL_term (upAllfv_term_term p_term)
              (upRen_term_term xi_term) s0 match H with
                                           | conj H _ => H
                                           end))
        (conj
           (allfvRenL_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  end.

Lemma upAllfvRenR_term_term (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
  upAllfv_term_term (funcomp p xi) x ->
  upAllfv_term_term p (upRen_term_term xi x).
Proof.
exact (fun x => match x with
                | S n' => fun i => i
                | O => fun H => H
                end).
Qed.

Fixpoint allfvRenR_term (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : term) {struct s} :
allfv_term (funcomp p_term xi_term) s ->
allfv_term p_term (ren_term xi_term s) :=
  match s with
  | tRel s0 => fun H => H
  | tSort s0 => fun H => conj I I
  | tProd s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term (upAllfv_term_term p_term)
              (upRen_term_term xi_term) s1
              (allfvImpl_term _ _ (upAllfvRenR_term_term p_term xi_term) s1
                 match H with
                 | conj _ H => match H with
                               | conj H _ => H
                               end
                 end)) I)
  | tLambda s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term (upAllfv_term_term p_term)
              (upRen_term_term xi_term) s1
              (allfvImpl_term _ _ (upAllfvRenR_term_term p_term xi_term) s1
                 match H with
                 | conj _ H => match H with
                               | conj H _ => H
                               end
                 end)) I)
  | tApp s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tNat => fun H => I
  | tZero => fun H => I
  | tSucc s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tNatElim s0 s1 s2 s3 =>
      fun H =>
      conj
        (allfvRenR_term (upAllfv_term_term p_term) (upRen_term_term xi_term)
           s0
           (allfvImpl_term _ _ (upAllfvRenR_term_term p_term xi_term) s0
              match H with
              | conj H _ => H
              end))
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end)
           (conj
              (allfvRenR_term p_term xi_term s2
                 match H with
                 | conj _ H =>
                     match H with
                     | conj _ H => match H with
                                   | conj H _ => H
                                   end
                     end
                 end)
              (conj
                 (allfvRenR_term p_term xi_term s3
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H =>
                            match H with
                            | conj _ H => match H with
                                          | conj H _ => H
                                          end
                            end
                        end
                    end) I)))
  | tEmpty => fun H => I
  | tEmptyElim s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term (upAllfv_term_term p_term) (upRen_term_term xi_term)
           s0
           (allfvImpl_term _ _ (upAllfvRenR_term_term p_term xi_term) s0
              match H with
              | conj H _ => H
              end))
        (conj
           (allfvRenR_term p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  end.

End Allfv.

Module Extra.

Import Core.

#[export]Hint Opaque subst_term: rewrite.

#[export]Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Allfv.

Export Extra.

End interface.

Export interface.

