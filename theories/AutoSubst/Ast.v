From LogRel.AutoSubst Require Import core unscoped.
From LogRel Require Import BasicAst.
From Coq Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive typeLF : Type :=
    lfArr : typeLF -> typeLF -> typeLF.

Lemma congr_lfArr {s0 : typeLF} {s1 : typeLF} {t0 : typeLF} {t1 : typeLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : lfArr s0 s1 = lfArr t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lfArr x s1) H0))
         (ap (fun x => lfArr t0 x) H1)).
Qed.

Inductive ctxLF : Type :=
  | lfCtxEmpty : ctxLF
  | lfCtxCons : ctxLF -> typeLF -> ctxLF.

Lemma congr_lfCtxEmpty : lfCtxEmpty = lfCtxEmpty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_lfCtxCons {s0 : ctxLF} {s1 : typeLF} {t0 : ctxLF} {t1 : typeLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : lfCtxCons s0 s1 = lfCtxCons t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lfCtxCons x s1) H0))
         (ap (fun x => lfCtxCons t0 x) H1)).
Qed.

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
  | tEmptyElim : term -> term -> term
  | tSig : term -> term -> term
  | tPair : term -> term -> term -> term -> term
  | tFst : term -> term
  | tSnd : term -> term
  | tId : term -> term -> term -> term
  | tRefl : term -> term -> term
  | tIdElim : term -> term -> term -> term -> term -> term -> term
  | tCtx : term
  | tBox : ctxLF -> typeLF -> term
  | tQuote : ctxLF -> termLF -> term
  | tBoxRec : term -> term -> term -> term -> ctxLF -> term -> term
with termLF : Type :=
  | lfLam : typeLF -> termLF -> termLF
  | lfApp : termLF -> termLF -> termLF
  | lfSplice : term -> subLF -> termLF
with subLF : Type :=
  | lfSubEmpty : subLF
  | lfWk : ctxLF -> subLF
  | lfSubCons : subLF -> termLF -> subLF.

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

Lemma congr_tSig {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tSig s0 s1 = tSig t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tSig x s1) H0))
         (ap (fun x => tSig t0 x) H1)).
Qed.

Lemma congr_tPair {s0 : term} {s1 : term} {s2 : term} {s3 : term} {t0 : term}
  {t1 : term} {t2 : term} {t3 : term} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) : tPair s0 s1 s2 s3 = tPair t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => tPair x s1 s2 s3) H0))
               (ap (fun x => tPair t0 x s2 s3) H1))
            (ap (fun x => tPair t0 t1 x s3) H2))
         (ap (fun x => tPair t0 t1 t2 x) H3)).
Qed.

Lemma congr_tFst {s0 : term} {t0 : term} (H0 : s0 = t0) : tFst s0 = tFst t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tFst x) H0)).
Qed.

Lemma congr_tSnd {s0 : term} {t0 : term} (H0 : s0 = t0) : tSnd s0 = tSnd t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tSnd x) H0)).
Qed.

Lemma congr_tId {s0 : term} {s1 : term} {s2 : term} {t0 : term} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tId s0 s1 s2 = tId t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tId x s1 s2) H0))
            (ap (fun x => tId t0 x s2) H1)) (ap (fun x => tId t0 t1 x) H2)).
Qed.

Lemma congr_tRefl {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tRefl s0 s1 = tRefl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tRefl x s1) H0))
         (ap (fun x => tRefl t0 x) H1)).
Qed.

Lemma congr_tIdElim {s0 : term} {s1 : term} {s2 : term} {s3 : term}
  {s4 : term} {s5 : term} {t0 : term} {t1 : term} {t2 : term} {t3 : term}
  {t4 : term} {t5 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  tIdElim s0 s1 s2 s3 s4 s5 = tIdElim t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => tIdElim x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => tIdElim t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => tIdElim t0 t1 x s3 s4 s5) H2))
               (ap (fun x => tIdElim t0 t1 t2 x s4 s5) H3))
            (ap (fun x => tIdElim t0 t1 t2 t3 x s5) H4))
         (ap (fun x => tIdElim t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_tCtx : tCtx = tCtx.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tBox {s0 : ctxLF} {s1 : typeLF} {t0 : ctxLF} {t1 : typeLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : tBox s0 s1 = tBox t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tBox x s1) H0))
         (ap (fun x => tBox t0 x) H1)).
Qed.

Lemma congr_tQuote {s0 : ctxLF} {s1 : termLF} {t0 : ctxLF} {t1 : termLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : tQuote s0 s1 = tQuote t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tQuote x s1) H0))
         (ap (fun x => tQuote t0 x) H1)).
Qed.

Lemma congr_tBoxRec {s0 : term} {s1 : term} {s2 : term} {s3 : term}
  {s4 : ctxLF} {s5 : term} {t0 : term} {t1 : term} {t2 : term} {t3 : term}
  {t4 : ctxLF} {t5 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  tBoxRec s0 s1 s2 s3 s4 s5 = tBoxRec t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => tBoxRec x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => tBoxRec t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => tBoxRec t0 t1 x s3 s4 s5) H2))
               (ap (fun x => tBoxRec t0 t1 t2 x s4 s5) H3))
            (ap (fun x => tBoxRec t0 t1 t2 t3 x s5) H4))
         (ap (fun x => tBoxRec t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma congr_lfLam {s0 : typeLF} {s1 : termLF} {t0 : typeLF} {t1 : termLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : lfLam s0 s1 = lfLam t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lfLam x s1) H0))
         (ap (fun x => lfLam t0 x) H1)).
Qed.

Lemma congr_lfApp {s0 : termLF} {s1 : termLF} {t0 : termLF} {t1 : termLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : lfApp s0 s1 = lfApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lfApp x s1) H0))
         (ap (fun x => lfApp t0 x) H1)).
Qed.

Lemma congr_lfSplice {s0 : term} {s1 : subLF} {t0 : term} {t1 : subLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : lfSplice s0 s1 = lfSplice t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lfSplice x s1) H0))
         (ap (fun x => lfSplice t0 x) H1)).
Qed.

Lemma congr_lfSubEmpty : lfSubEmpty = lfSubEmpty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_lfWk {s0 : ctxLF} {t0 : ctxLF} (H0 : s0 = t0) : lfWk s0 = lfWk t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lfWk x) H0)).
Qed.

Lemma congr_lfSubCons {s0 : subLF} {s1 : termLF} {t0 : subLF} {t1 : termLF}
  (H0 : s0 = t0) (H1 : s1 = t1) : lfSubCons s0 s1 = lfSubCons t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lfSubCons x s1) H0))
         (ap (fun x => lfSubCons t0 x) H1)).
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
  | tSig s0 s1 =>
      tSig (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  | tPair s0 s1 s2 s3 =>
      tPair (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
        (ren_term xi_term s2) (ren_term xi_term s3)
  | tFst s0 => tFst (ren_term xi_term s0)
  | tSnd s0 => tSnd (ren_term xi_term s0)
  | tId s0 s1 s2 =>
      tId (ren_term xi_term s0) (ren_term xi_term s1) (ren_term xi_term s2)
  | tRefl s0 s1 => tRefl (ren_term xi_term s0) (ren_term xi_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      tIdElim (ren_term xi_term s0) (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3) (ren_term xi_term s4) (ren_term xi_term s5)
  | tCtx => tCtx
  | tBox s0 s1 => tBox s0 s1
  | tQuote s0 s1 => tQuote s0 (ren_termLF xi_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      tBoxRec (ren_term (upRen_term_term (upRen_term_term xi_term)) s0)
        (ren_term xi_term s1) (ren_term xi_term s2) (ren_term xi_term s3) s4
        (ren_term xi_term s5)
  end
with ren_termLF (xi_term : nat -> nat) (s : termLF) {struct s} : termLF :=
  match s with
  | lfLam s0 s1 => lfLam s0 (ren_termLF xi_term s1)
  | lfApp s0 s1 => lfApp (ren_termLF xi_term s0) (ren_termLF xi_term s1)
  | lfSplice s0 s1 => lfSplice (ren_term xi_term s0) (ren_subLF xi_term s1)
  end
with ren_subLF (xi_term : nat -> nat) (s : subLF) {struct s} : subLF :=
  match s with
  | lfSubEmpty => lfSubEmpty
  | lfWk s0 => lfWk s0
  | lfSubCons s0 s1 =>
      lfSubCons (ren_subLF xi_term s0) (ren_termLF xi_term s1)
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
  | tSig s0 s1 =>
      tSig (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1)
  | tPair s0 s1 s2 s3 =>
      tPair (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3)
  | tFst s0 => tFst (subst_term sigma_term s0)
  | tSnd s0 => tSnd (subst_term sigma_term s0)
  | tId s0 s1 s2 =>
      tId (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term sigma_term s2)
  | tRefl s0 s1 =>
      tRefl (subst_term sigma_term s0) (subst_term sigma_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      tIdElim (subst_term sigma_term s0) (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5)
  | tCtx => tCtx
  | tBox s0 s1 => tBox s0 s1
  | tQuote s0 s1 => tQuote s0 (subst_termLF sigma_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      tBoxRec (subst_term (up_term_term (up_term_term sigma_term)) s0)
        (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3) s4 (subst_term sigma_term s5)
  end
with subst_termLF (sigma_term : nat -> term) (s : termLF) {struct s} : 
termLF :=
  match s with
  | lfLam s0 s1 => lfLam s0 (subst_termLF sigma_term s1)
  | lfApp s0 s1 =>
      lfApp (subst_termLF sigma_term s0) (subst_termLF sigma_term s1)
  | lfSplice s0 s1 =>
      lfSplice (subst_term sigma_term s0) (subst_subLF sigma_term s1)
  end
with subst_subLF (sigma_term : nat -> term) (s : subLF) {struct s} : 
subLF :=
  match s with
  | lfSubEmpty => lfSubEmpty
  | lfWk s0 => lfWk s0
  | lfSubCons s0 s1 =>
      lfSubCons (subst_subLF sigma_term s0) (subst_termLF sigma_term s1)
  end.

Lemma upId_term_term (sigma : nat -> term) (Eq : forall x, sigma x = tRel x)
  : forall x, up_term_term sigma x = tRel x.
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
  | tSig s0 s1 =>
      congr_tSig (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
  | tFst s0 => congr_tFst (idSubst_term sigma_term Eq_term s0)
  | tSnd s0 => congr_tSnd (idSubst_term sigma_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s2)
        (idSubst_term sigma_term Eq_term s3)
        (idSubst_term sigma_term Eq_term s4)
        (idSubst_term sigma_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0) (idSubst_termLF sigma_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (idSubst_term (up_term_term (up_term_term sigma_term))
           (upId_term_term _ (upId_term_term _ Eq_term)) s0)
        (idSubst_term sigma_term Eq_term s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3) (eq_refl s4)
        (idSubst_term sigma_term Eq_term s5)
  end
with idSubst_termLF (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = tRel x) (s : termLF) {struct s} :
subst_termLF sigma_term s = s :=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0) (idSubst_termLF sigma_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp (idSubst_termLF sigma_term Eq_term s0)
        (idSubst_termLF sigma_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice (idSubst_term sigma_term Eq_term s0)
        (idSubst_subLF sigma_term Eq_term s1)
  end
with idSubst_subLF (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = tRel x) (s : subLF) {struct s} :
subst_subLF sigma_term s = s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons (idSubst_subLF sigma_term Eq_term s0)
        (idSubst_termLF sigma_term Eq_term s1)
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
  | tSig s0 s1 =>
      congr_tSig (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
  | tFst s0 => congr_tFst (extRen_term xi_term zeta_term Eq_term s0)
  | tSnd s0 => congr_tSnd (extRen_term xi_term zeta_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s2)
        (extRen_term xi_term zeta_term Eq_term s3)
        (extRen_term xi_term zeta_term Eq_term s4)
        (extRen_term xi_term zeta_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0) (extRen_termLF xi_term zeta_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (extRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upExtRen_term_term _ _ (upExtRen_term_term _ _ Eq_term)) s0)
        (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3) (eq_refl s4)
        (extRen_term xi_term zeta_term Eq_term s5)
  end
with extRen_termLF (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : termLF) {struct s} :
ren_termLF xi_term s = ren_termLF zeta_term s :=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0) (extRen_termLF xi_term zeta_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp (extRen_termLF xi_term zeta_term Eq_term s0)
        (extRen_termLF xi_term zeta_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_subLF xi_term zeta_term Eq_term s1)
  end
with extRen_subLF (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : subLF) {struct s} :
ren_subLF xi_term s = ren_subLF zeta_term s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons (extRen_subLF xi_term zeta_term Eq_term s0)
        (extRen_termLF xi_term zeta_term Eq_term s1)
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
  | tSig s0 s1 =>
      congr_tSig (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
  | tFst s0 => congr_tFst (ext_term sigma_term tau_term Eq_term s0)
  | tSnd s0 => congr_tSnd (ext_term sigma_term tau_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s2)
        (ext_term sigma_term tau_term Eq_term s3)
        (ext_term sigma_term tau_term Eq_term s4)
        (ext_term sigma_term tau_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0) (ext_termLF sigma_term tau_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (ext_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (upExt_term_term _ _ (upExt_term_term _ _ Eq_term)) s0)
        (ext_term sigma_term tau_term Eq_term s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3) (eq_refl s4)
        (ext_term sigma_term tau_term Eq_term s5)
  end
with ext_termLF (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : termLF) {struct s} :
subst_termLF sigma_term s = subst_termLF tau_term s :=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0) (ext_termLF sigma_term tau_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp (ext_termLF sigma_term tau_term Eq_term s0)
        (ext_termLF sigma_term tau_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice (ext_term sigma_term tau_term Eq_term s0)
        (ext_subLF sigma_term tau_term Eq_term s1)
  end
with ext_subLF (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : subLF) {struct s} :
subst_subLF sigma_term s = subst_subLF tau_term s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons (ext_subLF sigma_term tau_term Eq_term s0)
        (ext_termLF sigma_term tau_term Eq_term s1)
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
  | tSig s0 s1 =>
      congr_tSig (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
  | tFst s0 =>
      congr_tFst (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | tSnd s0 =>
      congr_tSnd (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0)
        (compRenRen_termLF xi_term zeta_term rho_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (compRenRen_term (upRen_term_term (upRen_term_term xi_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (upRen_term_term (upRen_term_term rho_term))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_term)) s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3) (eq_refl s4)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s5)
  end
with compRenRen_termLF (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : termLF)
{struct s} :
ren_termLF zeta_term (ren_termLF xi_term s) = ren_termLF rho_term s :=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0)
        (compRenRen_termLF xi_term zeta_term rho_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp (compRenRen_termLF xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_termLF xi_term zeta_term rho_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_subLF xi_term zeta_term rho_term Eq_term s1)
  end
with compRenRen_subLF (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : subLF)
{struct s} : ren_subLF zeta_term (ren_subLF xi_term s) = ren_subLF rho_term s
:=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons
        (compRenRen_subLF xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_termLF xi_term zeta_term rho_term Eq_term s1)
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
  | tSig s0 s1 =>
      congr_tSig (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1) (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
  | tFst s0 =>
      congr_tFst (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | tSnd s0 =>
      congr_tSnd (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim
        (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term)) s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0)
        (compRenSubst_termLF xi_term tau_term theta_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (compRenSubst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_ren_subst_term_term _ _ _
              (up_ren_subst_term_term _ _ _ Eq_term)) s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
        (eq_refl s4)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s5)
  end
with compRenSubst_termLF (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : termLF)
{struct s} :
subst_termLF tau_term (ren_termLF xi_term s) = subst_termLF theta_term s :=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0)
        (compRenSubst_termLF xi_term tau_term theta_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp
        (compRenSubst_termLF xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_termLF xi_term tau_term theta_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice
        (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_subLF xi_term tau_term theta_term Eq_term s1)
  end
with compRenSubst_subLF (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : subLF)
{struct s} :
subst_subLF tau_term (ren_subLF xi_term s) = subst_subLF theta_term s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons
        (compRenSubst_subLF xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_termLF xi_term tau_term theta_term Eq_term s1)
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
  | tSig s0 s1 =>
      congr_tSig
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
  | tFst s0 =>
      congr_tFst
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | tSnd s0 =>
      congr_tSnd
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term)) s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0)
        (compSubstRen_termLF sigma_term zeta_term theta_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (compSubstRen_term (up_term_term (up_term_term sigma_term))
           (upRen_term_term (upRen_term_term zeta_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_ren_term_term _ _ _
              (up_subst_ren_term_term _ _ _ Eq_term)) s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
        (eq_refl s4)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s5)
  end
with compSubstRen_termLF (sigma_term : nat -> term) (zeta_term : nat -> nat)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : termLF) {struct s} :
ren_termLF zeta_term (subst_termLF sigma_term s) = subst_termLF theta_term s
:=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0)
        (compSubstRen_termLF sigma_term zeta_term theta_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp
        (compSubstRen_termLF sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_termLF sigma_term zeta_term theta_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_subLF sigma_term zeta_term theta_term Eq_term s1)
  end
with compSubstRen_subLF (sigma_term : nat -> term) (zeta_term : nat -> nat)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : subLF) {struct s} :
ren_subLF zeta_term (subst_subLF sigma_term s) = subst_subLF theta_term s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons
        (compSubstRen_subLF sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_termLF sigma_term zeta_term theta_term Eq_term s1)
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
  | tSig s0 s1 =>
      congr_tSig
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
  | tFst s0 =>
      congr_tFst
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | tSnd s0 =>
      congr_tSnd
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term)) s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0)
        (compSubstSubst_termLF sigma_term tau_term theta_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (compSubstSubst_term (up_term_term (up_term_term sigma_term))
           (up_term_term (up_term_term tau_term))
           (up_term_term (up_term_term theta_term))
           (up_subst_subst_term_term _ _ _
              (up_subst_subst_term_term _ _ _ Eq_term)) s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
        (eq_refl s4)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s5)
  end
with compSubstSubst_termLF (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : termLF) {struct s} :
subst_termLF tau_term (subst_termLF sigma_term s) = subst_termLF theta_term s
:=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0)
        (compSubstSubst_termLF sigma_term tau_term theta_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp
        (compSubstSubst_termLF sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_termLF sigma_term tau_term theta_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_subLF sigma_term tau_term theta_term Eq_term s1)
  end
with compSubstSubst_subLF (sigma_term : nat -> term) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : subLF) {struct s} :
subst_subLF tau_term (subst_subLF sigma_term s) = subst_subLF theta_term s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons
        (compSubstSubst_subLF sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_termLF sigma_term tau_term theta_term Eq_term s1)
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

Lemma renRen_termLF (xi_term : nat -> nat) (zeta_term : nat -> nat)
  (s : termLF) :
  ren_termLF zeta_term (ren_termLF xi_term s) =
  ren_termLF (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_termLF xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_termLF_pointwise (xi_term : nat -> nat)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_termLF zeta_term) (ren_termLF xi_term))
    (ren_termLF (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_termLF xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen_subLF (xi_term : nat -> nat) (zeta_term : nat -> nat)
  (s : subLF) :
  ren_subLF zeta_term (ren_subLF xi_term s) =
  ren_subLF (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_subLF xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_subLF_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_subLF zeta_term) (ren_subLF xi_term))
    (ren_subLF (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_subLF xi_term zeta_term _ (fun n => eq_refl) s).
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

Lemma renSubst_termLF (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : termLF) :
  subst_termLF tau_term (ren_termLF xi_term s) =
  subst_termLF (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_termLF xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_termLF_pointwise (xi_term : nat -> nat)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_termLF tau_term) (ren_termLF xi_term))
    (subst_termLF (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_termLF xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_subLF (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : subLF) :
  subst_subLF tau_term (ren_subLF xi_term s) =
  subst_subLF (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_subLF xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_subLF_pointwise (xi_term : nat -> nat)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_subLF tau_term) (ren_subLF xi_term))
    (subst_subLF (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_subLF xi_term tau_term _ (fun n => eq_refl) s).
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

Lemma substRen_termLF (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : termLF) :
  ren_termLF zeta_term (subst_termLF sigma_term s) =
  subst_termLF (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_termLF sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_termLF_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_termLF zeta_term) (subst_termLF sigma_term))
    (subst_termLF (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstRen_termLF sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_subLF (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : subLF) :
  ren_subLF zeta_term (subst_subLF sigma_term s) =
  subst_subLF (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_subLF sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_subLF_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_subLF zeta_term) (subst_subLF sigma_term))
    (subst_subLF (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstRen_subLF sigma_term zeta_term _ (fun n => eq_refl) s).
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

Lemma substSubst_termLF (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : termLF) :
  subst_termLF tau_term (subst_termLF sigma_term s) =
  subst_termLF (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_termLF sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_termLF_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_termLF tau_term) (subst_termLF sigma_term))
    (subst_termLF (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_termLF sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_subLF (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : subLF) :
  subst_subLF tau_term (subst_subLF sigma_term s) =
  subst_subLF (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_subLF sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_subLF_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_subLF tau_term) (subst_subLF sigma_term))
    (subst_subLF (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_subLF sigma_term tau_term _ (fun n => eq_refl) s).
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
  | tSig s0 s1 =>
      congr_tSig (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | tPair s0 s1 s2 s3 =>
      congr_tPair (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
  | tFst s0 => congr_tFst (rinst_inst_term xi_term sigma_term Eq_term s0)
  | tSnd s0 => congr_tSnd (rinst_inst_term xi_term sigma_term Eq_term s0)
  | tId s0 s1 s2 =>
      congr_tId (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  | tRefl s0 s1 =>
      congr_tRefl (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      congr_tIdElim (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s2) (rinst_inst_term xi_term sigma_term Eq_term s3)
        (rinst_inst_term xi_term sigma_term Eq_term s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
  | tCtx => congr_tCtx
  | tBox s0 s1 => congr_tBox (eq_refl s0) (eq_refl s1)
  | tQuote s0 s1 =>
      congr_tQuote (eq_refl s0)
        (rinst_inst_termLF xi_term sigma_term Eq_term s1)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      congr_tBoxRec
        (rinst_inst_term (upRen_term_term (upRen_term_term xi_term))
           (up_term_term (up_term_term sigma_term))
           (rinstInst_up_term_term _ _ (rinstInst_up_term_term _ _ Eq_term))
           s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3) (eq_refl s4)
        (rinst_inst_term xi_term sigma_term Eq_term s5)
  end
with rinst_inst_termLF (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (tRel) xi_term x = sigma_term x) (s : termLF)
{struct s} : ren_termLF xi_term s = subst_termLF sigma_term s :=
  match s with
  | lfLam s0 s1 =>
      congr_lfLam (eq_refl s0)
        (rinst_inst_termLF xi_term sigma_term Eq_term s1)
  | lfApp s0 s1 =>
      congr_lfApp (rinst_inst_termLF xi_term sigma_term Eq_term s0)
        (rinst_inst_termLF xi_term sigma_term Eq_term s1)
  | lfSplice s0 s1 =>
      congr_lfSplice (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_subLF xi_term sigma_term Eq_term s1)
  end
with rinst_inst_subLF (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (tRel) xi_term x = sigma_term x) (s : subLF)
{struct s} : ren_subLF xi_term s = subst_subLF sigma_term s :=
  match s with
  | lfSubEmpty => congr_lfSubEmpty
  | lfWk s0 => congr_lfWk (eq_refl s0)
  | lfSubCons s0 s1 =>
      congr_lfSubCons (rinst_inst_subLF xi_term sigma_term Eq_term s0)
        (rinst_inst_termLF xi_term sigma_term Eq_term s1)
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

Lemma rinstInst'_termLF (xi_term : nat -> nat) (s : termLF) :
  ren_termLF xi_term s = subst_termLF (funcomp (tRel) xi_term) s.
Proof.
exact (rinst_inst_termLF xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_termLF_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_termLF xi_term)
    (subst_termLF (funcomp (tRel) xi_term)).
Proof.
exact (fun s => rinst_inst_termLF xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_subLF (xi_term : nat -> nat) (s : subLF) :
  ren_subLF xi_term s = subst_subLF (funcomp (tRel) xi_term) s.
Proof.
exact (rinst_inst_subLF xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_subLF_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_subLF xi_term)
    (subst_subLF (funcomp (tRel) xi_term)).
Proof.
exact (fun s => rinst_inst_subLF xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (tRel) s = s.
Proof.
exact (idSubst_term (tRel) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise : pointwise_relation _ eq (subst_term (tRel)) id.
Proof.
exact (fun s => idSubst_term (tRel) (fun n => eq_refl) s).
Qed.

Lemma instId'_termLF (s : termLF) : subst_termLF (tRel) s = s.
Proof.
exact (idSubst_termLF (tRel) (fun n => eq_refl) s).
Qed.

Lemma instId'_termLF_pointwise :
  pointwise_relation _ eq (subst_termLF (tRel)) id.
Proof.
exact (fun s => idSubst_termLF (tRel) (fun n => eq_refl) s).
Qed.

Lemma instId'_subLF (s : subLF) : subst_subLF (tRel) s = s.
Proof.
exact (idSubst_subLF (tRel) (fun n => eq_refl) s).
Qed.

Lemma instId'_subLF_pointwise :
  pointwise_relation _ eq (subst_subLF (tRel)) id.
Proof.
exact (fun s => idSubst_subLF (tRel) (fun n => eq_refl) s).
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

Lemma rinstId'_termLF (s : termLF) : ren_termLF id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_termLF s) (rinstInst'_termLF id s)).
Qed.

Lemma rinstId'_termLF_pointwise : pointwise_relation _ eq (@ren_termLF id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_termLF s) (rinstInst'_termLF id s)).
Qed.

Lemma rinstId'_subLF (s : subLF) : ren_subLF id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_subLF s) (rinstInst'_subLF id s)).
Qed.

Lemma rinstId'_subLF_pointwise : pointwise_relation _ eq (@ren_subLF id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_subLF s) (rinstInst'_subLF id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (tRel x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (tRel)) sigma_term.
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

Class Up_subLF X Y :=
    up_subLF : X -> Y.

Class Up_termLF X Y :=
    up_termLF : X -> Y.

Class Up_term X Y :=
    up_term : X -> Y.

#[global]
Instance Subst_subLF : (Subst1 _ _ _) := @subst_subLF.

#[global]
Instance Subst_termLF : (Subst1 _ _ _) := @subst_termLF.

#[global]
Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global]
Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global]
Instance Ren_subLF : (Ren1 _ _ _) := @ren_subLF.

#[global]
Instance Ren_termLF : (Ren1 _ _ _) := @ren_termLF.

#[global]
Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global]
Instance VarInstance_term : (Var _ _) := @tRel.

Notation "[ sigma_term ]" := (subst_subLF sigma_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_term ]" := (subst_subLF sigma_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__subLF" := up_subLF (only printing) : subst_scope.

Notation "[ sigma_term ]" := (subst_termLF sigma_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_term ]" := (subst_termLF sigma_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__termLF" := up_termLF (only printing) : subst_scope.

Notation "[ sigma_term ]" := (subst_term sigma_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__term" := up_term (only printing) : subst_scope.

Notation "↑__term" := up_term_term (only printing) : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_subLF xi_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_subLF xi_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_termLF xi_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_termLF xi_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_term xi_term)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := tRel ( at level 1, only printing) : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
  ( at level 5, format "x __term", only printing) : subst_scope.

Notation "x '__term'" := (tRel x) ( at level 5, format "x __term") :
  subst_scope.

#[global]
Instance subst_subLF_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_subLF)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_subLF f_term s = subst_subLF g_term t')
         (ext_subLF f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_subLF_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_subLF)).
Proof.
exact (fun f_term g_term Eq_term s => ext_subLF f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_termLF_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_termLF)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_termLF f_term s = subst_termLF g_term t')
         (ext_termLF f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_termLF_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_termLF)).
Proof.
exact (fun f_term g_term Eq_term s => ext_termLF f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_term_morphism :
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

#[global]
Instance ren_subLF_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_subLF)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_subLF f_term s = ren_subLF g_term t')
         (extRen_subLF f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_subLF_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_subLF)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_subLF f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_termLF_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_termLF)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_termLF f_term s = ren_termLF g_term t')
         (extRen_termLF f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_termLF_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_termLF)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_termLF f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
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
                      Ren_termLF, Ren1, ren1, Ren_subLF, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1, Subst_termLF, Subst1, subst1, Subst_subLF,
                      Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1, Ren_termLF,
                                            Ren1, ren1, Ren_subLF, Ren1,
                                            ren1, Up_term_term, Up_term,
                                            up_term, Subst_term, Subst1,
                                            subst1, Subst_termLF, Subst1,
                                            subst1, Subst_subLF, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_subLF_pointwise
                 | progress setoid_rewrite substSubst_subLF
                 | progress setoid_rewrite substSubst_termLF_pointwise
                 | progress setoid_rewrite substSubst_termLF
                 | progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_subLF_pointwise
                 | progress setoid_rewrite substRen_subLF
                 | progress setoid_rewrite substRen_termLF_pointwise
                 | progress setoid_rewrite substRen_termLF
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_subLF_pointwise
                 | progress setoid_rewrite renSubst_subLF
                 | progress setoid_rewrite renSubst_termLF_pointwise
                 | progress setoid_rewrite renSubst_termLF
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_subLF_pointwise
                 | progress setoid_rewrite renRen_subLF
                 | progress setoid_rewrite renRen'_termLF_pointwise
                 | progress setoid_rewrite renRen_termLF
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_subLF_pointwise
                 | progress setoid_rewrite rinstId'_subLF
                 | progress setoid_rewrite rinstId'_termLF_pointwise
                 | progress setoid_rewrite rinstId'_termLF
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_subLF_pointwise
                 | progress setoid_rewrite instId'_subLF
                 | progress setoid_rewrite instId'_termLF_pointwise
                 | progress setoid_rewrite instId'_termLF
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress unfold up_term_term, upRen_term_term, up_ren
                 | progress
                    cbn[subst_subLF subst_termLF subst_term ren_subLF
                       ren_termLF ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Ren_termLF, Ren1, ren1, Ren_subLF, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  Subst_termLF, Subst1, subst1, Subst_subLF, Subst1, subst1
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_subLF_pointwise;
                  try setoid_rewrite rinstInst'_subLF;
                  try setoid_rewrite rinstInst'_termLF_pointwise;
                  try setoid_rewrite rinstInst'_termLF;
                  try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_subLF_pointwise;
                  try setoid_rewrite_left rinstInst'_subLF;
                  try setoid_rewrite_left rinstInst'_termLF_pointwise;
                  try setoid_rewrite_left rinstInst'_termLF;
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
  | tSig s0 s1 =>
      and (allfv_term p_term s0)
        (and (allfv_term (upAllfv_term_term p_term) s1) True)
  | tPair s0 s1 s2 s3 =>
      and (allfv_term p_term s0)
        (and (allfv_term (upAllfv_term_term p_term) s1)
           (and (allfv_term p_term s2) (and (allfv_term p_term s3) True)))
  | tFst s0 => and (allfv_term p_term s0) True
  | tSnd s0 => and (allfv_term p_term s0) True
  | tId s0 s1 s2 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1) (and (allfv_term p_term s2) True))
  | tRefl s0 s1 =>
      and (allfv_term p_term s0) (and (allfv_term p_term s1) True)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      and (allfv_term p_term s0)
        (and (allfv_term p_term s1)
           (and
              (allfv_term (upAllfv_term_term (upAllfv_term_term p_term)) s2)
              (and (allfv_term p_term s3)
                 (and (allfv_term p_term s4)
                    (and (allfv_term p_term s5) True)))))
  | tCtx => True
  | tBox s0 s1 => and True (and True True)
  | tQuote s0 s1 => and True (and (allfv_termLF p_term s1) True)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      and (allfv_term (upAllfv_term_term (upAllfv_term_term p_term)) s0)
        (and (allfv_term p_term s1)
           (and (allfv_term p_term s2)
              (and (allfv_term p_term s3)
                 (and True (and (allfv_term p_term s5) True)))))
  end
with allfv_termLF (p_term : nat -> Prop) (s : termLF) {struct s} : Prop :=
  match s with
  | lfLam s0 s1 => and True (and (allfv_termLF p_term s1) True)
  | lfApp s0 s1 =>
      and (allfv_termLF p_term s0) (and (allfv_termLF p_term s1) True)
  | lfSplice s0 s1 =>
      and (allfv_term p_term s0) (and (allfv_subLF p_term s1) True)
  end
with allfv_subLF (p_term : nat -> Prop) (s : subLF) {struct s} : Prop :=
  match s with
  | lfSubEmpty => True
  | lfWk s0 => and True True
  | lfSubCons s0 s1 =>
      and (allfv_subLF p_term s0) (and (allfv_termLF p_term s1) True)
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
  | tSig s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj
           (allfvTriv_term (upAllfv_term_term p_term)
              (upAllfvTriv_term_term H_term) s1) I)
  | tPair s0 s1 s2 s3 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj
           (allfvTriv_term (upAllfv_term_term p_term)
              (upAllfvTriv_term_term H_term) s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3) I)))
  | tFst s0 => conj (allfvTriv_term p_term H_term s0) I
  | tSnd s0 => conj (allfvTriv_term p_term H_term s0) I
  | tId s0 s1 s2 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2) I))
  | tRefl s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1) I)
  | tIdElim s0 s1 s2 s3 s4 s5 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj
              (allfvTriv_term (upAllfv_term_term (upAllfv_term_term p_term))
                 (upAllfvTriv_term_term (upAllfvTriv_term_term H_term)) s2)
              (conj (allfvTriv_term p_term H_term s3)
                 (conj (allfvTriv_term p_term H_term s4)
                    (conj (allfvTriv_term p_term H_term s5) I)))))
  | tCtx => I
  | tBox s0 s1 => conj I (conj I I)
  | tQuote s0 s1 => conj I (conj (allfvTriv_termLF p_term H_term s1) I)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      conj
        (allfvTriv_term (upAllfv_term_term (upAllfv_term_term p_term))
           (upAllfvTriv_term_term (upAllfvTriv_term_term H_term)) s0)
        (conj (allfvTriv_term p_term H_term s1)
           (conj (allfvTriv_term p_term H_term s2)
              (conj (allfvTriv_term p_term H_term s3)
                 (conj I (conj (allfvTriv_term p_term H_term s5) I)))))
  end
with allfvTriv_termLF (p_term : nat -> Prop) (H_term : forall x, p_term x)
(s : termLF) {struct s} : allfv_termLF p_term s :=
  match s with
  | lfLam s0 s1 => conj I (conj (allfvTriv_termLF p_term H_term s1) I)
  | lfApp s0 s1 =>
      conj (allfvTriv_termLF p_term H_term s0)
        (conj (allfvTriv_termLF p_term H_term s1) I)
  | lfSplice s0 s1 =>
      conj (allfvTriv_term p_term H_term s0)
        (conj (allfvTriv_subLF p_term H_term s1) I)
  end
with allfvTriv_subLF (p_term : nat -> Prop) (H_term : forall x, p_term x)
(s : subLF) {struct s} : allfv_subLF p_term s :=
  match s with
  | lfSubEmpty => I
  | lfWk s0 => conj I I
  | lfSubCons s0 s1 =>
      conj (allfvTriv_subLF p_term H_term s0)
        (conj (allfvTriv_termLF p_term H_term s1) I)
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
  | tSig s0 s1 =>
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
  | tPair s0 s1 s2 s3 =>
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
  | tFst s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | tSnd s0 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end) I
  | tId s0 s1 s2 =>
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
                 end) I))
  | tRefl s0 s1 =>
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
  | tIdElim s0 s1 s2 s3 s4 s5 =>
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
              end)
           (conj
              (allfvImpl_term (upAllfv_term_term (upAllfv_term_term p_term))
                 (upAllfv_term_term (upAllfv_term_term q_term))
                 (upAllfvImpl_term_term (upAllfvImpl_term_term H_term)) s2
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
                    end)
                 (conj
                    (allfvImpl_term p_term q_term H_term s4
                       match HP with
                       | conj _ HP =>
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
                           end
                       end)
                    (conj
                       (allfvImpl_term p_term q_term H_term s5
                          match HP with
                          | conj _ HP =>
                              match HP with
                              | conj _ HP =>
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
                                  end
                              end
                          end) I)))))
  | tCtx => fun HP => I
  | tBox s0 s1 => fun HP => conj I (conj I I)
  | tQuote s0 s1 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_termLF p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      fun HP =>
      conj
        (allfvImpl_term (upAllfv_term_term (upAllfv_term_term p_term))
           (upAllfv_term_term (upAllfv_term_term q_term))
           (upAllfvImpl_term_term (upAllfvImpl_term_term H_term)) s0
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
                    end)
                 (conj I
                    (conj
                       (allfvImpl_term p_term q_term H_term s5
                          match HP with
                          | conj _ HP =>
                              match HP with
                              | conj _ HP =>
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
                                  end
                              end
                          end) I)))))
  end
with allfvImpl_termLF (p_term : nat -> Prop) (q_term : nat -> Prop)
(H_term : forall x, p_term x -> q_term x) (s : termLF) {struct s} :
allfv_termLF p_term s -> allfv_termLF q_term s :=
  match s with
  | lfLam s0 s1 =>
      fun HP =>
      conj I
        (conj
           (allfvImpl_termLF p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | lfApp s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_termLF p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_termLF p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  | lfSplice s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_term p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_subLF p_term q_term H_term s1
              match HP with
              | conj _ HP => match HP with
                             | conj HP _ => HP
                             end
              end) I)
  end
with allfvImpl_subLF (p_term : nat -> Prop) (q_term : nat -> Prop)
(H_term : forall x, p_term x -> q_term x) (s : subLF) {struct s} :
allfv_subLF p_term s -> allfv_subLF q_term s :=
  match s with
  | lfSubEmpty => fun HP => I
  | lfWk s0 => fun HP => conj I I
  | lfSubCons s0 s1 =>
      fun HP =>
      conj
        (allfvImpl_subLF p_term q_term H_term s0
           match HP with
           | conj HP _ => HP
           end)
        (conj
           (allfvImpl_termLF p_term q_term H_term s1
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

Lemma upAllfvRenL_term_term2 (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
      upAllfv_term_term (upAllfv_term_term p) (upRen_term_term (upRen_term_term xi) x) ->
      upAllfv_term_term (upAllfv_term_term (funcomp p xi)) x.
Proof.
   intros x.
   refine (match x with S n' => fun H => upAllfvRenL_term_term p xi _ H | 0 => fun i => i end).
Qed.


Fixpoint allfvRenL_term (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : term) {struct s} :
allfv_term p_term (ren_term xi_term s) ->
allfv_term (funcomp p_term xi_term) s :=
  match s as s return 
      allfv_term p_term (ren_term xi_term s) ->
      allfv_term (funcomp p_term xi_term) s  with
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
  | tSig s0 s1 =>
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
  | tPair s0 s1 s2 s3 =>
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
                 end))
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
  | tFst s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tSnd s0 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tId s0 s1 s2 =>
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
                 end) I))
  | tRefl s0 s1 =>
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
  | tIdElim s0 s1 s2 s3 s4 s5 =>
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
              end)
           (conj
              (allfvImpl_term _ _ (upAllfvRenL_term_term2 p_term xi_term) s2
                 (allfvRenL_term
                    (upAllfv_term_term (upAllfv_term_term p_term))
                    (upRen_term_term (upRen_term_term xi_term)) s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end))
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
                    end)
                 (conj
                    (allfvRenL_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenL_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  | tCtx => fun H => I
  | tBox s0 s1 => fun H => conj I (conj I I)
  | tQuote s0 s1 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj
        (allfvImpl_term _ _ (upAllfvRenL_term_term2 p_term xi_term) s0
           (allfvRenL_term (upAllfv_term_term (upAllfv_term_term p_term))
              (upRen_term_term (upRen_term_term xi_term)) s0
              match H with
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
                    end)
                 (conj I
                    (conj
                       (allfvRenL_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  end
with allfvRenL_termLF (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : termLF) {struct s} :
allfv_termLF p_term (ren_termLF xi_term s) ->
allfv_termLF (funcomp p_term xi_term) s :=
  match s with
  | lfLam s0 s1 =>
      fun H =>
      conj I
        (conj
           (allfvRenL_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | lfApp s0 s1 =>
      fun H =>
      conj
        (allfvRenL_termLF p_term xi_term s0 match H with
                                            | conj H _ => H
                                            end)
        (conj
           (allfvRenL_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | lfSplice s0 s1 =>
      fun H =>
      conj
        (allfvRenL_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenL_subLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  end
with allfvRenL_subLF (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : subLF) {struct s} :
allfv_subLF p_term (ren_subLF xi_term s) ->
allfv_subLF (funcomp p_term xi_term) s :=
  match s with
  | lfSubEmpty => fun H => I
  | lfWk s0 => fun H => conj I I
  | lfSubCons s0 s1 =>
      fun H =>
      conj
        (allfvRenL_subLF p_term xi_term s0 match H with
                                           | conj H _ => H
                                           end)
        (conj
           (allfvRenL_termLF p_term xi_term s1
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

Lemma upAllfvRenR_term_term2 (p : nat -> Prop) (xi : nat -> nat) :
  forall x,
   upAllfv_term_term (upAllfv_term_term (funcomp p xi)) x ->
   upAllfv_term_term (upAllfv_term_term p) (upRen_term_term (upRen_term_term xi) x).
Proof.
exact (fun x => match x with
                | S n' => fun H => upAllfvRenR_term_term p xi _ H
                | O => fun i => i
                end).
Qed.


Fixpoint allfvRenR_term (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : term) {struct s} :
allfv_term (funcomp p_term xi_term) s ->
allfv_term p_term (ren_term xi_term s) :=
  match s 
   return 
allfv_term (funcomp p_term xi_term) s ->
allfv_term p_term (ren_term xi_term s)
  with
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
  | tSig s0 s1 =>
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
  | tPair s0 s1 s2 s3 =>
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
                 end))
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
  | tFst s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tSnd s0 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end) I
  | tId s0 s1 s2 =>
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
                 end) I))
  | tRefl s0 s1 =>
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
  | tIdElim s0 s1 s2 s3 s4 s5 =>
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
              end)
           (conj
              (allfvRenR_term (upAllfv_term_term (upAllfv_term_term p_term))
                 (upRen_term_term (upRen_term_term xi_term)) s2
                 (allfvImpl_term _ _ (upAllfvRenR_term_term2 p_term xi_term)
                    s2
                    match H with
                    | conj _ H =>
                        match H with
                        | conj _ H => match H with
                                      | conj H _ => H
                                      end
                        end
                    end))
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
                    end)
                 (conj
                    (allfvRenR_term p_term xi_term s4
                       match H with
                       | conj _ H =>
                           match H with
                           | conj _ H =>
                               match H with
                               | conj _ H =>
                                   match H with
                                   | conj _ H =>
                                       match H with
                                       | conj H _ => H
                                       end
                                   end
                               end
                           end
                       end)
                    (conj
                       (allfvRenR_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  | tCtx => fun H => I
  | tBox s0 s1 => fun H => conj I (conj I I)
  | tQuote s0 s1 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | tBoxRec s0 s1 s2 s3 s4 s5 =>
      fun H =>
      conj
        (allfvRenR_term (upAllfv_term_term (upAllfv_term_term p_term))
           (upRen_term_term (upRen_term_term xi_term)) s0
           (allfvImpl_term _ _ (upAllfvRenR_term_term2 p_term xi_term) s0
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
                    end)
                 (conj I
                    (conj
                       (allfvRenR_term p_term xi_term s5
                          match H with
                          | conj _ H =>
                              match H with
                              | conj _ H =>
                                  match H with
                                  | conj _ H =>
                                      match H with
                                      | conj _ H =>
                                          match H with
                                          | conj _ H =>
                                              match H with
                                              | conj H _ => H
                                              end
                                          end
                                      end
                                  end
                              end
                          end) I)))))
  end
with allfvRenR_termLF (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : termLF) {struct s} :
allfv_termLF (funcomp p_term xi_term) s ->
allfv_termLF p_term (ren_termLF xi_term s) :=
  match s with
  | lfLam s0 s1 =>
      fun H =>
      conj I
        (conj
           (allfvRenR_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | lfApp s0 s1 =>
      fun H =>
      conj
        (allfvRenR_termLF p_term xi_term s0 match H with
                                            | conj H _ => H
                                            end)
        (conj
           (allfvRenR_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  | lfSplice s0 s1 =>
      fun H =>
      conj
        (allfvRenR_term p_term xi_term s0 match H with
                                          | conj H _ => H
                                          end)
        (conj
           (allfvRenR_subLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  end
with allfvRenR_subLF (p_term : nat -> Prop) (xi_term : nat -> nat)
(s : subLF) {struct s} :
allfv_subLF (funcomp p_term xi_term) s ->
allfv_subLF p_term (ren_subLF xi_term s) :=
  match s with
  | lfSubEmpty => fun H => I
  | lfWk s0 => fun H => conj I I
  | lfSubCons s0 s1 =>
      fun H =>
      conj
        (allfvRenR_subLF p_term xi_term s0 match H with
                                           | conj H _ => H
                                           end)
        (conj
           (allfvRenR_termLF p_term xi_term s1
              match H with
              | conj _ H => match H with
                            | conj H _ => H
                            end
              end) I)
  end.

End Allfv.

Module Extra.

Import Core.

#[export]Hint Opaque subst_subLF: rewrite.

#[export]Hint Opaque subst_termLF: rewrite.

#[export]Hint Opaque subst_term: rewrite.

#[export]Hint Opaque ren_subLF: rewrite.

#[export]Hint Opaque ren_termLF: rewrite.

#[export]Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Allfv.

Export Extra.

End interface.

Export interface.

