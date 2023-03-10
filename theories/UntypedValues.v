From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped UntypedReduction.

Inductive snf (r : term) : Type :=
  | snf_tSort {s} : [ r ⇒* tSort s ] -> snf r
  | snf_tProd {na A B} : [ r ⇒* tProd na A B ] -> snf A -> snf B -> snf r
  | snf_tLambda {na A t} : [ r ⇒* tLambda na A t ] -> snf A -> snf t -> snf r
  | snf_sne {n} : [ r ⇒* n ] -> sne n -> snf r
with sne (r : term) : Type :=
  | sne_tRel {v} : r = tRel v -> sne r
  | sne_tApp {n t} : r = tApp n t -> sne n -> snf t -> sne r.

Lemma sne_whne : forall (t : term), sne t -> whne t.
Proof.
intros t Ht; induction Ht; subst; constructor; assumption.
Qed.

Lemma snf_red : forall t u, [ t ⇒* u ] -> snf u -> snf t.
Proof.
intros t u Hr Hu; destruct Hu.
+ eapply snf_tSort.
  transitivity u; eassumption.
+ eapply snf_tProd.
  - transitivity u; eassumption.
  - assumption.
  - assumption.
+ eapply snf_tLambda.
  - transitivity u; eassumption.
  - assumption.
  - assumption.
+ eapply snf_sne.
  - transitivity u; eassumption.
  - eassumption.
Qed.

Inductive isSNType : term -> Type :=
  | UnivType {s} : isSNType (tSort s)
  | ProdType {na A B} : snf A -> snf B -> isSNType (tProd na A B)
  | NeType {A}  : sne A -> isSNType A.

Inductive isSNFun : term -> Type :=
  | LamFun {na A t} : snf A -> snf t -> isSNFun (tLambda na A t)
  | NeFun  {f} : sne f -> isSNFun f.

Lemma isSNType_snf t : isSNType t -> snf t.
Proof.
destruct 1.
+ eapply snf_tSort; reflexivity.
+ eapply snf_tProd; first[reflexivity|assumption].
+ eapply snf_sne; first[reflexivity|assumption].
Qed.

Lemma isSNType_whnf t : isSNType t -> whnf t.
Proof.
destruct 1; constructor.
apply sne_whne; assumption.
Qed.

Lemma isSNFun_snf t : isSNFun t -> snf t.
Proof.
destruct 1.
+ eapply snf_tLambda; first[reflexivity|assumption].
+ eapply snf_sne; first[reflexivity|assumption].
Qed.

Lemma isSNFun_whnf t : isSNFun t -> whnf t.
Proof.
destruct 1; constructor.
apply sne_whne; assumption.
Qed.

Lemma isSNType_isType t : isSNType t -> isType t.
Proof.
destruct 1; constructor; now apply sne_whne.
Qed.

Lemma isSNFun_isFun t : isSNFun t -> isFun t.
Proof.
destruct 1; constructor; now apply sne_whne.
Qed.

Section RenSnf.

  Variable (ρ : nat -> nat).

  Lemma sne_ren t : sne t -> sne (t⟨ρ⟩).
  Proof.
  Admitted. (* FIXME *)

  Lemma snf_ren t : snf t -> snf (t⟨ρ⟩).
  Proof.
  Admitted. (* FIXME *)

End RenSnf.

Lemma isSNType_ren ρ t : isSNType t -> isSNType (t⟨ρ⟩).
Proof.
destruct 1; cbn; constructor; first [apply sne_ren|apply snf_ren]; assumption.
Qed.

Lemma isSNFun_ren ρ t : isSNFun t -> isSNFun (t⟨ρ⟩).
Proof.
destruct 1; cbn; constructor; first [apply sne_ren|apply snf_ren]; assumption.
Qed.
