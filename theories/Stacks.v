(** * LogRel.Stacks: definition of stacks, representing evaluation contexts. *)
From Coq Require Import List.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst NormalForms.

Lemma rev_rec :
forall [A : Type] (P : list A -> Type),
P nil ->
(forall (x : A) (l : list A), P l -> P (l ++ x :: nil)) ->
forall l : list A, P l.
Proof.
  intros.
  rewrite <- rev_involutive.
  induction (rev l) ; eauto.
Qed.

Variant ty_entry : term -> Type :=
  | eSort s : ty_entry (tSort s)
  | eProd A B : ty_entry (tProd A B)
  | eNat : ty_entry tNat
  | eEmpty : ty_entry tEmpty
  | eSig A B : ty_entry (tSig A B).

Variant nat_entry : term -> Type :=
  | eZero : nat_entry tZero
  | eSucc t : nat_entry (tSucc t).

Variant dest_entry : Type :=
  | eEmptyElim (P : term)
  | eNatElim (P : term) (hs hz : term)
  | eApp (u : term)
  | eFst
  | eSnd.

Definition zip1 (t : term) (e : dest_entry) : term :=
  match e with
    | eEmptyElim P => (tEmptyElim P t)
    | eNatElim P hs hz => (tNatElim P hs hz t) 
    | eApp u => (tApp t u)
    | eFst => tFst t
    | eSnd => tSnd t
  end.

Definition stack := list dest_entry.

Fixpoint zip t (π : stack) :=
  match π with
  | nil => t
  | cons s π => zip (zip1 t s) π
  end.

Section NfEntries.

Lemma zip_app t (π π' : stack) :
  zip t (π ++ π')%list = zip (zip t π) π'.
Proof.
  induction π in t |- * ; cbn.
  - reflexivity.
  - apply IHπ.
Qed.

Lemma zip_whne n π :
  whne n -> whne (zip n π).
Proof.
  intros Hne.
  induction π as [|[]] in n, Hne |- * ; cbn.
  1: eassumption.
  all: eapply IHπ ; now econstructor.
Qed.

Lemma stack_whne t :
  whne t <~> ∑ (s : stack) (n : nat), t = zip (tRel n) s.
Proof.
  split.
  - induction 1.
    1:
    { exists nil.
      eexists.
      reflexivity.
    }
    all: destruct IHwhne as (?&?&?) ; subst.
    1: eexists (_ ++ (eApp _ :: nil))%list.
    2: eexists (_ ++ (eNatElim _ _ _ :: nil))%list.
    3: eexists (_ ++ (eEmptyElim _ :: nil))%list.
    4: eexists (_ ++ (eFst :: nil))%list.
    5: eexists (_ ++ (eSnd :: nil))%list.
    all: eexists.
    all: rewrite zip_app ; cbn.
    all: reflexivity.
  - intros (π&n&->).
    apply zip_whne.
    now constructor.
Qed.

Lemma isType_entry t :
  ty_entry t <~> (isType t × isCanonical t).
Proof.
  split.
  - intros [].
    all: split ; now constructor.
  - intros [[] i] ; cycle -1.
    1: now edestruct can_whne.
    all: now constructor.
Qed.

Lemma isNat_entry t :
  nat_entry t <~> (isNat t × isCanonical t).
Proof.
  split.
  - intros [].
    all: split ; now constructor.
  - intros [[] i] ; cycle -1.
    1: now edestruct can_whne.
    all: now constructor.
Qed.

End NfEntries.