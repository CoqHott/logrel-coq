(** * LogRel.Decidability.Functions: conversion and type-checker implementation. *)
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context DeclarativeTyping.
From PartialFun Require Import Monad PartialFun.

Import MonadNotations.
Set Universe Polymorphism.

(* #[local] Remove Hints MonadOrec : typeclass_instances.
#[local] Hint Resolve MonadOrec | 3 : typeclass_instances.
#[local] Hint Resolve MonadId | 10 : typeclass_instances. *)

Inductive errors : Type :=
  | variable_not_in_context (n : nat) (Γ : context) : errors
  | head_mismatch (T : option term) (t t' : term) : errors
  | variable_mismatch (n n' : nat) : errors
  | destructor_mismatch (t t' : term) : errors
  | conv_error : errors
  | type_error : errors.

#[local]Instance ty_errors : Errors := errors.
#[local]Existing Instance MonadId | 10.

(* #[local] Instance MonadOrecError A B : Monad (fun X => orec A B (result X)) :=
  MonadTransResult.(mon_trans_mon) _ _. *)
Definition MonadError : Monad result :=
  MonadTransResult.(mon_trans_mon) id _.

#[local]Existing Instance MonadError | 1.

Equations ctx_access (Γ : context) (n : nat) : result term :=
  ctx_access ε _ := raise (H := MonadId) (A := term) (variable_not_in_context n ε) ; (** The context does not contain the variable! *)
  ctx_access (_,,d) 0 := ret (Monad := MonadError) (d⟨↑⟩) ;
  ctx_access (Γ,,_) (S n') := d ← (ctx_access Γ n') ;; ret d⟨↑⟩.

Definition eq_sort (s s' : sort) : result unit := success (M := id).

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

Variant tm_view1 : term -> Type :=
  | tm_view1_type {t} : ty_entry t -> tm_view1 t
  | tm_view1_fun A t : tm_view1 (tLambda A t)
  | tm_view1_rel n : tm_view1 (tRel n)
  | tm_view1_nat {t} : nat_entry t -> tm_view1 t
  | tm_view1_sig A B a b : tm_view1 (tPair A B a b)
  | tm_view1_dest t (s : dest_entry) : tm_view1 (zip1 t s).

Definition build_tm_view1 t : tm_view1 t :=
  match t with
  | tRel n => tm_view1_rel n
  | tSort s => tm_view1_type (eSort s)
  | tProd A B => tm_view1_type (eProd A B)
  | tLambda A t => tm_view1_fun A t
  | tApp t u => tm_view1_dest t (eApp u)
  | tNat => tm_view1_type (eNat)
  | tZero => tm_view1_nat (eZero)
  | tSucc t => tm_view1_nat (eSucc t)
  | tNatElim P hs hz t => tm_view1_dest t (eNatElim P hs hz)
  | tEmpty => tm_view1_type (eEmpty)
  | tEmptyElim P t => tm_view1_dest t (eEmptyElim P)
  | tSig A B => tm_view1_type (eSig A B)
  | tPair A B a b => tm_view1_sig A B a b
  | tFst t => tm_view1_dest t eFst
  | tSnd t => tm_view1_dest t eSnd
  end.

Variant ne_view1 : term -> Type :=
  | ne_view1_rel n : ne_view1 (tRel n)
  | ne_view1_dest t s : ne_view1 (zip1 t s).

Variant nf_view1 : term -> Type :=
  | nf_view1_type {t} : ty_entry t -> nf_view1 t
  | nf_view1_fun A t : nf_view1 (tLambda A t)
  | nf_view1_nat {t} : nat_entry t -> nf_view1 t
  | nf_view1_sig A B a b : nf_view1 (tPair A B a b)
  | nf_view1_ne {t} : ne_view1 t -> nf_view1 t.

Definition build_nf_view1 t : nf_view1 t :=
  match t with
  | tRel n => nf_view1_ne (ne_view1_rel n)
  | tSort s => nf_view1_type (eSort s)
  | tProd A B => nf_view1_type (eProd A B)
  | tLambda A t => nf_view1_fun A t
  | tApp t u => nf_view1_ne (ne_view1_dest t (eApp u))
  | tNat => nf_view1_type (eNat)
  | tZero => nf_view1_nat (eZero)
  | tSucc t => nf_view1_nat (eSucc t)
  | tNatElim P hs hz t => nf_view1_ne (ne_view1_dest t (eNatElim P hs hz))
  | tEmpty => nf_view1_type (eEmpty)
  | tEmptyElim P t => nf_view1_ne (ne_view1_dest t (eEmptyElim P))
  | tSig A B => nf_view1_type (eSig A B)
  | tPair A B a b => nf_view1_sig A B a b
  | tFst t => nf_view1_ne (ne_view1_dest t eFst)
  | tSnd t => nf_view1_ne (ne_view1_dest t eSnd)
  end.

Variant ty_view1 : term -> Type :=
  | ty_view1_ty {t} : ty_entry t -> ty_view1 t
  | ty_view1_small {t} : ne_view1 t -> ty_view1 t
  | ty_view1_anomaly {t} : ty_view1 t.

Definition build_ty_view1 t : ty_view1 t :=
  match (build_tm_view1 t) with
  | tm_view1_type e => ty_view1_ty e
  | tm_view1_rel n => ty_view1_small (ne_view1_rel n)
  | tm_view1_dest t s => ty_view1_small (ne_view1_dest t s)
  | tm_view1_fun _ _ | tm_view1_nat _ | tm_view1_sig _ _ _ _ => ty_view1_anomaly
  end.

Definition stack := list dest_entry.

Fixpoint zip t (π : stack) :=
  match π with
  | nil => t
  | cons s π => zip (zip1 t s) π
  end.


Equations wh_red_stack : term × stack ⇀ term :=
  wh_red_stack (t,π) with (build_tm_view1 t) :=
  wh_red_stack (?(tRel n)       ,π)                         (tm_view1_rel n) := ret (zip (tRel n) π) ;
  wh_red_stack (?(zip1 t s)     ,π)                         (tm_view1_dest t s) := id <*> rec (t,cons s π) ;
  wh_red_stack (?(tLambda A t)  ,nil)                       (tm_view1_fun A t) := ret (tLambda A t) ;
  wh_red_stack (?(tLambda A t)  ,cons (eApp u) π)           (tm_view1_fun A t) := id <*> rec (t[u..], π) ;
  wh_red_stack (_               ,cons _ _)                  (tm_view1_fun _ _) := undefined ;
  wh_red_stack (t               ,nil)                       (tm_view1_nat _) := ret t ;
  wh_red_stack (?(tZero)        ,cons (eNatElim _ hz _) π)  (tm_view1_nat eZero) := id <*> rec (hz,π) ;
  wh_red_stack (?(tSucc t)      ,cons (eNatElim P hz hs) π) (tm_view1_nat (eSucc t)) := id <*> rec (hs ,cons (eApp t) (cons (eApp (tNatElim P hz hs t)) π)) ;
  wh_red_stack (t               ,cons _ _)                  (tm_view1_nat _) := undefined ;
  wh_red_stack (?(tPair A B a b),nil)                       (tm_view1_sig A B a b) := ret (tPair A B a b) ;
  wh_red_stack (?(tPair A B a b),cons eFst π)               (tm_view1_sig A B a b) := id <*> rec (a , π) ;
  wh_red_stack (?(tPair A B a b),cons eSnd π)               (tm_view1_sig A B a b) := id <*> rec (b , π) ;
  wh_red_stack (?(tPair A B a b),cons _ π)                  (tm_view1_sig A B a b) := undefined ;
  wh_red_stack (t               ,nil)                       (tm_view1_type _) := ret t ;
  wh_red_stack (t               ,cons s _)                  (tm_view1_type _) := undefined.

Equations wh_red : term ⇀ term :=
  wh_red t := id <*> call wh_red_stack (t,nil).

Definition wh_red_fuel n t := fueled wh_red n t.

  (* Compute (deep_red_fuel 10 (tApp (tLambda U (tRel 0)) U)).
  Compute (deep_red_fuel 1000 (tNatElim
    tNat
    tZero
    (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
    (tSucc (tSucc tZero)))). *)

Inductive nf_ty_view2 : term -> term -> Type :=
  | ty_sorts (s1 s2 : sort) : nf_ty_view2 (tSort s1) (tSort s2)
  | ty_prods (A A' B B' : term) :
      nf_ty_view2 (tProd A B) (tProd A' B')
  | ty_nats : nf_ty_view2 tNat tNat
  | ty_emptys : nf_ty_view2 tEmpty tEmpty
  | ty_sigs (A A' B B' : term) : nf_ty_view2 (tSig A B) (tSig A' B')
  | ty_neutrals (n n' : term) : nf_ty_view2 n n'
  | ty_mismatch (t u : term) : nf_ty_view2 t u
  | ty_anomaly (t u : term) : nf_ty_view2 t u.

Equations build_nf_ty_view2 (A A' : term) : nf_ty_view2 A A' :=
  build_nf_ty_view2 A A' with (build_ty_view1 A), (build_ty_view1 A') := {
    (** Matching types *)
    | ty_view1_ty (eSort s1), ty_view1_ty (eSort s2) :=
        ty_sorts s1 s2 ;
    | ty_view1_ty (eProd A B), ty_view1_ty (eProd A' B') :=
        ty_prods A A' B B' ;
    | ty_view1_ty eNat, ty_view1_ty eNat :=
        ty_nats;
    | ty_view1_ty eEmpty, ty_view1_ty eEmpty :=
        ty_emptys;
    | ty_view1_ty (eSig A B), ty_view1_ty (eSig A' B') :=
        ty_sigs A A' B B'
    | ty_view1_small _, ty_view1_small _ :=
        ty_neutrals _ _ ;
    (** Mismatching sorts *)
    | ty_view1_ty _, ty_view1_ty _ :=
        ty_mismatch _ _ ;
    | ty_view1_small _, ty_view1_ty _ :=
        ty_mismatch _ _ ;
    | ty_view1_ty _, ty_view1_small _ :=
        ty_mismatch _ _ ;
    (** Anomaly *)
    | ty_view1_anomaly,_ := ty_anomaly _ _ ;
    | _, ty_view1_anomaly := ty_anomaly _ _;
  }.

Inductive nf_view3 : term -> term -> term -> Type :=
| types {A A'} (s : sort) : nf_ty_view2 A A' -> nf_view3 (tSort s) A A'
| functions A B t t' : nf_view3 (tProd A B) t t'
| zeros : nf_view3 tNat tZero tZero
| succs t t' : nf_view3 tNat (tSucc t) (tSucc t')
| pairs A B t t' : nf_view3 (tSig A B) t t'
| neutrals (A n n' : term) : nf_view3 A n n'
| mismatch (A t u : term) : nf_view3 A t u
| anomaly (A t u : term) : nf_view3 A t u.

Equations build_nf_view3 T t t' : nf_view3 T t t' :=
  build_nf_view3 T t t' with (build_ty_view1 T) := {
  (** Matching typed *)
  | ty_view1_ty (eSort s) := types s (build_nf_ty_view2 t t') ;
  (** Functions *)
  | ty_view1_ty (eProd A B) := functions A B _ _ ;
  (** Naturals *)
  | ty_view1_ty eNat with (build_nf_view1 t), (build_nf_view1 t') :=
    {
      | nf_view1_nat eZero, nf_view1_nat eZero :=
        zeros ;
      | nf_view1_nat (eSucc u), nf_view1_nat (eSucc u') :=
        succs u u' ;
      | nf_view1_ne _, nf_view1_ne _ := neutrals _ _ _ ;
      | nf_view1_nat _, nf_view1_nat _ :=
          mismatch _ _ _ ;
      | nf_view1_ne _, nf_view1_nat _ :=
          mismatch _ _ _ ;
      | nf_view1_nat _, nf_view1_ne _ :=
          mismatch _ _ _ ;
      | _, _ := anomaly _ _ _ ;
    } ;
  (** Inhabitants of the empty type must be neutrals *)
  | ty_view1_ty eEmpty with (build_nf_view1 t), (build_nf_view1 t') :=
  {
    | nf_view1_ne _, nf_view1_ne _ := 
      neutrals _ _ _ ;
    | _, _ := anomaly _ _ _ ;
  }
  (** Pairs *)
  | ty_view1_ty (eSig A B) := pairs A B _ _ ;
  (** Neutral type *)
  | ty_view1_small _ := neutrals _ _ _ ;
  (** The type is not a type *)
  | ty_view1_anomaly := anomaly _ _ _ ;
  }.

Variant conv_state : Type :=
  | ty_state (** Conversion of arbitrary types *)
  | ty_red_state (** Comparison of types in weak-head normal forms *)
  | tm_state (** Conversion of arbitrary terms *)
  | tm_red_state (** Comparison of terms if weak-head normal forms *)
  | ne_state (** Comparison of neutrals *)
  | ne_red_state. (** Comparison of neutrals with a reduced type *)

Definition cstate_input (c : conv_state) : Type :=
  match c with
  | tm_state | tm_red_state => term
  | ty_state | ty_red_state | ne_state | ne_red_state => unit
  end.

Definition cstate_output (c : conv_state) : Type :=
  match c with
  | ty_state | ty_red_state | tm_state | tm_red_state => unit
  | ne_state | ne_red_state => term
  end.

Equations conv :
  ∇ (x : ∑ (c : conv_state) (_ : context) (_ : cstate_input c) (_ : term), term),
  (result (cstate_output (x.π1))) :=
  conv (ty_state;Γ;_;T;V) :=
    T' ← call wh_red T ;;
    V' ← call wh_red V ;;
    id <*> rec (ty_red_state;Γ;tt;T';V') ;
  conv (ty_red_state;Γ;_;T;T') with (build_nf_ty_view2 T T') :=
  {
    | ty_sorts s s' :=
        ret (eq_sort s s') ;
    | ty_prods A A' B B' :=
      r ← rec (ty_state;Γ;tt;A;A') ;;
      match r with
      | error e => raise e
      | ok _ => id <*> rec (ty_state;(Γ,,A);tt;B;B')
      end ;
    | ty_nats := success ;
    | ty_emptys := success ;
    | ty_sigs A A' B B' :=
      r ← rec (ty_state;Γ;tt;A;A') ;;
      match r with
      | error e => raise e
      | ok _ => id <*> rec (ty_state;(Γ,,A);tt;B;B')
      end ;
    | ty_neutrals _ _ :=
        r ← rec (ne_state;Γ;tt;T;T') ;;
        match r with
        | ok _ => success
        | error e => raise e
        end ;
    | ty_mismatch _ _ := raise (head_mismatch None T T') ;
    | ty_anomaly _ _ := undefined ;
  } ;
  conv (tm_state;Γ;A;t;u) :=
    A' ← call wh_red A ;;
    t' ← call wh_red t ;;
    u' ← call wh_red u ;;
    id <*> rec (tm_red_state;Γ;A';t';u') ;
  conv (tm_red_state;Γ;A;t;u) with (build_nf_view3 A t u) :=
  {
    | types s (ty_sorts s1 s2) := undefined ;
    | types s (ty_prods A A' B B') :=
      r ← rec (tm_state;Γ;tSort s;A;A') ;;
      match r with
      | error e => raise e
      | ok _ => id <*> rec (tm_state;Γ,,A;tSort s;B;B') 
      end ;
    | types _ ty_nats := success ;
    | types _ ty_emptys := success ;
    | types s (ty_sigs A A' B B') :=
      r ← rec (tm_state;Γ;tSort s;A;A') ;;
      match r with
      | error e => raise e
      | ok _ => id <*> rec (tm_state;Γ,,A;tSort s;B;B') 
      end ;
    | types _ (ty_neutrals _ _) := 
        r ← rec (ne_state;Γ;tt;t;u) ;;
          match r with
          | ok _ => success
          | error e => raise e
          end ;
    | types s (ty_mismatch _ _) := raise (head_mismatch (Some (tSort s)) t u) ;
    | types _ (ty_anomaly _ _) := undefined ;
    | functions A B t u :=
        id <*> rec (tm_state;Γ,,A;B;eta_expand t;eta_expand u) ;
    | zeros := success ;
    | succs t' u' :=
        id <*> rec (tm_state;Γ;tNat;t';u') ;
    | pairs A B t u :=
        r ← rec (tm_state;Γ;A;tFst t; tFst u) ;;  
        match r with
        | ok _ => id <*> rec (tm_state;Γ; B[(tFst t)..]; tSnd t; tSnd u)
        | error e => raise e
        end ;
    | neutrals _ _ _ := 
      r ← rec (ne_state;Γ;tt;t;u) ;;
        match r with
        | ok _ => success
        | error e => raise e
        end ;
    | mismatch _ _ _ := raise (head_mismatch (Some A) t u) ;
    | anomaly _ _ _ := undefined ;
  } ;
  conv (ne_state;Γ;_;tRel n;tRel n')
    with n =? n' :=
    { | false := raise (variable_mismatch n n') ;
      | true with (ctx_access Γ n) := 
        {
        | error e => undefined ;
        | ok d => ret (ok d)
        }
    } ;
  conv (ne_state;Γ;_;tApp n t ; tApp n' t') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | error e => raise e
    | (ok (tProd A B)) => r ← rec (tm_state;Γ;A;t;t') ;;
      match r with
      | error e => raise e
      | ok _ => ret (ok B[t..])
      end
    | (ok _) => undefined (** the whnf of the type of an applied neutral must be a Π type!*)
    end ;
  conv (ne_state;Γ;_;tNatElim P hz hs n;tNatElim P' hz' hs' n') :=
    rn ← rec (ne_red_state;Γ;tt;n;n') ;;
    match rn with
    | error e => raise e
    | ok tNat =>
        rP ← rec (ty_state;(Γ,,tNat);tt;P;P') ;;
        match rP with
        | error e => raise e
        | ok _ =>
            rz ← rec (tm_state;Γ;P[tZero..];hz;hz') ;;
            rs ← rec (tm_state;Γ;elimSuccHypTy P;hs;hs') ;;
            match rz, rs with
            | ok _, ok _ => ret (ok P[n..])
            | _, _ => raise conv_error
            end
        end
    | ok _ => undefined
    end ;
  conv (ne_state;Γ;_;tEmptyElim P n;tEmptyElim P' n') :=
    rn ← rec (ne_red_state;Γ;tt;n;n') ;;
    match rn with
    | error e => raise e
    | ok tEmpty =>
        rP ← rec (ty_state;(Γ,,tEmpty);tt;P;P') ;;
        match rP with
        | error e => raise e
        | ok _ => ret (ok P[n..])
        end
    | ok _ => undefined
    end ;
  conv (ne_state; Γ; _ ; tFst n; tFst n') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | error e => raise e
    | (ok (tSig A B)) => ret (ok A)
    | (ok _) => undefined (** the whnf of the type of a projected neutral must be a Σ type!*)
    end ;
  conv (ne_state; Γ; _ ; tSnd n; tSnd n') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | error e => raise e
    | (ok (tSig A B)) => ret (ok (B[(tFst n)..]))
    | (ok _) => undefined (** the whnf of the type of a projected neutral must be a Σ type!*)
    end ;
  conv (ne_state;Γ;_;n;n') := raise (destructor_mismatch n n') ;
  conv (ne_red_state;Γ;_;t;u) :=
    Ainf ← rec (ne_state;Γ;tt;t;u) ;;
    match Ainf with
    | error e => raise e
    | ok Ainf' => A' ← call wh_red Ainf' ;; ret (ok A')
    end.

Variant typing_state : Type :=
  | inf_state (** inference *)
  | check_state (** checking *)
  | inf_red_state (** inference of a type reduced to whnf *)
  | wf_ty_state. (** checking well-formation of a type *)

Definition tstate_input (s : typing_state) : Type :=
  match s with
  | inf_state | inf_red_state | wf_ty_state => unit
  | check_state => term
  end.

Definition tstate_output (s : typing_state) : Type :=
  match s with
  | inf_state | inf_red_state => term
  | wf_ty_state | check_state => unit
  end.

Equations typing : ∇ (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term),
  (result (tstate_output (x.π1))) :=
  typing (wf_ty_state;Γ;_;T) with (build_ty_view1 T) :=
  {
    | ty_view1_ty (eSort s) := success ;
    | ty_view1_ty (eProd A B) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        match rA with
        | error e => raise e
        | ok _ => id <*> rec (wf_ty_state;Γ,,A;tt;B)
        end ;
    | ty_view1_ty (eNat) := success ;
    | ty_view1_ty (eEmpty) := success ;
    | ty_view1_ty (eSig A B) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        match rA with
        | error e => raise e
        | ok _ => id <*> rec (wf_ty_state;Γ,,A;tt;B)
        end ;
    | ty_view1_small _ :=
        r ← rec (inf_red_state;Γ;tt;T) ;;
        match r with
        | ok (tSort _) => success
        | ok _ => raise type_error
        | error e => raise e
        end
    | ty_view1_anomaly := raise type_error ;
  } ;
  typing (inf_state;Γ;_;t) with t :=
  {
    | tRel n with (ctx_access Γ n) :=
        {
          | error _ := raise (variable_not_in_context n Γ) ;
          | ok d := ret (ok d)
        } ;
    | tSort s := raise type_error ;
    | tProd A B :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | ok (tSort sA) =>
            rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
            match rB with
            | ok (tSort sB) => ret (ok (tSort (sort_of_product sA sB)))
            | ok _ => raise type_error
            | error e => raise e
            end
        | ok _ => raise type_error
        | error e => raise e
        end ;
    | tLambda A u :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        match rA with
        | ok _ =>
            ru ← rec (inf_state;Γ,,A;tt;u) ;;
            match ru with
            | ok B => ret (ok (tProd A B))
            | error e => raise e
            end
        | error e => raise e
        end ;
    | tApp f u :=
      rf ← rec (inf_red_state;Γ;tt;f) ;;
      match rf with
      | ok (tProd A B) =>
          ru ← rec (check_state;Γ;A;u) ;;
          match ru with
          | ok _ => (ret (ok B[u..])) 
          | error e => raise e
          end 
      | ok _ => raise type_error
      | error e => raise e 
      end ;
    | tNat := ret (ok U) ;
    | tZero := ret (ok tNat) ;
    | tSucc u :=
        ru ← rec (inf_red_state;Γ;tt;u) ;;
        match ru with
        | ok tNat => ret (ok tNat)
        | ok _ => raise type_error
        | error e => raise e
        end ;
    | tNatElim P hz hs n :=
      rn ← rec (inf_red_state;Γ;tt;n) ;;
      match rn with
      | error e => raise e
      | ok tNat =>
          rP ← rec (wf_ty_state;(Γ,,tNat);tt;P) ;;
          match rP with
          | error e => raise e
          | ok _ =>
              rz ← rec (check_state;Γ;P[tZero..];hz) ;;
              rs ← rec (check_state;Γ;elimSuccHypTy P;hs) ;;
              match rz, rs with
              | ok _, ok _ => ret (ok P[n..])
              | _, _ => raise type_error
              end
          end
      | ok _ => raise type_error
      end ;
      | tEmpty := ret (ok U) ;
      | tEmptyElim P e :=
          re ← rec (inf_red_state;Γ;tt;e) ;;
          match re with
          | error e => raise e
          | ok tEmpty =>
              rP ← rec (wf_ty_state;(Γ,,tEmpty);tt;P) ;;
              match rP with
              | error e => raise e
              | ok _ => ret (ok P[e..])
              end
          | ok _ => raise type_error
          end ;
      | tSig A B :=  
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | ok (tSort sA) =>
            rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
            match rB with
            | ok (tSort sB) => ret (ok (tSort (sort_of_product sA sB))) (* Should that be taken as a parameter for sigma as well ? *)
            | ok _ => raise type_error
            | error e => raise e
            end
        | ok _ => raise type_error
        | error e => raise e
        end ;
      | tPair A B a b :=  
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        match rA with
        | ok _ =>
            rB ← rec (wf_ty_state;Γ,,A;tt;B) ;;
            match rB with
            | ok _ => ra ← rec (check_state;Γ;A; a) ;;
              match ra with
              | ok _ => rb ← rec (check_state;Γ;B[a..]; b) ;;
                match rb with
                | ok _ => ret (ok (tSig A B))
                | error e => raise e
                end 
              | error e => raise e
              end
            | error e => raise e
            end
        | error e => raise e
        end ;
      | tFst u :=
        rt ← rec (inf_red_state; Γ; tt; u) ;;
        match rt with
        | ok (tSig A B) => ret (ok A)
        | ok _ => raise type_error
        | error e => raise e
        end
      | tSnd u :=
        rt ← rec (inf_red_state; Γ; tt; u) ;;
        match rt with
        | ok (tSig A B) => ret (ok (B[(tFst u)..]))
        | ok _ => raise type_error
        | error e => raise e
        end 
  } ;
  typing (inf_red_state;Γ;_;t) :=
    r ← rec (inf_state;Γ;_;t) ;;
    match r with
    | error e => raise e
    | ok T => ok <*> call wh_red T
    end ;
  typing (check_state;Γ;T;t) :=
    r ← rec (inf_state;Γ;tt;t) ;;
    match r with
    | error e => raise e
    | ok T' => (id (X := result unit)) <*> call conv (ty_state;Γ;tt;T';T)
    end.

(* #[local] Definition infer (Γ : context) (t : term) : Fueled (result term) := 
  (fueled typing 1000 (inf_state;Γ;tt;t)).

#[local] Definition check (Γ : context) (T t : term) : Fueled (result unit) := 
  (fueled typing 1000 (check_state;Γ;T;t)).

#[local] Definition check_ty (Γ : context) (t : term) : Fueled (result unit) := 
  (fueled typing 1000 (wf_ty_state;Γ;tt;t)).

Check (eq_refl :
  (infer ε
  (tNatElim
    tNat
    tZero
  (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
  (tSucc (tSucc tZero))))
  = (Success (ok tNat))).

Check (eq_refl : (infer ε (tProd U (tRel 0))) = (Success (error type_error))).
Check (eq_refl : (check_ty ε (tProd U (tRel 0))) = (Success (ok tt))).

Check (eq_refl :
  (infer ε
    (tLambda tNat (tNatElim
      tNat
      tZero
    (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
    (tRel 0))))
  = (Success (ok (tProd tNat tNat)))). *)