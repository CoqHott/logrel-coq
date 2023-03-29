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
  | conv_error
  | type_error.

#[local]Instance ty_errors : Errors := errors.

(* #[local] Instance MonadOrecError A B : Monad (fun X => orec A B (result X)) :=
  MonadTransResult.(mon_trans_mon) _ _.
Definition MonadError : Monad result :=
  MonadTransResult.(mon_trans_mon) id _.

#[local]Existing Instance MonadError | 1. *)

Inductive stack :=
| sEmptyElim (P : term) (π : stack)
| sNatElim (P : term) (hs hz : term) (π : stack)
| sApp (u : term) (π : stack)
| sNil.

Fixpoint zip t π :=
  match π with
  | sEmptyElim P π => zip (tEmptyElim P t) π
  | sNatElim P hs hz π => zip (tNatElim P hs hz t) π 
  | sApp u π => zip (tApp t u) π
  | sNil => t
  end.

Equations wh_red_stack : term × stack ⇀ term :=
  wh_red_stack (tRel n, π) := ret (zip (tRel n) π) ;
  wh_red_stack (tLambda _ t, sApp u π) :=
    id <*> rec (t[u..], π) ;
  wh_red_stack (tApp t u, π) :=
    id <*> rec (t, sApp u π) ;
  wh_red_stack (tZero,sNatElim _ hz _ π) :=
    id <*> rec (hz,π) ;
  wh_red_stack (tSucc t,sNatElim P hz hs π) :=
    id <*> rec (hs,sApp t (sApp (tNatElim P hz hs t) π)) ;
  wh_red_stack (tNatElim P hz hs t, π) :=
    id <*> rec (t,sNatElim P hz hs π) ;
  wh_red_stack (tEmptyElim P t, π) :=
    id <*> rec (t,sEmptyElim P π) ;
  wh_red_stack (t,sNil) := ret t ; (** A normal form in the empty stack has finished computing *)
  wh_red_stack (t, sApp _ _) := undefined ; (** The stack does not correspond to the term! *)
  wh_red_stack (t, sNatElim _ _ _ _) := undefined ; (** The stack does not correspond to the term! *)
  wh_red_stack (t, sEmptyElim _ _ ) := undefined. (** The stack does not correspond to the term! *)

Equations wh_red : term ⇀ term :=
  wh_red t := id <*> call wh_red_stack (t,sNil).

Definition wh_red_fuel n t := fueled wh_red n t.

(* Compute (deep_red_fuel 10 (tApp (tLambda U (tRel 0)) U)).
Compute (deep_red_fuel 1000 (tNatElim
  tNat
  tZero
  (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
  (tSucc (tSucc tZero)))). *)

Equations ctx_access : (context × nat) ⇀ term :=
  ctx_access (ε , _ ) := undefined ; (** The context does not contain the variable! *)
  ctx_access (_,,d , 0 ) := ret (d⟨↑⟩) ;
  ctx_access ( Γ,,_ , S n') := d ← rec (Γ,n') ;; ret d⟨↑⟩.

Definition eq_sort (s s' : sort) : result unit := success (M := id).

Inductive nf_view1 : term -> Type :=
  | nf_view1_type t : nf_view1 t
  | nf_view1_fun t : nf_view1 t
  | nf_view1_nat t : nf_view1 t
  | nf_view1_ne n : nf_view1 n.

Definition build_nf_view1 t : nf_view1 t :=
  match t with
  | tRel _| tApp _ _ | tNatElim _ _ _ _ | tEmptyElim _ _ => nf_view1_ne _
  | tSort _| tProd _ _ | tNat | tEmpty => nf_view1_type _
  | tLambda _ _ => nf_view1_fun _
  | tZero | tSucc _ => nf_view1_nat _
  end.

Inductive nf_ty_view : term -> Type :=
| nf_ty_view_sort s : nf_ty_view (tSort s)
| nf_ty_view_prod A B : nf_ty_view (tProd A B)
| nf_ty_view_nat : nf_ty_view tNat
| nf_ty_view_empty : nf_ty_view tEmpty
| nf_ty_view_ne n : nf_ty_view n
| nf_ty_view_anomaly t : nf_ty_view t.

Definition build_nf_ty_view t : nf_ty_view t :=
  match t with
  | tSort s => nf_ty_view_sort _
  | tProd A B => nf_ty_view_prod _ _
  | tNat => nf_ty_view_nat
  | tEmpty => nf_ty_view_empty
  | tRel _ | tApp _ _ | tNatElim _ _ _ _ | tEmptyElim _ _ => nf_ty_view_ne _
  | tLambda _ _ | tZero | tSucc _ => nf_ty_view_anomaly _
  end.

Inductive nf_view3 : term -> term -> term -> Type :=
| sorts (s s1 s2 : sort) : nf_view3 (tSort s) (tSort s1) (tSort s2)
| prods (s : sort) (A A' B B' : term) :
    nf_view3 (tSort s) (tProd A B) (tProd A' B')
| nats s : nf_view3 (tSort s) tNat tNat
| emptys s : nf_view3 (tSort s) tEmpty tEmpty
| functions A B t t' : nf_view3 (tProd A B) t t'
| zeros : nf_view3 tNat tZero tZero
| succs t t' : nf_view3 tNat (tSucc t) (tSucc t')
| neutrals (A n n' : term) : nf_view3 A n n'
| mismatch (A t u : term) : nf_view3 A t u
| anomaly (A t u : term) : nf_view3 A t u.

Equations nf_case T t t' : nf_view3 T t t' :=
  nf_case T t t' with (build_nf_ty_view T), (build_nf_view1 t), (build_nf_view1 t') := {
  (** Matching typed *)
  | nf_ty_view_sort s, nf_view1_type (tSort s1), nf_view1_type (tSort s2) :=
      sorts s s1 s2 ;
  | nf_ty_view_sort s, nf_view1_type (tProd A B), nf_view1_type (tProd A' B') :=
      prods s A A' B B' ;
  | nf_ty_view_sort _, nf_view1_type tNat, nf_view1_type tNat :=
      nats s;
  | nf_ty_view_sort _, nf_view1_ne _, nf_view1_ne _ :=
      neutrals _ _ _ ;
  (** Mismatching sorts *)
  | nf_ty_view_sort _, nf_view1_type _, nf_view1_type _ :=
      mismatch _ _ _ ;
  | nf_ty_view_sort _, nf_view1_ne _, nf_view1_type _ :=
      mismatch _ _ _ ;
  | nf_ty_view_sort _, nf_view1_type _, nf_view1_ne _ :=
      mismatch _ _ _ ;
  (** Functions *)
  | nf_ty_view_prod A B, _, _ :=
      functions A B _ _ ;
  (** Matching naturals *)
  | nf_ty_view_nat, nf_view1_nat tZero, nf_view1_nat tZero :=
      zeros ;
  | nf_ty_view_nat, nf_view1_nat (tSucc u), nf_view1_nat (tSucc u') :=
      succs u u' ;
  | nf_ty_view_nat, nf_view1_ne _, nf_view1_ne _ :=
      neutrals _ _ _ ;
  (** Mismatching naturals *)
  | nf_ty_view_nat, nf_view1_nat _, nf_view1_nat _ :=
      mismatch _ _ _ ;
  | nf_ty_view_nat, nf_view1_ne _, nf_view1_nat _ :=
      mismatch _ _ _ ;
  | nf_ty_view_nat, nf_view1_nat _, nf_view1_ne _ :=
      mismatch _ _ _ ;
  (** Inhabitants of the empty type must be neutrals *)
  | nf_ty_view_empty, nf_view1_ne _, nf_view1_ne _ :=
      neutrals _ _ _ ;
  (** Elements of a neutral type *)
  | nf_ty_view_ne _, nf_view1_ne _, nf_view1_ne _ :=
      neutrals _ _ _ ;
  (** Unreachable cases *)
  | _, _, _ := anomaly _ _ _
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
  conv (ty_red_state;Γ;_;T;T') with (build_nf_ty_view T), (build_nf_ty_view T') :=
  {
    | nf_ty_view_sort s, nf_ty_view_sort s' :=
        ret (M := orec _ _) (Monad := MonadOrec) (eq_sort s s') ;
    | (nf_ty_view_prod A B), (nf_ty_view_prod A' B') :=
      r ← rec (ty_state;Γ;tt;A;A') ;;
      id <*> rec (ty_state;(Γ,,A);tt;B;B')
    | nf_ty_view_nat, nf_ty_view_nat := success ;
    | nf_ty_view_ne _, nf_ty_view_ne _ :=
        (* (fun _ => tt) <*> rec (ne_state;Γ;tt;T;T') ; *)
        (* This should work, but the system does not find the correct bind *)
        r ← rec (ne_state;Γ;tt;T;T') ;;
        match r with
        | ok _ => success
        | error e => raise e
        end ;
    | nf_ty_view_anomaly _, _ := undefined ;
    | _, nf_ty_view_anomaly _ := undefined ;
    | _, _ := raise conv_error ; (** Heads do not match *)
  } ;
  conv (tm_state;Γ;A;t;u) :=
    A' ← call wh_red A ;;
    t' ← call wh_red t ;;
    u' ← call wh_red u ;;
    id <*> rec (tm_red_state;Γ;A';t';u') ;
  conv (tm_red_state;Γ;A;t;u) with (nf_case A t u) :=
  {
    | sorts s s1 s2 := 
      ret (eq_sort s1 s2) ;
    | prods s A A' B B' :=
      r ← rec (tm_state;Γ;tSort s;A;A') ;;
      id <*> rec (tm_state;Γ,,A;tSort s;B;B') ;
    | nats s := success ;
    | emptys s := success ;
    | functions A B _ _ :=
        id <*> rec (tm_state;Γ,,A;B;eta_expand t;eta_expand u) ;
    | zeros := success ;
    | succs t' u' :=
        id <*> rec (tm_state;Γ;tNat;t';u') ;
    | neutrals _ _ _ := 
      r ← rec (ne_state;Γ;tt;t;u) ;;
        match r with
        | ok _ => success
        | error e => raise e
        end ;
    | mismatch _ _ _ := raise conv_error ;
    | anomaly _ _ _ := undefined ;
  } ;
  conv (ne_state;Γ;_;tRel n;tRel n')
    with n =? n' :=
    { | false => raise conv_error
      | true => d ← call ctx_access (Γ,n) ;; ret (ok d)
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
    rP ← rec (ty_state;(Γ,,tNat);tt;P;P') ;;
    match rP with
    | error e => raise e
    | ok _ =>
        rz ← rec (tm_state;Γ;P[tZero..];hz;hz') ;;
        rs ← rec (tm_state;Γ;elimSuccHypTy P;hs;hs') ;;
        rn ← rec (tm_state;Γ;tNat;n;n') ;;
        match rz, rs, rn with
        | ok _, ok _, ok _ => ret (ok P[n..])
        | _, _, _ => raise conv_error
        end
    end ;
  conv (ne_state;Γ;_;tEmptyElim P n;tEmptyElim P' n') :=
    rP ← rec (ty_state;(Γ,,tEmpty);tt;P;P') ;;
    match rP with
    | error e => raise e
    | ok _ =>
        rn ← rec (tm_state;Γ;tNat;n;n') ;;
        match rn with
        | ok _ => ret (ok P[n..])
        | error e => raise e
        end
    end ;
  conv (ne_state;_) := raise conv_error ;
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
  typing (wf_ty_state;Γ;_;T) with (build_nf_ty_view T) :=
  {
    | nf_ty_view_sort s := success ;
    | nf_ty_view_prod A B :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        id <*> rec (wf_ty_state;Γ,,A;tt;B) ;
    | nf_ty_view_nat := success ;
    | nf_ty_view_empty := success ;
    | nf_ty_view_ne _ :=
        r ← rec (inf_red_state;Γ;tt;T) ;;
        match r with
        | ok (tSort _) => success
        | ok _ => raise type_error
        | error e => raise e
        end
    | nf_ty_view_anomaly _ := raise type_error ;
  } ;
  typing (inf_state;Γ;_;t) with t :=
  {
    | tRel n := ok <*> call ctx_access (Γ,n) ;
    | tSort s := raise type_error ;
    | tProd A B :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | ok (tSort sA) =>
            rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
            match rB with
            | ok _ => raise type_error
            | error e => raise e
            end
        | ok _ => raise type_error
        | error e => raise e
        end ;
    | tLambda A u :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | ok (tSort sA) =>
            ru ← rec (inf_state;Γ,,A;tt;u) ;;
            match ru with
            | ok B => ret (ok (tProd A B))
            | error e => raise e
            end
        | ok _ => raise type_error
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
      rP ← rec (wf_ty_state;(Γ,,tNat);tt;P) ;;
      match rP with
      | error e => raise e
      | ok _ =>
          rz ← rec (check_state;Γ;P[tZero..];hz) ;;
          rs ← rec (check_state;Γ;elimSuccHypTy P;hs) ;;
          rn ← rec (check_state;Γ;tNat;n) ;;
          match rz, rs, rn with
          | ok _, ok _, ok _ => ret (ok P[n..])
          | _, _, _ => raise type_error
          end
      end ;
    | _ := undefined ;
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

#[local] Definition infer (Γ : context) (t : term) : Fueled (result term) := 
  (fueled typing 1000 (inf_state;Γ;tt;t)).

#[local] Definition check_ty (Γ : context) (t : term) : Fueled (result unit) := 
  (fueled typing 1000 (wf_ty_state;Γ;tt;t)).

Compute (infer ε
  (tNatElim
    tNat
    tZero
  (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
  (tSucc (tSucc tZero)))).

Compute (infer ε (tProd U (tRel 0))).
Compute (check_ty ε (tProd U (tRel 0))).

Compute (infer ε
  (tLambda tNat (tNatElim
    tNat
    tZero
  (tLambda tNat (tLambda tNat (tSucc (tSucc (tRel 0)))))
  (tRel 0)))).