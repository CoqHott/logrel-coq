(** * LogRel.Decidability.Functions: conversion and type-checker implementation. *)
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From PartialFun Require Import Monad PartialFun MonadExn.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.

Import MonadNotations.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

#[global]
Obligation Tactic := idtac.


Inductive errors : Type :=
  | variable_not_in_context (n : nat) (Γ : context) : errors
  | head_mismatch (T : option term) (t t' : term) : errors
  | variable_mismatch (n n' : nat) : errors
  | destructor_mismatch (t t' : term) : errors
  | conv_error : errors
  | type_error : errors.

#[export]Existing Instance OrecEffectExn.
#[export]Existing Instance MonadExn | 1.
#[export]Existing Instance MonadRaiseExn.

Equations ctx_access (Γ : context) (n : nat) : exn errors term :=
  ctx_access ε _ := raise (A := term) (variable_not_in_context n ε) ; (** The context does not contain the variable! *)
  ctx_access (_,,d) 0 := ret (d⟨↑⟩) ;
  ctx_access (Γ,,_) (S n') := d ← (ctx_access Γ n') ;; ret d⟨↑⟩.

Definition eq_sort (s s' : sort) : exn errors unit := success tt.

Variant ty_entry : term -> Type :=
  | eSort s : ty_entry (tSort s)
  | eProd A B : ty_entry (tProd A B)
  | eNat : ty_entry tNat
  | eEmpty : ty_entry tEmpty
  | eSig A B : ty_entry (tSig A B)
  | eId A x y : ty_entry (tId A x y).

Variant nat_entry : term -> Type :=
  | eZero : nat_entry tZero
  | eSucc t : nat_entry (tSucc t).

Variant dest_entry : Type :=
  | eEmptyElim (P : term)
  | eNatElim (P : term) (hs hz : term)
  | eApp (u : term)
  | eFst
  | eSnd
  | eIdElim (A x P hr y : term).

Definition zip1 (t : term) (e : dest_entry) : term :=
  match e with
    | eEmptyElim P => (tEmptyElim P t)
    | eNatElim P hs hz => (tNatElim P hs hz t)
    | eApp u => (tApp t u)
    | eFst => tFst t
    | eSnd => tSnd t
    | eIdElim A x P hr y => tIdElim A x P hr y t
  end.

Variant tm_view1 : term -> Type :=
  | tm_view1_type {t} : ty_entry t -> tm_view1 t
  | tm_view1_fun A t : tm_view1 (tLambda A t)
  | tm_view1_rel n : tm_view1 (tRel n)
  | tm_view1_nat {t} : nat_entry t -> tm_view1 t
  | tm_view1_sig A B a b : tm_view1 (tPair A B a b)
  | tm_view1_id A x : tm_view1 (tRefl A x)
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
  | tId A x y => tm_view1_type (eId A x y)
  | tRefl A x => tm_view1_id A x
  | tIdElim A x P hr y e => tm_view1_dest e (eIdElim A x P hr y)
  end.

Variant ne_view1 : term -> Type :=
  | ne_view1_rel n : ne_view1 (tRel n)
  | ne_view1_dest t s : ne_view1 (zip1 t s).

Variant nf_view1 : term -> Type :=
  | nf_view1_type {t} : ty_entry t -> nf_view1 t
  | nf_view1_fun A t : nf_view1 (tLambda A t)
  | nf_view1_nat {t} : nat_entry t -> nf_view1 t
  | nf_view1_sig A B a b : nf_view1 (tPair A B a b)
  | nf_view1_id A x : nf_view1 (tRefl A x)
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
  | tId A x y => nf_view1_type (eId A x y)
  | tRefl A x => nf_view1_id A x
  | tIdElim A x P hr y e => nf_view1_ne (ne_view1_dest e (eIdElim A x P hr y))
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
  | tm_view1_fun _ _ 
  | tm_view1_nat _ 
  | tm_view1_sig _ _ _ _ 
  | tm_view1_id _ _ => ty_view1_anomaly
  end.

Definition stack := list dest_entry.

Fixpoint zip t (π : stack) :=
  match π with
  | nil => t
  | cons s π => zip (zip1 t s) π
  end.


(* Introduce the following in PartialFun *)

Definition callTypesFactory I (F : I -> Type) (f : forall i, F i) (pfuns : forall (i :I), PFun (f i)) : CallTypes I := {|
  ct_src i := psrc (f i) ;
  ct_tgt i := ptgt (f i) ;
|}.

#[program]
Definition callablePropsFactory I (F : I -> Type) (f : forall i, F i) (pfuns : forall (i :I), PFun (f i)) 
  : CallableProps (callTypesFactory I F f pfuns) := {|
  cp_graph i := pgraph (f i) ;
  cp_fueled i := pfueled (f i) ;
  cp_def i := pdef (f i)
|}.
Next Obligation. intros. eapply pgraph_fun. all: eassumption. Qed.
Next Obligation. intros; now eapply pfueled_graph. Qed.
Next Obligation. intros; now eapply pdef_graph. Qed.

#[export]Instance CallEmpty : CallTypes False | 5 :=
  callTypesFactory False
        (False_rect _)
        (fun bot => match bot return False_rect _ bot with end)
        (fun bot => match bot return PFun@{Set Set Set} _ with end).

#[export]Instance CallablePropsEmpty : CallableProps CallEmpty | 5 :=
      callablePropsFactory False
        (False_rect _)
        (fun bot => match bot return False_rect _ bot with end)
        (fun bot => match bot return PFun@{Set Set Set} _ with end).

Equations wh_red_stack : ∇(_ : term × stack), False ⇒ term :=
  wh_red_stack (t,π) with (build_tm_view1 t) :=
  wh_red_stack (?(tRel n)       ,π)                           (tm_view1_rel n) := ret (zip (tRel n) π) ;
  wh_red_stack (?(zip1 t s)     ,π)                           (tm_view1_dest t s) := rec (t,cons s π) ;
  wh_red_stack (?(tLambda A t)  ,nil)                         (tm_view1_fun A t) := ret (tLambda A t) ;
  wh_red_stack (?(tLambda A t)  ,cons (eApp u) π)             (tm_view1_fun A t) := rec (t[u..], π) ;
  wh_red_stack (_               ,cons _ _)                    (tm_view1_fun _ _) := undefined ;
  wh_red_stack (t               ,nil)                         (tm_view1_nat _) := ret t ;
  wh_red_stack (?(tZero)        ,cons (eNatElim _ hz _) π)    (tm_view1_nat eZero) := rec (hz,π) ;
  wh_red_stack (?(tSucc t)      ,cons (eNatElim P hz hs) π)   (tm_view1_nat (eSucc t)) := rec (hs ,cons (eApp t) (cons (eApp (tNatElim P hz hs t)) π)) ;
  wh_red_stack (t               ,cons _ _)                    (tm_view1_nat _) := undefined ;
  wh_red_stack (?(tPair A B a b),nil)                         (tm_view1_sig A B a b) := ret (tPair A B a b) ;
  wh_red_stack (?(tPair A B a b),cons eFst π)                 (tm_view1_sig A B a b) := rec (a , π) ;
  wh_red_stack (?(tPair A B a b),cons eSnd π)                 (tm_view1_sig A B a b) := rec (b , π) ;
  wh_red_stack (?(tPair A B a b),cons _ π)                    (tm_view1_sig A B a b) := undefined ;
  wh_red_stack (?(tRefl A x)    ,nil)                         (tm_view1_id A x) := ret (tRefl A x) ;
  wh_red_stack (?(tRefl A x)    ,cons (eIdElim _ _ _ hr _) π) (tm_view1_id A x) := rec (hr, π) ;
  wh_red_stack (_               ,cons _ _)                    (tm_view1_id _ _) := undefined ;
  wh_red_stack (t               ,nil)                         (tm_view1_type _) := ret t ;
  wh_red_stack (t               ,cons s _)                    (tm_view1_type _) := undefined.


Inductive Sing {F} (f : F) : Set := mkSing.
Inductive Duo {F1 F2} (f1 : F1) (f2 : F2) := mkLeft | mkRight.

Arguments mkLeft {_ _} _ {_}.
Arguments mkRight {_ _} {_} _.

#[global]
Instance callTypesSing {F} (f : F) `{PFun F f} : CallTypes (Sing f) :=
  callTypesFactory _ (fun _ => F) (fun _ => f) (fun _ => _).

#[global]
Instance callablePropsSing {F} (f : F) `{PFun F f} : CallableProps (callTypesSing f) :=
  callablePropsFactory _ (fun _ => F) (fun _ => f) (fun _ => _).

#[global]
Instance callTypesDuo {F1 F2} (f1 : F1) (f2 : F2) `{PFun F1 f1, PFun F2 f2} : CallTypes (Duo f1 f2) :=
  let F := fun x : Duo f1 f2 => match x with mkLeft _ => F1 | mkRight _ => F2 end in
  let f := fun x : Duo f1 f2 => match x as x return F x with
                               | mkLeft _ => f1 | mkRight _ => f2 end in
  let pfun := fun x : Duo f1 f2 => match x as x return PFun (f x) with
                               | mkLeft _ => _ | mkRight _ => _ end in
  callTypesFactory _ F f pfun.

#[global]
Instance callablePropsDuo {F1 F2} (f1 : F1) (f2 : F2) `{PFun F1 f1, PFun F2 f2} : CallableProps (callTypesDuo f1 f2) :=
  let F := fun x : Duo f1 f2 => match x with mkLeft _ => F1 | mkRight _ => F2 end in
  let f := fun x : Duo f1 f2 => match x as x return F x with
                               | mkLeft _ => f1 | mkRight _ => f2 end in
  let pfun := fun x : Duo f1 f2 => match x as x return PFun (f x) with
                               | mkLeft _ => _ | mkRight _ => _ end in
  callablePropsFactory _ F f pfun.

Definition call_single {F}
  (f : F) `{PFun F f} {A B} := ext_call (mkSing f) (A:=A) (B:=B).


#[export] Instance: PFun wh_red_stack := pfun_gen _ _ wh_red_stack.

Definition wh_red : ∇(t : term), Sing wh_red_stack ⇒ term :=
  fun t => call_single wh_red_stack (t,nil).

#[export] Instance: PFun wh_red := pfun_gen _ _ wh_red.

Definition wh_red_fuel n t := fueled wh_red n t.

Inductive nf_ty_view2 : term -> term -> Type :=
  | ty_sorts (s1 s2 : sort) : nf_ty_view2 (tSort s1) (tSort s2)
  | ty_prods (A A' B B' : term) :
      nf_ty_view2 (tProd A B) (tProd A' B')
  | ty_nats : nf_ty_view2 tNat tNat
  | ty_emptys : nf_ty_view2 tEmpty tEmpty
  | ty_sigs (A A' B B' : term) : nf_ty_view2 (tSig A B) (tSig A' B')
  | ty_ids A A' x x' y y' : nf_ty_view2 (tId A x y) (tId A' x' y')
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
    | ty_view1_ty (eId A x y), ty_view1_ty (eId A' x' y') :=
        ty_ids A A' x x' y y'
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
| refls A x y A' x' A'' x'' : nf_view3 (tId A x y) (tRefl A' x') (tRefl A'' x'')
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
  (** Identity witnesses *)
  | ty_view1_ty (eId A x y) with (build_nf_view1 t), (build_nf_view1 t') :=
    {
      | nf_view1_id A' x', nf_view1_id A'' x'' := refls A x y A' x' A'' x'' ;
      | nf_view1_ne _, nf_view1_ne _ := neutrals _ _ _ ;
      | nf_view1_ne _, nf_view1_id _ _ :=
          mismatch _ _ _ ;
      | nf_view1_id _ _, nf_view1_ne _ :=
          mismatch _ _ _ ;
      | _, _ := anomaly _ _ _ ;
    }
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

Definition cstate_input (c : conv_state) : Set :=
  match c with
  | tm_state | tm_red_state => term
  | ty_state | ty_red_state | ne_state | ne_red_state => unit
  end.

Definition cstate_output (c : conv_state) : Set :=
  match c with
  | ty_state | ty_red_state | tm_state | tm_red_state => unit
  | ne_state | ne_red_state => term
  end.

#[export]Existing Instance combined_monad.
#[export]Existing Instance OrecEffectExnRaise.


Section Conversion.


Definition conv_dom (c : conv_state) :=
  ∑ (_ : context) (_ : cstate_input c) (_ : term), term.
Definition conv_full_dom := ∑ (c : conv_state), conv_dom c.
Definition conv_cod (c : conv_state) := exn errors (cstate_output c).
(* Definition conv_full_cod (x : conv_full_dom) := conv_cod (x.π1). *)
Definition conv_full_cod (x : conv_full_dom) := conv_cod (x.π1).

#[local]
Notation M0 := (orec (Sing wh_red) (conv_full_dom) (conv_full_cod)).
#[local]
Notation M := (combined_orec (exn errors) (Sing wh_red) conv_full_dom conv_full_cod).

Definition conv_stmt (c : conv_state) :=
  forall x0 : conv_dom c, M (cstate_output c).


Equations conv_ty : conv_stmt ty_state :=
  | (Γ;inp;T;V) :=
    T' ← call_single wh_red T ;;[M0]
    V' ← call_single wh_red V ;;[M0]
    r ← rec (ty_red_state;Γ;tt;T';V') ;;[M]
    ret (A:= unit) r.

(* Goal True. *)
(* pose (c := conv_stmt ty_red_state). *)
(* unfold conv_stmt in c. *)
(* unfold combined in c. *)
(* Unset Printing Notations. *)
(* unfold M0 in c. *)
(* Eval unfold  conv_stmt in conv_stmt ty_red_state. *)

Definition ok {M} `{Monad M} : M unit := ret tt.

Equations conv_ty_red : conv_stmt ty_red_state :=
  | (Γ;inp;T;T') with (build_nf_ty_view2 T T') :=
  {
    | ty_sorts s s' := ret (M:=M0) (eq_sort s s') ;
    | ty_prods A A' B B' :=
        rec (ty_state;Γ;tt;A;A') ;;
        rec (ty_state;(Γ,,A);tt;B;B') (* ::: (ty_red_state;Γ;inp;tProd A B;tProd A' B') ;*) ;
    | ty_nats := ok ;
    | ty_emptys := ok ;
    | ty_sigs A A' B B' :=
        rec (ty_state;Γ;tt;A;A') ;;
        rec (ty_state;(Γ,,A);tt;B;B') (* ::: (ty_red_state;Γ;inp;tSig A B;tSig A' B') ;*) ;
      | ty_neutrals _ _ :=
          rec (ne_state;Γ;tt;T;T') ;; ok ;
    | ty_ids A A' x x' y y' :=
      rec (ty_state;Γ;tt;A;A') ;;
      rec (tm_state;Γ;A;x;x') ;;
      rec (tm_state;Γ;A;y;y')
    | ty_mismatch _ _ := raise (head_mismatch None T T') ;
    | ty_anomaly _ _ := undefined ;
  }.

(* Set Typeclasses Debug. *)
Equations conv_tm : conv_stmt tm_state :=
  | (Γ;A;t;u) :=
    A' ← call_single wh_red A ;;[M0]
    t' ← call_single wh_red t ;;[M0]
    u' ← call_single wh_red u ;;[M0]
    map (M:=M) (@id (cstate_output tm_state)) (rec (tm_red_state;Γ;A';t';u')).
    (* id <*> rec (tm_red_state;Γ;A';t';u'). *)

Equations conv_tm_red : conv_stmt tm_red_state :=
  | (Γ;A;t;u) with (build_nf_view3 A t u) :=
  {
    | types s (ty_sorts s1 s2) := undefined ;
    | types s (ty_prods A A' B B') :=
      rec (tm_state;Γ;tSort s;A;A') ;;
      rec (tm_state;Γ,,A;tSort s;B;B') (* ::: (tm_red_state;Γ;tSort s;tProd A B;tProd A' B') ;*) ;
    | types _ ty_nats := ok ;
    | types _ ty_emptys := ok ;
    | types s (ty_sigs A A' B B') :=
        rec (tm_state;Γ;tSort s;A;A') ;;
        rec (tm_state;Γ,,A;tSort s;B;B') (* ::: (tm_red_state;Γ;tSort s;tSig A B;tSig A' B') ;*) ;
    | types s (ty_ids A A' x x' y y') :=
        rec (tm_state;Γ;tSort s;A;A') ;;
        rec (tm_state;Γ;A;x;x') ;;
        rec (tm_state;Γ;A;y;y')
    | types _ (ty_neutrals _ _) :=
        rec (ne_state;Γ;tt;t;u) ;; ok ;
    | types s (ty_mismatch _ _) := raise (head_mismatch (Some (tSort s)) t u) ;
    | types _ (ty_anomaly _ _) := undefined ;
    | functions A B t u :=
        rec (tm_state;Γ,,A;B;eta_expand t;eta_expand u) (* ::: (tm_red_state;Γ;tProd A B;t;u) ;*) ;
    | zeros := ok ;
    | succs t' u' :=
        rec (tm_state;Γ;tNat;t';u') ;
    | pairs A B t u :=
        rec (tm_state;Γ;A;tFst t; tFst u) ;;
        rec (tm_state;Γ; B[(tFst t)..]; tSnd t; tSnd u) (* ::: (tm_red_state;Γ;tSig A B;t;u) ;*) ;
    | refls A x y A' x' A'' x'' := 
      rec (ty_state;Γ;tt;A';A'') ;;
      rec (tm_state;Γ;A';x';x'')
    | neutrals _ _ _ :=
      rec (ne_state;Γ;tt;t;u) ;; ok ;
    | mismatch _ _ _ := raise (head_mismatch (Some A) t u) ;
    | anomaly _ _ _ := undefined ;
  }.

Equations to_neutral_diag (t u : term) : option (ne_view1 t × ne_view1 u) :=
  | t, u with build_nf_view1 t, build_nf_view1 u =>
  {
    | nf_view1_ne te, nf_view1_ne ue => Some (te, ue)
    | _ , _ => None
  }.


Time Equations conv_ne : conv_stmt ne_state :=
  | (Γ;inp; t; t') with t, t', to_neutral_diag t t' :=
  {
    | _, _, Some (ne_view1_rel n, ne_view1_rel n') with n =? n' :=
    { | false := raise (variable_mismatch n n') ;
      | true with (ctx_access Γ n) := 
        {
        | exception e => undefined ;
        | success d => ret d (* ::: (ne_state;Γ;inp;tRel n; tRel n')*)
        }
    } ;
    | _, _, Some (ne_view1_dest n (eApp t), ne_view1_dest n' (eApp t')) =>
      T ← rec (ne_red_state;Γ;tt;n;n') ;;
      match T with
      | tProd A B => 
        rec (tm_state;Γ;A;t;t') ;; ret B[t..]
      |  _ => undefined (** the whnf of the type of an applied neutral must be a Π type!*)
      end ;
    | _, _, Some (ne_view1_dest n (eNatElim P hz hs), ne_view1_dest n' (eNatElim P' hz' hs')) =>
      rn ← rec (ne_red_state;Γ;tt;n;n') ;;
      match rn with
      | tNat =>
          rec (ty_state;(Γ,,tNat);tt;P;P') ;;
          rec (tm_state;Γ;P[tZero..];hz;hz') ;;
          rec (tm_state;Γ;elimSuccHypTy P;hs;hs') ;;
          ret P[n..]
      | _ => undefined
      end ;
    | _, _, Some (ne_view1_dest n (eEmptyElim P), ne_view1_dest n' (eEmptyElim P')) =>
      rn ← rec (ne_red_state;Γ;tt;n;n') ;;
      match rn with
      | tEmpty =>
          rec (ty_state;(Γ,,tEmpty);tt;P;P') ;;
          ret P[n..]
      | _ => undefined
      end ;
    | _, _, Some (ne_view1_dest n eFst, ne_view1_dest n' eFst) =>
      T ← rec (ne_red_state;Γ;tt;n;n') ;;
      match T with
      | tSig A B => ret A 
      | _ => undefined (** the whnf of the type of a projected neutral must be a Σ type!*)
      end ;
    | _, _, Some (ne_view1_dest n eSnd, ne_view1_dest n' eSnd) =>
      T ← rec (ne_red_state;Γ;tt;n;n') ;;
      match T with
      | tSig A B => ret B[(tFst n)..]
      | _ => undefined (** the whnf of the type of a projected neutral must be a Σ type!*)
      end ; 
    | _, _, Some (ne_view1_dest n (eIdElim A x P hr y), ne_view1_dest n' (eIdElim A' x' P' hr' y')) =>
      T ← rec (ne_red_state;Γ;tt;n;n') ;;
      match T with
      | tId _ _ _ =>
        rec (ty_state;Γ;tt;A;A') ;;
        rec (tm_state;Γ;A;x;x') ;;
        rec (ty_state;Γ,,A,,tId A⟨↑⟩ x⟨↑⟩ (tRel 0);tt;P;P') ;;
        rec (tm_state;Γ;P[tRefl A x.: x..];hr;hr') ;;
        rec (tm_state;Γ;A;y;y') ;;
        ret P[n .: y..]
      | _ => undefined
      end ;
    | w, w', _ => raise (destructor_mismatch w w')
  }.


(*Time Equations conv_ne_alt : conv_stmt ne_state :=
  | (Γ;inp;tRel n;tRel n')
    with n =? n' :=
    { | false := raise (variable_mismatch n n') ;
      | true with (ctx_access Γ n) := 
        {
        | error e => undefined ;
        | ok d => ret d (* ::: (ne_state;Γ;inp;tRel n; tRel n')*)
        }
    } ;
  | (Γ;inp;tApp n t ; tApp n' t') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | tProd A B => 
      rec (tm_state;Γ;A;t;t') ;; ret B[t..]
      (* (ret (B[t..])) ::: (ne_state;Γ;inp;tApp n t; tApp n' t') *)
    |  _ => undefined (** the whnf of the type of an applied neutral must be a Π type!*)
    end ;
  | (Γ;inp;tNatElim P hz hs n;tNatElim P' hz' hs' n') :=
    rn ← rec (ne_red_state;Γ;tt;n;n') ;;
    match rn with
    | tNat =>
        rec (ty_state;(Γ,,tNat);tt;P;P') ;;
        rec (tm_state;Γ;P[tZero..];hz;hz') ;;
        rec (tm_state;Γ;elimSuccHypTy P;hs;hs') ;;
        ret P[n..]
        (* ret (P[n..]) ::: (ne_state;Γ;inp;tNatElim P hz hs n;tNatElim P' hz' hs' n') *)
    | _ => undefined
    end ;
  | (Γ;inp;tEmptyElim P n;tEmptyElim P' n') :=
    rn ← rec (ne_red_state;Γ;tt;n;n') ;;
    match rn with
    | tEmpty =>
        rec (ty_state;(Γ,,tEmpty);tt;P;P') ;;
        ret P[n..]
        (* ret (P[n..]) ::: (ne_state;Γ;inp;tEmptyElim P n;tEmptyElim P' n') *)
    | _ => undefined
    end ;
  | ( Γ; inp ; tFst n; tFst n') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | tSig A B => ret A (* ::: (ne_state;Γ; inp; tFst n; tFst n')*)
    | _ => undefined (** the whnf of the type of a projected neutral must be a Σ type!*)
    end ;
  | ( Γ; inp ; tSnd n; tSnd n') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | tSig A B => ret B[(tFst n)..]
      (* ret (B[(tFst n)..]) ::: (ne_state;Γ; inp; tSnd n; tSnd n') *)
    | _ => undefined (** the whnf of the type of a projected neutral must be a Σ type!*)
    end ; 
  | (Γ;_;n;n') := raise (destructor_mismatch n n'). *)

Equations conv_ne_red : conv_stmt ne_red_state :=
  | (Γ;inp;t;u) :=
    Ainf ← rec (ne_state;Γ;tt;t;u) ;;[M]
    r ← call_single wh_red Ainf ;;[M0]
    ret (M:=M) r.

Equations conv : ∇(x : conv_full_dom), Sing wh_red ⇒ exn errors ♯ cstate_output x.π1 :=
  | (ty_state; Γ ; inp ; T; V) := conv_ty (Γ; inp; T; V);
  | (ty_red_state; Γ ; inp ; T; V) := conv_ty_red (Γ; inp; T; V);
  | (tm_state; Γ ; inp ; T; V) := conv_tm (Γ; inp; T; V);
  | (tm_red_state; Γ ; inp ; T; V) := conv_tm_red (Γ; inp; T; V);
  | (ne_state; Γ ; inp ; T; V) := conv_ne (Γ; inp; T; V);
  | (ne_red_state; Γ ; inp ; T; V) := conv_ne_red (Γ; inp; T; V).

End Conversion.


#[export] Instance: PFun conv := pfun_gen _ _ conv.

Section Typing.

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

Definition typing_dom (c : typing_state) :=
  ∑ (_ : context) (_ : tstate_input c), term.
Definition typing_full_dom := ∑ (c : typing_state), typing_dom c.
Definition typing_cod (c : typing_state) := exn errors (tstate_output c).
Definition typing_full_cod (x : typing_full_dom) := typing_cod (x.π1).

#[local]Definition ϕ := Duo wh_red conv.

#[local]
Notation M0 := (orec ϕ (typing_full_dom) (typing_full_cod)).
#[local]
Notation M := (combined_orec (exn errors) ϕ (typing_full_dom) (typing_full_cod)).

Definition typing_stmt (c : typing_state) :=
  forall x0 : typing_dom c, M (tstate_output c).

Equations typing_wf_ty : typing_stmt wf_ty_state :=
  typing_wf_ty (Γ;_;T) with (build_ty_view1 T) :=
  {
    | ty_view1_ty (eSort s) := ok ;
    | ty_view1_ty (eProd A B) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        rec (wf_ty_state;Γ,,A;tt;B) ;
    | ty_view1_ty (eNat) := ok ;
    | ty_view1_ty (eEmpty) := ok ;
    | ty_view1_ty (eSig A B) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        rec (wf_ty_state;Γ,,A;tt;B) ;
    | ty_view1_ty (eId A x y) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        rec (check_state;Γ;A;x) ;;
        rec (check_state;Γ;A;y)
    | ty_view1_small _ :=
        r ← rec (inf_red_state;Γ;tt;T) ;;[M]
        match r with
        | tSort _ => ok
        | _ => raise type_error
        end
    | ty_view1_anomaly := raise type_error ;
  }.

  Equations typing_inf : typing_stmt inf_state :=
  | (Γ;_;t) with t := {
    | tRel n with (ctx_access Γ n) :=
        {
          | exception _ := raise (variable_not_in_context n Γ) ;
          | success d := ret d
        } ;
    | tSort s := raise type_error ;
    | tProd A B :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | tSort sA =>
            rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
            match rB with
            | tSort sB => ret (tSort (sort_of_product sA sB))
            | _ => raise type_error
            end
        | _ => raise type_error
        end ;
    | tLambda A u :=
        rec (wf_ty_state;Γ;tt;A) ;;[M]
        B ← rec (inf_state;Γ,,A;tt;u) ;;
        ret (tProd A B) ;
    | tApp f u :=
      rf ← rec (inf_red_state;Γ;tt;f) ;;
      match rf with
      | tProd A B =>
          rec (check_state;Γ;A;u) ;;
          ret B[u..]
      | _ => raise type_error
      end ;
    | tNat := ret U ;
    | tZero := ret tNat ;
    | tSucc u :=
        ru ← rec (inf_red_state;Γ;tt;u) ;;
        match ru with
        | tNat => ret tNat
        | _ => raise type_error
        end ;
    | tNatElim P hz hs n :=
      rn ← rec (inf_red_state;Γ;tt;n) ;;
      match rn with
      | tNat =>
          rec (wf_ty_state;(Γ,,tNat);tt;P) ;;
          rec (check_state;Γ;P[tZero..];hz) ;;
          rec (check_state;Γ;elimSuccHypTy P;hs) ;;
          ret P[n..]
      | _ => raise type_error
      end ;
    | tEmpty := ret U ;
    | tEmptyElim P e :=
        re ← rec (inf_red_state;Γ;tt;e) ;;
        match re with
        | tEmpty =>
            rec (wf_ty_state;(Γ,,tEmpty);tt;P) ;;
            ret P[e..]
        | _ => raise type_error
        end ;
    | tSig A B :=
      rA ← rec (inf_red_state;Γ;tt;A) ;;
      match rA with
      | tSort sA =>
          rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
          match rB with
          | tSort sB => ret (tSort (sort_of_product sA sB)) (* Should that be taken as a parameter for sigma as well ? *)
          | _ => raise type_error
          end
      | _ => raise type_error
      end ;
    | tPair A B a b :=
      rec (wf_ty_state;Γ;tt;A) ;;
      rec (wf_ty_state;Γ,,A;tt;B) ;;
      rec (check_state;Γ;A; a) ;;
      rec (check_state;Γ;B[a..]; b) ;;
      ret (tSig A B) ;
    | tFst u :=
      rt ← rec (inf_red_state; Γ; tt; u) ;;
      match rt with
      | tSig A B => ret A
      | _ => raise type_error
      end ;
    | tSnd u :=
      rt ← rec (inf_red_state; Γ; tt; u) ;;
      match rt with
      | tSig A B => ret (B[(tFst u)..])
      | _ => raise type_error
      end ;
    | tId A x y :=
      rA ← rec (inf_red_state;Γ;tt;A) ;;
      match rA with
      | tSort sA =>
        rec (check_state;Γ;A;x) ;;
        rec (check_state;Γ;A;y) ;;
        ret (tSort sA)
      | _ => raise type_error
      end ;
    | tRefl A x :=
      rec (wf_ty_state;Γ;tt;A) ;;
      rec (check_state;Γ;A;x) ;;
      ret (tId A x x) ;
    | tIdElim A x P hr y e :=
      rec (wf_ty_state;Γ;tt;A) ;;
      rec (check_state;Γ;A;x) ;;
      rec (wf_ty_state;Γ,,A,,tId A⟨↑⟩ x⟨↑⟩ (tRel 0);tt;P) ;;
      rec (check_state;Γ;P[tRefl A x.: x..];hr) ;;
      rec (check_state;Γ;A;y) ;;
      rec (check_state;Γ;tId A x y;e) ;;
      ret P[e.:y..] ;
  }.

  Equations typing_inf_red : typing_stmt inf_red_state :=
  | (Γ;_;t) :=
    T ← rec (inf_state;Γ;_;t) ;;[M]
    r ← ext_call (mkLeft wh_red (f2:=conv)) T ;;[M0]
    ret (M:=M) r.

  Equations typing_check : typing_stmt check_state :=
  | (Γ;T;t) :=
    T' ← rec (inf_state;Γ;tt;t) ;;[M]
    ext_call (I:=ϕ) (mkRight conv) (ty_state;Γ;tt;T';T).

  Equations typing : ∇ (x : typing_full_dom), ϕ ⇒ exn errors ♯ tstate_output x.π1 :=
  | (wf_ty_state; Γ; inp; T) := typing_wf_ty (Γ;inp;T)
  | (inf_state; Γ; inp; t) := typing_inf (Γ;inp;t)
  | (inf_red_state; Γ; inp; t) := typing_inf_red (Γ;inp;t)
  | (check_state; Γ; inp; t) := typing_check (Γ;inp;t).

End Typing.

#[export] Instance: PFun typing := pfun_gen _ _ typing.

Section CtxTyping.

  Equations check_ctx : ∇ (Γ : context), Sing typing ⇒ exn errors ♯ unit :=
    check_ctx ε := ret tt ;
    check_ctx (Γ,,A) :=
      rec Γ ;;[combined_orec (exn _) _ _ _]
      call_single typing (wf_ty_state;Γ;tt;A).

End CtxTyping.
