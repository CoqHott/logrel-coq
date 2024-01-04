(** * LogRel.Decidability.Functions: conversion and type-checker implementation. *)
From Coq Require Import Nat Lia List.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.
From PartialFun Require Import Monad PartialFun.

Import MonadNotations.
Set Universe Polymorphism.
Import IndexedDefinitions.

Definition singleton_store {F} (f : F) : forall (x : unit), unit := fun _ => tt.

(** DO NOT PUT AS INSTANCE IN GENERAL
    (create loops in typeclass search since it autofires itself) *)
Definition singleton_pfun {F} (f : F) `{PFun F f} : forall (x : unit), PFun (singleton_store f x).
Proof. destruct H; now econstructor. Defined.

Definition call_single {F}
  (f : F) `{PFun F f} {A B} :=
  call (pfun:=singleton_pfun f) tt (A:=A) (B:=B).

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
  | eSig A B : ty_entry (tSig A B)
  | eList A : ty_entry (tList A).

Variant nat_entry : term -> Type :=
  | eZero : nat_entry tZero
  | eSucc t : nat_entry (tSucc t).

Variant list_entry : term -> Type :=
  | eNil A : list_entry (tNil A)
  | eCons A hd tl : list_entry (tCons A hd tl).

Variant ne_entry : Type :=
  | eEmptyElim (P : term)
  | eNatElim (P : term) (hs hz : term)
  | eApp (u : term)
  | eFst
  | eSnd
  | eListElim (A P hnil hcons : term).

Definition zip1_ne (t : term) (e : ne_entry) : term :=
  match e with
    | eEmptyElim P => (tEmptyElim P t)
    | eNatElim P hs hz => (tNatElim P hs hz t) 
    | eApp u => (tApp t u)
    | eFst => tFst t
    | eSnd => tSnd t
    | eListElim A P hnil hcons => (tListElim A P hnil hcons t)
  end.

Variant tm_view1 : term -> Type :=
  | tm_view1_type {t} : ty_entry t -> tm_view1 t
  | tm_view1_fun A t : tm_view1 (tLambda A t)
  | tm_view1_rel n : tm_view1 (tRel n)
  | tm_view1_nat {t} : nat_entry t -> tm_view1 t
  | tm_view1_sig A B a b : tm_view1 (tPair A B a b)
  | tm_view1_list {t} : list_entry t -> tm_view1 t
  | tm_view1_map A B f l : tm_view1 (tMap A B f l)
  | tm_view1_dest t (s : ne_entry) : tm_view1 (zip1_ne t s).

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
  | tList A => tm_view1_type (eList A)
  | tNil A => tm_view1_list (eNil A)
  | tCons A hd tl => tm_view1_list (eCons A hd tl)
  | tMap A B f l => tm_view1_map A B f l
  | tListElim A P hn hc l => tm_view1_dest l (eListElim A P hn hc)
  end.

Variant ne_view1 : term -> Type :=
  | ne_view1_rel n : ne_view1 (tRel n)
  | ne_view1_dest t s : ne_view1 (zip1_ne t s).

Variant nf_view1 : term -> Type :=
  | nf_view1_type {t} : ty_entry t -> nf_view1 t
  | nf_view1_fun A t : nf_view1 (tLambda A t)
  | nf_view1_nat {t} : nat_entry t -> nf_view1 t
  | nf_view1_sig A B a b : nf_view1 (tPair A B a b)
  | nf_view1_list {t} : list_entry t -> nf_view1 t
  | nf_view1_map A B f l : nf_view1 (tMap A B f l)
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
  | tList A => nf_view1_type (eList A)
  | tNil A => nf_view1_list (eNil A)
  | tCons A hd tl => nf_view1_list (eCons A hd tl)
  | tMap A B f l => nf_view1_map A B f l
  | tListElim A P hn hc l => nf_view1_ne (ne_view1_dest l (eListElim A P hn hc))
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
  | tm_view1_list _      
  | tm_view1_map _ _ _ _ => ty_view1_anomaly
  end.

Variant stack_entry : Type :=
| sEmptyElim (P : term)
| sNatElim (P : term) (hs hz : term)
| sApp (u : term)
| sFst
| sSnd
| sMap (A B f : term)
| sListElim (A P hnil hcons : term).

Definition to_stack (e : ne_entry) : stack_entry :=
  match e with
  | eEmptyElim P => sEmptyElim P
  | eNatElim P hs hz => sNatElim P hs hz
  | eApp u => sApp u
  | eFst => sFst
  | eSnd => sSnd
  | eListElim A P hn hc => sListElim A P hn hc
  end.

Coercion to_stack : ne_entry >-> stack_entry.

Definition zip1 (t : term) (s : stack_entry) : term :=
match s with
  | sEmptyElim P => (tEmptyElim P t)
  | sNatElim P hs hz => (tNatElim P hs hz t) 
  | sApp u => (tApp t u)
  | sFst => tFst t
  | sSnd => tSnd t
  | sMap A B f => tMap A B f t
  | sListElim A P hn hc => tListElim A P hn hc t
end.

Definition stack := list stack_entry.

Fixpoint zip t (π : stack) :=
  match π with
  | [::] => t
  | s :: π => zip (zip1 t s) π
  end.

Definition empty_store : forall (x: False), match x return Set with end :=
  fun x => match x as x return match x return Set with end with end.

#[global]
Instance empty_pfun : forall (x:False), PFun@{Set Set Set} (empty_store x) | 5 :=
  fun x => match x as x return PFun (empty_store x) with end.

Arguments rec {_ _ _ _ _ _}.

Equations compact : term × stack ⇀[empty_store] term :=
  compact (t,[::]) := ret t ;
  compact (t,s::π) with (Map.into_view t) := {
  compact (?(u),s::π) (@Map.IsNotMap u _) := rec (zip1 u s,π) ;
  compact (?(tMap A B f l),s::π) (@Map.IsMap A B f l) with s := {
    | sMap B' C g => rec (tMap A C (comp A g f) l,π);
    | sListElim B' P hn hc => rec (tListElim B' P hn hc (tMap A B f l),π);
    | _ => undefined ;
  }}.

#[local] Instance: forall x, PFun (singleton_store compact x) := singleton_pfun compact.

Equations wh_red_stack : term × stack ⇀[singleton_store compact] term :=
  wh_red_stack (t,π) with (build_tm_view1 t) :=
  wh_red_stack (?(tRel n)       ,π)                       (tm_view1_rel n)
    := call_single compact ((tRel n),π) ;
  wh_red_stack (?(zip1_ne t s)  ,π)                       (tm_view1_dest t s)
    := rec (t,(to_stack s) :: π) ;
  wh_red_stack (?(tMap A B f l),π)                       (tm_view1_map A B f l)
    := rec (l,(sMap A B f) :: π) ;
  wh_red_stack (?(tLambda A t)  ,[::])                    (tm_view1_fun A t)
    := ret (tLambda A t) ;
  wh_red_stack (?(tLambda A t)  ,(sApp u) :: π)           (tm_view1_fun A t) 
    := rec (t[u..], π) ;
  wh_red_stack (_               ,_ :: _)                  (tm_view1_fun _ _)
    := undefined ;
  wh_red_stack (t               ,[::])                    (tm_view1_nat _)
    := ret t ;
  wh_red_stack (?(tZero)        ,(sNatElim _ hz _) :: π)  (tm_view1_nat eZero)
    := rec (hz,π) ;
  wh_red_stack (?(tSucc t)      ,(sNatElim P hz hs) :: π) (tm_view1_nat (eSucc t))
    := rec (hs ,(sApp t) :: (sApp (tNatElim P hz hs t) :: π)) ;
  wh_red_stack (t               , _ :: _)                 (tm_view1_nat _)
    := undefined ;
  wh_red_stack (?(tPair A B a b),[::])                    (tm_view1_sig A B a b)
    := ret (tPair A B a b) ;
  wh_red_stack (?(tPair A B a b),sFst :: π)               (tm_view1_sig A B a b)
    := rec (a , π) ;
  wh_red_stack (?(tPair A B a b),sSnd :: π)               (tm_view1_sig A B a b)
    := rec (b , π) ;
  wh_red_stack (?(tPair A B a b),_ :: π)                  (tm_view1_sig A B a b)
    := undefined ;
  wh_red_stack (t               ,[::])                   (tm_view1_list _)
    := ret t ;
  wh_red_stack (?(tNil A)       ,(sMap _ B _) :: π)      (tm_view1_list (eNil A))
    := rec (tNil B, π) ;
  wh_red_stack (?(tCons _ hd tl),(sMap A B f) :: π)      (tm_view1_list (eCons _ hd tl))
    := rec (tCons B (tApp f hd) (tMap A B f tl), π) ;
  wh_red_stack (?(tNil A)       ,(sListElim _ _ hnil _) :: π)      (tm_view1_list (eNil A))
    := rec (hnil, π) ;
  wh_red_stack (?(tCons _ hd tl),(sListElim A P hnil hcons) :: π)      (tm_view1_list (eCons _ hd tl))
    := rec (tApp (tApp (tApp hcons hd) tl) (tListElim A P hnil hcons tl), π) ;
  wh_red_stack (t               , _ :: _)                 (tm_view1_list _)
    := undefined;
  wh_red_stack (t               ,[::])                    (tm_view1_type _)
    := ret t ;
  wh_red_stack (t               ,s :: _)                  (tm_view1_type _)
    := undefined.

#[local] Instance: forall x, PFun (singleton_store wh_red_stack x) := singleton_pfun wh_red_stack.

Equations wh_red : term ⇀[singleton_store wh_red_stack] term :=
  wh_red t := call_single wh_red_stack (t,[::]).

Definition wh_red_fuel n t := fueled wh_red n t.

Inductive nf_ty_view2 : term -> term -> Type :=
  | ty_sorts (s1 s2 : sort) : nf_ty_view2 (tSort s1) (tSort s2)
  | ty_prods (A A' B B' : term) :
      nf_ty_view2 (tProd A B) (tProd A' B')
  | ty_nats : nf_ty_view2 tNat tNat
  | ty_emptys : nf_ty_view2 tEmpty tEmpty
  | ty_sigs (A A' B B' : term) : nf_ty_view2 (tSig A B) (tSig A' B')
  | ty_lists (A A' : term) : nf_ty_view2 (tList A) (tList A')
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
    |ty_view1_ty (eList A), ty_view1_ty (eList A') :=
        ty_lists A A'
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
| nils A A1 A2 : nf_view3 (tList A) (tNil A1) (tNil A2)
| conss A A1 A2 hd1 hd2 tl1 tl2 : nf_view3 (tList A) (tCons A1 hd1 tl1) (tCons A2 hd2 tl2)
(* | map_l T A B f n n' : nf_view3 (tList T) (tMap A B f n) n' 
| map_r T A' B' f' n n' : nf_view3 (tList T) n (tMap A' B' f' n')
| maps T A A' B B' f f' n n' : nf_view3 (tList T) (tMap A B f n) (tMap A' B' f' n') *)
| neutral_lists A n n' : nf_view3 (tList A) n n'
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
  (** Lists *)
  | ty_view1_ty (eList A) with (build_nf_view1 t), (build_nf_view1 t') :=
  {
    | nf_view1_list (eNil A1), nf_view1_list (eNil A2) :=
      nils A A1 A2
    | nf_view1_list (eCons A1 hd1 tl1), nf_view1_list (eCons A2 hd2 tl2) :=
      conss A A1 A2 hd1 hd2 tl1 tl2
    | nf_view1_map _ _ _ _, nf_view1_map _ _ _ _ := neutral_lists _ _ _ ;
    | nf_view1_map _ _ _ _, nf_view1_ne _ := neutral_lists _ _ _ ;
    | nf_view1_ne _, nf_view1_map _ _ _ _ := neutral_lists _ _ _ ;
    | nf_view1_ne _, nf_view1_ne _ := neutral_lists _ _ _ ;
    | nf_view1_list _, nf_view1_list _ :=
        mismatch _ _ _ ;
    | nf_view1_ne _, nf_view1_list _ :=
        mismatch _ _ _ ;
    | nf_view1_map _ _ _ _ , nf_view1_list _ :=
        mismatch _ _ _ ;
    | nf_view1_list _, nf_view1_ne _ :=
        mismatch _ _ _ ;
    | nf_view1_list _, nf_view1_map _ _ _ _ :=
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
  | ne_red_state (** Comparison of neutrals with a reduced type *)
  | ne_list_state. (** Comparison of neutral lists *)

Definition cstate_input (c : conv_state) : Type :=
  match c with
  | tm_state | tm_red_state | ne_list_state => term
  | ty_state | ty_red_state | ne_state | ne_red_state => unit
  end.

Definition cstate_output (c : conv_state) : Type :=
  match c with
  | ty_state | ty_red_state | tm_state | tm_red_state | ne_list_state => unit
  | ne_state | ne_red_state => term
  end.

Definition errrec {I F} φ {pfun A B} C := @irec I F φ pfun A B (result C).

Definition monad_erec : forall {I F φ pfun A B}, Monad (@errrec I F φ pfun A B) :=
  fun {I F φ pfun A B} => mon_trans_mon (irec φ A B) _.

Definition ecall {I F} {ϕ : forall i, F i} `{pfun : forall i, PFun (ϕ i)} {A B} (g : I) (x : psrc (ϕ g)) : @errrec I F ϕ pfun A B (ptgt (ϕ g) x) :=
  lift (irec _ A B) _ _ (call g x).

Section Conversion.


Definition conv_dom (c : conv_state) :=
  ∑ (_ : context) (_ : cstate_input c) (_ : term), term.
Definition conv_full_dom := ∑ (c : conv_state), conv_dom c.
Definition conv_cod (c : conv_state) := result (cstate_output c).
Definition conv_full_cod (x : conv_full_dom) := conv_cod (x.π1).

#[local] Instance: forall x, PFun (singleton_store wh_red x) := singleton_pfun wh_red.

#[local]
Notation M0 := (irec (singleton_store wh_red) (conv_full_dom) (conv_full_cod)).
#[local]
Notation M := (errrec (singleton_store wh_red) (A:=conv_full_dom) (B:=conv_full_cod)).

#[local] Instance: Monad M0 := MonadOrec.
#[local] Instance: Monad M := monad_erec.

Definition conv_stmt (c : conv_state) := forall x0 : conv_dom c, M (cstate_output c).

Equations conv_ty : conv_stmt ty_state :=
  | (Γ;inp;T;V) :=
    T' ← call_single wh_red T ;;[M0]
    V' ← call_single wh_red V ;;[M0]
    id <*> rec (ty_red_state;Γ;tt;T';V').

Equations conv_ty_red : conv_stmt ty_red_state :=
  | (Γ;inp;T;T') with (build_nf_ty_view2 T T') :=
  {
    | ty_sorts s s' := ret (eq_sort s s') ;
    | ty_prods A A' B B' :=
        rec (ty_state;Γ;tt;A;A') ;;
        rec (ty_state;(Γ,,A);tt;B;B') (* ::: (ty_red_state;Γ;inp;tProd A B;tProd A' B') ;*) ;
    | ty_nats := success ;
    | ty_emptys := success ;
    | ty_sigs A A' B B' :=
        rec (ty_state;Γ;tt;A;A') ;;
        rec (ty_state;(Γ,,A);tt;B;B') (* ::: (ty_red_state;Γ;inp;tSig A B;tSig A' B') ;*) ;
      | ty_neutrals _ _ :=
          rec (ne_state;Γ;tt;T;T') ;; success (M:=irec _ _ _) ;
    | ty_lists A A' :=
      rec (ty_state;Γ;tt;A;A') ;
    | ty_mismatch _ _ := raise (head_mismatch None T T') ;
    | ty_anomaly _ _ := undefined ;
  }.

Equations conv_tm : conv_stmt tm_state :=
  | (Γ;A;t;u) :=
    A' ← call_single wh_red A ;;[M0]
    t' ← call_single wh_red t ;;[M0]
    u' ← call_single wh_red u ;;[M0]
    id <*> rec (tm_red_state;Γ;A';t';u'). 

Equations conv_tm_red : conv_stmt tm_red_state :=
  | (Γ;A;t;u) with (build_nf_view3 A t u) :=
  {
    | types s (ty_sorts s1 s2) := undefined ;
    | types s (ty_prods A A' B B') :=
      rec (tm_state;Γ;tSort s;A;A') ;;
      rec (tm_state;Γ,,A;tSort s;B;B') (* ::: (tm_red_state;Γ;tSort s;tProd A B;tProd A' B') ;*) ;
    | types _ ty_nats := success ;
    | types _ ty_emptys := success ;
    | types s (ty_sigs A A' B B') :=
        rec (tm_state;Γ;tSort s;A;A') ;;
        rec (tm_state;Γ,,A;tSort s;B;B') (* ::: (tm_red_state;Γ;tSort s;tSig A B;tSig A' B') ;*) ;
    | types _ (ty_lists A A') := 
        rec (tm_state;Γ;tSort s; A; A') ;
    | types _ (ty_neutrals _ _) :=
        rec (ne_state;Γ;tt;t;u) ;; success (M:=M0) ;
    | types s (ty_mismatch _ _) := raise (head_mismatch (Some (tSort s)) t u) ;
    | types _ (ty_anomaly _ _) := undefined ;
    | functions A B t u :=
        rec (tm_state;Γ,,A;B;eta_expand t;eta_expand u) (* ::: (tm_red_state;Γ;tProd A B;t;u) ;*) ;
    | zeros := success ;
    | succs t' u' :=
        rec (tm_state;Γ;tNat;t';u') ;
    | pairs A B t u :=
        rec (tm_state;Γ;A;tFst t; tFst u) ;;
        rec (tm_state;Γ; B[(tFst t)..]; tSnd t; tSnd u) (* ::: (tm_red_state;Γ;tSig A B;t;u) ;*) ;
    | nils A A1 A2 := success
      (* rec (ty_state;Γ;tt;A1;A2) ;;
      rec (ty_state;Γ;tt;A1;A) *)
    | conss A A1 A2 hd1 hd2 tl1 tl2 => 
      (* rec (ty_state;Γ;tt;A1;A2) ;;
      rec (ty_state;Γ;tt;A1;A) ;; *)
      rec (tm_state;Γ;A;hd1;hd2) ;;
      rec (tm_state;Γ;tList A; tl1; tl2)
    | neutral_lists A _ _ :=
      rec (ne_list_state;Γ;A;t;u) ;; success (M:=M0) ;
    | neutrals A _ _ :=
      rec (ne_state;Γ;tt;t;u) ;; success (M:=M0) ;
    | mismatch _ _ _ := raise (head_mismatch (Some A) t u) ;
    | anomaly _ _ _ := undefined ;
  }.
  
Equations to_neutral_diag (t u : term) : option (ne_view1 t × ne_view1 u) :=
  | t, u with build_nf_view1 t, build_nf_view1 u =>
  {
    | nf_view1_ne te, nf_view1_ne ue => Some (te, ue)
    | _ , _ => None
  }.

Equations conv_ne : conv_stmt ne_state :=
  | (Γ;inp; t; t') with t, t', to_neutral_diag t t' :=
  {
    | _, _, Some (ne_view1_rel n, ne_view1_rel n') with n =? n' :=
    { | false := raise (variable_mismatch n n') ;
      | true with (ctx_access Γ n) := 
        {
        | error e => undefined ;
        | ok d => ret d (* ::: (ne_state;Γ;inp;tRel n; tRel n')*)
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
    | _, _, Some (ne_view1_dest n (eListElim A P hn hc), ne_view1_dest n' (eListElim A' P' hn' hc')) =>
      rec (ty_state;Γ;tt;A;A') ;;
      rec (ne_list_state;Γ;A;n;n') ;;
      rec (ty_state;Γ,,tList A;tt;P;P') ;;
      rec (tm_state;Γ;P[(tNil A)..];hn;hn') ;;
      rec (tm_state;Γ;elimConsHypTy A P;hc;hc') ;;
      ret (P[n..]) ;
    | w, w', Some _ => raise (destructor_mismatch w w')
    | _, _, None => undefined
  }.
  
Equations conv_ne_list : conv_stmt ne_list_state :=
  | (Γ;B; t; t') :=
    let r := Map.eta B t in
    let r' := Map.eta B t' in
    T ← rec (ne_red_state;Γ;tt;r.(Map.lst);r'.(Map.lst)) ;;
    match T with
    | tList A =>
        rec (tm_state;Γ,,A;B⟨↑⟩;r.(Map.fn);r'.(Map.fn))
    | _ => undefined
    end.

Equations conv_ne_red : conv_stmt ne_red_state :=
  | (Γ;inp;t;u) :=
    Ainf ← rec (ne_state;Γ;tt;t;u) ;;
    ecall tt Ainf.

Equations conv : ∇[singleton_store wh_red] (x : conv_full_dom), conv_full_cod x :=
  | (ty_state; Γ ; inp ; T; V) := conv_ty (Γ; inp; T; V);
  | (ty_red_state; Γ ; inp ; T; V) := conv_ty_red (Γ; inp; T; V);
  | (tm_state; Γ ; inp ; T; V) := conv_tm (Γ; inp; T; V);
  | (tm_red_state; Γ ; inp ; T; V) := conv_tm_red (Γ; inp; T; V);
  | (ne_state; Γ ; inp ; T; V) := conv_ne (Γ; inp; T; V);
  | (ne_red_state; Γ ; inp ; T; V) := conv_ne_red (Γ; inp; T; V)
  | (ne_list_state;Γ;B;t;t') := conv_ne_list (Γ;B;t;t').

End Conversion.

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

Definition binary_store_ty@{u} F1 F2 := fun b : bool => if b return Type@{u} then F1 else F2.
Definition binary_store@{u} {F1 F2: Type@{u}} (f1 : F1) (f2 : F2) :
  forall b, binary_store_ty F1 F2 b :=
  fun b => if b as b return binary_store_ty F1 F2 b then f1 else f2.

(** DO NOT PUT AS INSTANCE IN GENERAL
    (create loops in typeclass search since it autofires itself) *)
Definition binary_pfun@{u a b} {F1 F2: Type@{u}} (f1 : F1) (f2 : F2)
  `{h1: PFun@{u a b} F1 f1} `{h2: PFun@{u a b} F2 f2} :
  forall b, PFun@{u a b} (binary_store f1 f2 b).
Proof.
  intros b; destruct b; [destruct h1| destruct h2]; now econstructor.
Defined.

#[local]
Instance: forall b, PFun (binary_store wh_red conv b) := binary_pfun wh_red conv.


Definition typing_dom (c : typing_state) :=
  ∑ (_ : context) (_ : tstate_input c), term.
Definition typing_full_dom := ∑ (c : typing_state), typing_dom c.
Definition typing_cod (c : typing_state) := result (tstate_output c).
Definition typing_full_cod (x : typing_full_dom) := typing_cod (x.π1).

Definition ϕ := (binary_store wh_red conv).
Definition wh_red_key := true.
Definition conv_key := false.

#[local]
Notation M0 := (irec ϕ (typing_full_dom) (typing_full_cod)).
#[local]
Notation M := (errrec ϕ (A:=typing_full_dom) (B:=typing_full_cod)).

#[local] Instance: Monad M0 := MonadOrec.
#[local] Instance: Monad M := monad_erec.

Definition typing_stmt (c : typing_state) := forall x0 : typing_dom c, M (tstate_output c).

Equations typing_wf_ty : typing_stmt wf_ty_state :=
  typing_wf_ty (Γ;_;T) with (build_ty_view1 T) :=
  {
    | ty_view1_ty (eSort s) := success ;
    | ty_view1_ty (eProd A B) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        id <*> rec (wf_ty_state;Γ,,A;tt;B) ;
    | ty_view1_ty (eNat) := success ;
    | ty_view1_ty (eEmpty) := success ;
    | ty_view1_ty (eSig A B) :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        id <*> rec (wf_ty_state;Γ,,A;tt;B) ;
    | ty_view1_ty (eList A) :=
      rec (wf_ty_state;Γ;tt;A)
    | ty_view1_small _ :=
        r ← rec (inf_red_state;Γ;tt;T) ;;[M]
        match r with
        | tSort _ => success (M:=M0)
        | _ => raise (M:=M0) type_error
        end
    | ty_view1_anomaly := raise type_error ;
  }.

  Equations typing_inf : typing_stmt inf_state :=
  | (Γ;_;t) with t := {
    | tRel n with (ctx_access Γ n) :=
        {
          | error _ := raise (variable_not_in_context n Γ) ;
          | ok d := ret (ok d)
        } ;
    | tSort s := raise type_error ;
    | tProd A B :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | tSort sA =>
            rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
            match rB with
            | tSort sB => ret (tSort (sort_of_product sA sB))
            | _ => raise (M:=M0) type_error
            end
        | _ => raise (M:=M0) type_error
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
      | _ => raise (M:=M0) type_error
      end ;
    | tNat := ret U ;
    | tZero := ret tNat ;
    | tSucc u :=
        ru ← rec (inf_red_state;Γ;tt;u) ;;
        match ru with
        | tNat => ret tNat
        | _ => raise (M:=M0) type_error
        end ;
    | tNatElim P hz hs n :=
      rn ← rec (inf_red_state;Γ;tt;n) ;;
      match rn with
      | tNat =>
          rec (wf_ty_state;(Γ,,tNat);tt;P) ;;
          rec (check_state;Γ;P[tZero..];hz) ;;
          rec (check_state;Γ;elimSuccHypTy P;hs) ;;
          ret P[n..]
      | _ => raise (M:=M0) type_error
      end ;
    | tEmpty := ret U ;
    | tEmptyElim P e :=
        re ← rec (inf_red_state;Γ;tt;e) ;;
        match re with
        | tEmpty =>
            rec (wf_ty_state;(Γ,,tEmpty);tt;P) ;;
            ret P[e..]
        | _ => raise (M:=M0) type_error
        end ;
    | tSig A B :=
      rA ← rec (inf_red_state;Γ;tt;A) ;;
      match rA with
      | tSort sA =>
          rB ← rec (inf_red_state;Γ,,A;tt;B) ;;
          match rB with
          | tSort sB => ret (tSort (sort_of_product sA sB)) (* Should that be taken as a parameter for sigma as well ? *)
          | _ => raise (M:=M0) type_error
          end
      | _ => raise (M:=M0) type_error
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
      | _ => raise (M:=M0) type_error
      end ;
    | tSnd u :=
      rt ← rec (inf_red_state; Γ; tt; u) ;;
      match rt with
      | tSig A B => ret (B[(tFst u)..])
      | _ => raise (M:=M0) type_error
      end ;
    | tList A :=
      rA ← rec (inf_red_state;Γ;tt;A) ;;
      match rA with
      | tSort s => ret (tSort s)
      | _ => raise (M:=M0) type_error
      end
    | tNil A :=
      rec (wf_ty_state;Γ;tt;A) ;;
      ret (tList A)
    | tCons A hd tl :=
      rec (wf_ty_state;Γ;tt;A) ;;
      rec (check_state;Γ;A;hd) ;;
      rec (check_state;Γ;tList A;tl) ;;
      ret (tList A)
    | tMap A B f l :=
      rec (wf_ty_state;Γ;tt;A) ;;
      rec (wf_ty_state;Γ;tt;B) ;;
      rec (check_state;Γ;arr A B;f) ;;
      rec (check_state;Γ;tList A;l) ;;
      ret (tList B)
    | tListElim A P hnil hcons l :=
      rec (wf_ty_state;Γ;tt;A) ;;
      rec (wf_ty_state;(Γ,,tList A);tt;P) ;;
      rec (check_state;Γ;tList A;l) ;;
      rec (check_state;Γ;P[(tNil A)..];hnil) ;;
      rec (check_state;Γ;elimConsHypTy A P;hcons) ;;
      ret (P[l..])
  }.

  Equations typing_inf_red : typing_stmt inf_red_state :=
  | (Γ;_;t) :=
    T ← rec (inf_state;Γ;_;t) ;;
    ecall wh_red_key T.

  Equations typing_check : typing_stmt check_state :=
  | (Γ;T;t) :=
    T' ← rec (inf_state;Γ;tt;t) ;;
    call (ϕ:=ϕ) conv_key (ty_state;Γ;tt;T';T).

  Equations typing : ∇[ϕ] x, typing_full_cod x :=
  | (wf_ty_state; Γ; inp; T) := typing_wf_ty (Γ;inp;T)
  | (inf_state; Γ; inp; t) := typing_inf (Γ;inp;t)
  | (inf_red_state; Γ; inp; t) := typing_inf_red (Γ;inp;t)
  | (check_state; Γ; inp; t) := typing_check (Γ;inp;t).

End Typing.



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
