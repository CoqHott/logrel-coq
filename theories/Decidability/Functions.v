(** * LogRel.Decidability.Functions: conversion and type-checker implementation. *)
From PartialFun Require Import PartialFun.
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context DeclarativeTyping.

Inductive stack :=
| sNatElim (P : term) (hs hz : term) (π : stack)
| sApp (u : term) (π : stack)
| sNil.

Fixpoint zip t π :=
  match π with
  | sNatElim P hs hz π => zip (tNatElim P hs hz t) π 
  | sApp u π => zip (tApp t u) π
  | sNil => t
  end.

Equations wh_red_stack : term × stack ⇀ term :=
  wh_red_stack (tRel n, π) := ret (zip (tRel n) π) ;
  wh_red_stack (tLambda _ _ t, sApp u π) :=
    v ← rec (t[u..], π) ;;
    ret v ;
  wh_red_stack (tApp t u, π) :=
    rec (t, sApp u π) ret ;
  wh_red_stack (tZero,sNatElim _ hz _ π) :=
    v ← rec (hz,π) ;;
    ret v ;
  wh_red_stack (tSucc t,sNatElim P hz hs π) :=
    v ← rec (hs,sApp t (sApp (tNatElim P hz hs t) π)) ;;
    ret v ;
  wh_red_stack (tNatElim P hz hs t, π) :=
    v ← rec (t,sNatElim P hz hs π) ;;
    ret v ;
  wh_red_stack (t,sNil) := ret t ; (** A normal form in the empty stack has finished computing *)
  wh_red_stack (t, sApp _ _) := undefined ; (** The stack does not correspond to the term! *)
  wh_red_stack (t, sNatElim _ _ _ _) := undefined. (** The stack does not correspond to the term! *)

Equations wh_red : term ⇀ term :=
  wh_red t := t' ← call wh_red_stack (t,sNil) ;; ret t'.

Definition wh_red_fuel n t := fueled wh_red n t.

(* Compute (deep_red_fuel 10 (tApp (tLambda anDummy U (tRel 0)) U)).
Compute (deep_red_fuel 1000 (tNatElim
  tNat
  tZero
  (tLambda anDummy tNat (tLambda anDummy tNat (tSucc (tSucc (tRel 0)))))
  (tSucc (tSucc tZero)))). *)

Variant conv_state : Set :=
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

Equations ctx_access : (context × nat) ⇀ context_decl :=
  ctx_access (ε , _ ) := undefined ; (** The context does not contain the variable! *)
  ctx_access (_,,d , 0 ) := ret (d⟨↑⟩) ;
  ctx_access ( Γ,,_ , S n') := d ← rec (Γ,n') ;; ret d⟨↑⟩.

Definition eq_sort (s s' : sort) : bool := true.

Inductive nf_view1 : term -> Set :=
  | nf_view1_type t : nf_view1 t
  | nf_view1_fun t : nf_view1 t
  | nf_view1_nat t : nf_view1 t
  | nf_view1_ne n : nf_view1 n.

Definition build_nf_view1 t : nf_view1 t :=
  match t with
  | tRel _| tApp _ _ | tNatElim _ _ _ _ => nf_view1_ne _
  | tSort _| tProd _ _ _ | tNat => nf_view1_type _
  | tLambda _ _ _ => nf_view1_fun _
  | tZero | tSucc _ => nf_view1_nat _
  end.

Inductive nf_ty_view : term -> Set :=
| nf_ty_view_sort s : nf_ty_view (tSort s)
| nf_ty_view_prod na A B : nf_ty_view (tProd na A B)
| nf_ty_view_nat : nf_ty_view tNat
| nf_ty_view_ne n : nf_ty_view n
| nf_ty_view_anomaly t : nf_ty_view t.

Definition build_nf_ty_view t : nf_ty_view t :=
  match t with
  | tSort s => nf_ty_view_sort _
  | tProd na A B => nf_ty_view_prod _ _ _
  | tNat => nf_ty_view_nat
  | tRel _ | tApp _ _ | tNatElim _ _ _ _ => nf_ty_view_ne _
  | tLambda _ _ _ | tZero | tSucc _ => nf_ty_view_anomaly _
  end.

Inductive nf_view3 : term -> term -> term -> Set :=
| sorts (s s1 s2 : sort) : nf_view3 (tSort s) (tSort s1) (tSort s2)
| prods (s : sort) (na na' : aname) (A A' B B' : term) :
    nf_view3 (tSort s) (tProd na A B) (tProd na' A' B')
| nats s : nf_view3 (tSort s) tNat tNat
| functions na A B t t' : nf_view3 (tProd na A B) t t'
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
  | nf_ty_view_sort s, nf_view1_type (tProd na A B), nf_view1_type (tProd na' A' B') :=
      prods s na na' A A' B B' ;
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
  | nf_ty_view_prod na A B, _, _ :=
      functions na A B _ _ ;
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
  (** Elements of a neutral type *)
  | nf_ty_view_ne _, nf_view1_ne _, nf_view1_ne _ :=
      neutrals _ _ _ ;
  (** Unreachable cases *)
  | _, _, _ := anomaly _ _ _
  }.

Equations conv :
  ∇ (x : ∑ (c : conv_state) (_ : context) (_ : cstate_input c) (_ : term), term),
  option (cstate_output (x.π1)) :=
  conv (ty_state;Γ;_;T;V) :=
    T' ← call wh_red T ;;
    V' ← call wh_red V ;;
    r ← rec (ty_red_state;Γ;tt;T';V') ;;
    ret (r : option unit) ;
  conv (ty_red_state;Γ;_;T;T') with (build_nf_ty_view T), (build_nf_ty_view T') :=
  {
    | nf_ty_view_sort s, nf_ty_view_sort s' := if (eq_sort s s') then ret (Some tt) else ret None ;
    | (nf_ty_view_prod na A B), (nf_ty_view_prod na' A' B') with (eq_binder_annot na na') :=
    {
      | false := ret None
      | true :=
          r ← rec (ty_state;Γ;tt;A;A') ;;
          match r with
          | None => ret None
          | Some _ => r' ← rec (ty_state;(Γ,,vass na A);tt;B;B') ;; ret (r' : option unit)
          end
    }
    | nf_ty_view_nat, nf_ty_view_nat := ret (Some tt) ;
    | nf_ty_view_ne _, nf_ty_view_ne _ :=
        r ← rec (ne_state;Γ;tt;T;T') ;; ret (if (r : option term) then Some tt else None);
    | nf_ty_view_anomaly _, _ := undefined ;
    | _, nf_ty_view_anomaly _ := undefined ;
    | _, _ := ret None ; (** Heads do not match *)
  } ;
  conv (tm_state;Γ;A;t;u) :=
    A' ← call wh_red A ;;
    t' ← call wh_red t ;;
    u' ← call wh_red u ;;
    r ← rec (tm_red_state;Γ;A';t';u') ;;
    ret (r : option unit) ; (* weird: using b without annotation fails? *)
  conv (tm_red_state;Γ;A;t;u) with (nf_case A t u) :=
  {
    | sorts s s1 s2 with (eq_sort s1 s2) :=
      {
        | false => ret None
        | true => ret (Some tt)
      }
    | prods s na na' A A' B B' with (eq_binder_annot na na') :=
      {
        | false := ret None
        | true := r ← rec (tm_state;Γ;tSort s;A;A') ;;
            match r with
            | None => ret None
            | Some _ => r' ← rec (tm_state;Γ,,vass na A;tSort s;B;B') ;;
                ret r'
            end
      }
    | nats s := ret (Some tt) ;
    | functions na A B _ _ :=
        rec (tm_state;Γ,,vass na A;B;eta_expand t;eta_expand u) ret ;
    | zeros := ret (Some tt) ;
    | succs t' u' :=
        rec (tm_state;Γ;tNat;t';u') ret ;
    | neutrals _ _ _ := r ← rec (ne_state;Γ;tt;t;u) ;;
        match r with
        | Some _ => ret (Some tt)
        | None => ret None
        end ;
    | mismatch _ _ _ := ret None ;
    | anomaly _ _ _ := undefined ;
  } ;
  conv (ne_state;Γ;_;tRel n;tRel n')
    with n =? n' :=
    { | false => ret None
      | true => d ← call ctx_access (Γ,n) ;; ret (Some d.(decl_type))
    } ;
  conv (ne_state;Γ;_;tApp n t ; tApp n' t') :=
    T ← rec (ne_red_state;Γ;tt;n;n') ;;
    match T with
    | None => ret None
    | (Some (tProd na A B)) => r ← rec (tm_state;Γ;A;t;t') ;;
      match r with
      | None => ret None
      | Some _ => ret (Some (B[t..] : term))
      end
    | (Some _) => undefined (** the whnf of the type of an applied neutral must be a Π type!*)
    end ;
  conv (ne_state;Γ;_;tNatElim P hz hs n;tNatElim P' hz' hs' n') :=
    rP ← rec (ty_state;(Γ,,vass anDummy tNat);tt;P;P') ;;
    match rP with
    | None => ret None
    | Some _ =>
        rz ← rec (tm_state;Γ;P[tZero..];hz;hz') ;;
        rs ← rec (tm_state;Γ;elimSuccHypTy anDummy P;hs;hs') ;;
        rn ← rec (tm_state;Γ;tNat;n;n') ;;
        match rz, rs, rn with
        | Some _, Some _, Some _ => ret (Some P[n..])
        | _, _, _ => ret None
        end
    end ;
  conv (ne_state;_) := ret None ;
  conv (ne_red_state;Γ;_;t;u) :=
    Ainf ← rec (ne_state;Γ;tt;t;u) ;;
    match Ainf with
    | None => ret None
    | Some Ainf' => A' ← call wh_red Ainf' ;; ret (Some (A' : term))
      (* same, why do we need an annotation here? Coq seems to be lost by pattern-matching*)
    end.

Variant typing_state : Set :=
  | inf_state (** inference *)
  | check_state (** checking *)
  | inf_red_state (** inference of a type reduced to whnf *)
  | wf_ty_state. (** checking well-formation of a type *)

Definition tstate_input (s : typing_state) : Set :=
  match s with
  | inf_state | inf_red_state | wf_ty_state => unit
  | check_state => term
  end.

Definition tstate_output (s : typing_state) : Set :=
  match s with
  | inf_state | inf_red_state => term
  | wf_ty_state | check_state => unit
  end.

Equations typing : ∇ (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term),
  option (tstate_output (x.π1)) :=
  typing (wf_ty_state;Γ;_;T) with (build_nf_ty_view T) :=
  {
    | nf_ty_view_sort s := ret (Some tt) ;
    | nf_ty_view_prod na A B :=
        rA ← rec (wf_ty_state;Γ;tt;A) ;;
        match rA with
        | Some _ =>
            rB ← rec (wf_ty_state;Γ,,vass na A;tt;B) ;;
            ret rB
        | _ => ret None
        end ;
    | nf_ty_view_nat := ret (Some tt) ;
    | nf_ty_view_ne _ :=
        r ← rec (inf_red_state;Γ;tt;T) ;;
        match r with
        | Some (tSort _) => ret (Some tt)
        | _ => ret None
        end
    | nf_ty_view_anomaly _ := ret None
  } ;
  typing (inf_state;Γ;_;t) with t :=
  {
    | tRel n := r ← call ctx_access (Γ,n) ;; ret (Some (r.(decl_type))) ;
    | tSort s := ret None ;
    | tProd na A B :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | Some (tSort sA) =>
            rB ← rec (inf_red_state;Γ,,vass na A;tt;B) ;;
            match rB with
            | Some (tSort sB) => ret (Some (tSort (sort_of_product sA sB)))
            | _ => ret None
            end
        | _ => ret None
        end ;
    | tLambda na A u :=
        rA ← rec (inf_red_state;Γ;tt;A) ;;
        match rA with
        | Some (tSort sA) =>
            ru ← rec (inf_state;Γ,,vass na A;tt;u) ;;
            match ru with
            | Some B => ret (Some (tProd na A B))
            | _ => ret None
            end
        | _ => ret None
        end ;
    | tApp f u :=
      rf ← rec (inf_red_state;Γ;tt;f) ;;
      match rf with
      | Some (tProd na A B) =>
          ru ← rec (check_state;Γ;A;u) ;;
          if (ru : option unit) then (ret (Some B[u..])) else (ret None)
      | _ => ret None
      end ;
    | tNat := ret (Some U) ;
    | tZero := ret (Some tNat) ;
    | tSucc u :=
        ru ← rec (inf_red_state;Γ;tt;u) ;;
        match ru with
        | Some tNat => ret (Some tNat)
        | _ => ret None
        end ;
    | tNatElim P hz hs n :=
      rP ← rec (wf_ty_state;(Γ,,vass anDummy tNat);tt;P) ;;
      match rP with
      | None => ret None
      | Some _ =>
          rz ← rec (check_state;Γ;P[tZero..];hz) ;;
          rs ← rec (check_state;Γ;elimSuccHypTy anDummy P;hs) ;;
          rn ← rec (check_state;Γ;tNat;n) ;;
          match rz, rs, rn with
          | Some _, Some _, Some _ => ret (Some P[n..])
          | _, _, _ => ret None
          end
      end ;
  } ;
  typing (inf_red_state;Γ;_;t) :=
    r ← rec (inf_state;Γ;_;t) ;;
    match r with
    | None => ret None
    | Some T => T' ← call wh_red T ;; ret (Some (T' : term))
    end ;
  typing (check_state;Γ;T;t) :=
    r ← rec (inf_state;Γ;tt;t) ;;
    match r with
    | None => ret None
    | Some T' => r' ← call conv (ty_state;Γ;tt;T';T) ;;
        ret (r' : option unit)
    end.

#[local] Definition infer (Γ : context) (t : term) : Fueled (option term) := 
  (fueled typing 1000 (inf_state;Γ;tt;t)).

#[local] Definition check_ty (Γ : context) (t : term) : Fueled (option unit) := 
  (fueled typing 1000 (wf_ty_state;Γ;tt;t)).

Compute (infer ε
  (tNatElim
    tNat
    tZero
  (tLambda anDummy tNat (tLambda anDummy tNat (tSucc (tSucc (tRel 0)))))
  (tSucc (tSucc tZero)))).

Compute (infer ε (tProd anDummy U (tRel 0))).
Compute (check_ty ε (tProd anDummy U (tRel 0))).

Compute (infer ε
  (tLambda anDummy tNat (tNatElim
    tNat
    tZero
  (tLambda anDummy tNat (tLambda anDummy tNat (tSucc (tSucc (tRel 0)))))
  (tRel 0)))).