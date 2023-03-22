(** * LogRel.Decidability: type-checker implementation. *)
From PartialFun Require Import PartialFun.
From Coq Require Import Nat Lia.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.

Inductive stack :=
| sApp (u : term) (π : stack)
| sNil.

Fixpoint zip t π :=
  match π with
  | sApp u π => zip (tApp t u) π
  | sNil => t
  end.

Notation "( x , y )" := (pair x y).

Equations wh_red_stack : term × stack ⇀ term :=
  wh_red_stack (tLambda _ _ t, sApp u π) :=
    v ← rec (t[u..], π) ;;
    ret v ;
  wh_red_stack (tLambda na A t, sNil) :=
    ret (tLambda na A t) ;
  wh_red_stack (tApp t u, π) :=
    v ← rec (t, sApp u π) ;;
    ret v ;
  wh_red_stack (t, sNil) := ret t ;
  wh_red_stack (t, sApp _ _) := undefined.  (** The stack does not correspond to the term! *)

Equations wh_red : term ⇀ term :=
  wh_red t := t' ← call wh_red_stack (t,sNil) ;; ret t'.

Definition wh_red_fuel n t := fueled wh_red n t.

Compute (wh_red_fuel 10 (tApp (tLambda anDummy U (tRel 0)) U)).

Variant conv_state : Set :=
  | init_state (** Conversion of arbitrary terms *)
  | nf_state (** Weak-head normal forms comparison *)
  | ne_state (** Neutral comparison *)
  | ne_red_state. (** Neutral comparison, with a reduced type *)

Definition state_input (c : conv_state) : Set :=
  match c with
  | init_state | nf_state => term
  | ne_state | ne_red_state => unit
  end.

Definition state_output (c : conv_state) : Set :=
  match c with
  | init_state | nf_state => unit
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
  | nf_view1_ne n : nf_view1 n.

Definition nf_view1_build t : nf_view1 t :=
  match t with
  | tRel _| tApp _ _ => nf_view1_ne t
  | tSort _| tProd _ _ _ => nf_view1_type t
  | tLambda _ _ _ => nf_view1_fun t
  end.

Inductive nf_view3 : term -> term -> term -> Set :=
| sorts (s s1 s2 : sort) : nf_view3 (tSort s) (tSort s1) (tSort s2)
| prods (s : sort) (na na' : aname) (A A' B B' : term) :
    nf_view3 (tSort s) (tProd na A B) (tProd na' A' B')
| functions na A B t t' : nf_view3 (tProd na A B) t t'
| neutrals (A n n' : term) : nf_view3 A n n'
| mismatch (A t u : term) : nf_view3 A t u
| anomaly (A t u : term) : nf_view3 A t u.

Equations nf_case T t t' : nf_view3 T t t' :=
  nf_case T t t' with (nf_view1_build T), (nf_view1_build t), (nf_view1_build t') := {
  | nf_view1_type (tSort s), nf_view1_type (tSort s1), nf_view1_type (tSort s2) :=
      sorts s s1 s2 ;
  | nf_view1_type (tSort s), nf_view1_type (tProd na A B), nf_view1_type (tProd na' A' B') :=
      prods s na na' A A' B B' ;
  | nf_view1_type (tSort _), nf_view1_ne _, nf_view1_ne _ :=
    neutrals _ _ _ ;
  | nf_view1_type (tSort _), nf_view1_type (tSort _), nf_view1_type (tProd _ _ _) :=
      mismatch _ _ _ ;
  | nf_view1_type (tSort _), nf_view1_type (tProd _ _ _), nf_view1_type (tSort _) :=
      mismatch _ _ _ ;
  | nf_view1_type (tSort _), nf_view1_ne _, nf_view1_type _ :=
      mismatch _ _ _ ;
  | nf_view1_type (tSort _), nf_view1_type _, nf_view1_ne _ :=
      mismatch _ _ _ ;
  | nf_view1_type (tProd na A B), _, _ :=
      functions na A B _ _ ;
  | nf_view1_ne _, nf_view1_ne _, nf_view1_ne _ :=
      neutrals _ _ _ ;
  | _, _, _ := anomaly _ _ _
  }.

Equations conv :
  ∇ (x : ∑ (c : conv_state) (_ : context) (_ : state_input c) (_ : term), term),
  option (state_output (x.π1)) :=
  conv (init_state;Γ;A;t;u) :=
    A' ← call wh_red A ;;
    t' ← call wh_red t ;;
    u' ← call wh_red u ;;
    b ← rec (nf_state;Γ;A';t';u') ;;
    ret (b : option unit) ; (* weird: using b without annotation fails? *)
  conv (nf_state;Γ;A;t;u) with (nf_case A t u) :=
  {
    | sorts s s1 s2 with (eq_sort s1 s2) :=
      {
        | false => ret None
        | true => ret (Some tt)
      }
    | prods s na na' A A' B B' with (eq_binder_annot na na') :=
      {
        | false => ret None
        | true => b ← rec (init_state;Γ;tSort s;A;A') ;;
            match b with
            | None => ret None
            | Some _ => b' ← rec (init_state;Γ,,vass na A;tSort s;B;B') ;;
                ret b'
            end
      }
    | functions na A B _ _ :=
        b ← rec (init_state;Γ,,vass na A;B;eta_expand t;eta_expand u) ;;
        ret b
    | neutrals _ _ _ := b ← rec (ne_state;Γ;tt;t;u) ;;
        match b with
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
    | (Some (tProd na A B)) => b ← rec (init_state;Γ;A;t;t') ;;
      match b with
      | None => ret None
      | Some _ => ret (Some (B[t..] : term))
      end
    | (Some _) => undefined (** the whnf of the type of an applied neutral must be a Π type!*)
    end ;
  conv (ne_state;Γ;_;tRel _;tApp _ _) :=
    ret None ; (** the neutrals don't match*)
  conv (ne_state;Γ;_;tApp _ _;tRel _) :=
    ret None ; (** the neutrals don't match *)
  conv (ne_state;_) := undefined ; (** we are not comparing neutrals!*)
  conv (ne_red_state;Γ;_;t;u) :=
    Ainf ← rec (ne_state;Γ;tt;t;u) ;;
    match Ainf with
    | None => ret None
    | Some Ainf' => A' ← call wh_red Ainf' ;; ret (Some (A' : term))
      (* same, why do we need an annotation here? Coq seems to be lost by pattern-matching*)
    end.