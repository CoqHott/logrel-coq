(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context DirectedDirections DirectedContext DirectedDirectioning GenericTyping.

Set Primitive Projections.

Reserved Notation "[ |-( ) Γ ]" (at level 0, Γ at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ]" (at level 0, Γ, d, A at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t : A @( dA ) ]" (at level 0, Γ, dt, t, A, dA at level 50, only parsing).
Reserved Notation "[ Γ |-( d ) A ≅ B ]" (at level 0, Γ, d, A, B at level 50, only parsing).
Reserved Notation "[ Γ |-( dt ) t ≅ t' : A @( dA ) ]" (at level 0, Γ, dt, t, t', A, dA at level 50, only parsing).
(* Reserved Notation "[ Γ |-( dt ) t ⤳* u ∈ A @( dA ) ]" (at level 0, Γ, dt, t, u, A, dA at level 50). *)


(* I think these should be provable after the fundamental lemma for any
  typing judgement sound with respect to the declarative typing *)
Class GenericConsequences `{GP : GenericTypingProperties} := {
  wft_ty : forall {Γ A t}, [Γ |- t : A] -> [Γ |- A]
}.


Record WfDirectedCtx `{WfContext} (Θ: context) :=
  { wf_ctx: [ |- List.map ty Θ ]
  ; wf_ctx_dir: DirCtx (List.map ty Θ) (List.map dir Θ) (List.map ty_dir Θ)
  }.
Notation "[ |-( ) Θ ]" := (WfDirectedCtx Θ).

Record WfType `{WfType} (Θ: context) (d: direction) (A: term) :=
  { wft: [ List.map ty Θ |- A ]
  ; wft_ctx_dir: DirCtx (List.map ty Θ) (List.map dir Θ) (List.map ty_dir Θ)
  ; wft_dir: [ List.map dir Θ |- A ◃ d ]
  }.
Notation "[ Θ |-( d ) A ]" := (WfType Θ d A).

Record Typing `{Typing} (Θ: context) (dt: direction) (T: term) (dT: direction) (t: term) :=
  { wt: [ List.map ty Θ |- t : T ]
  ; wt_ctx_dir: DirCtx (List.map ty Θ) (List.map dir Θ) (List.map ty_dir Θ)
  ; wt_dir: [ List.map dir Θ |- t ◃ dt ]
  ; wt_ty_dir: [ List.map dir Θ |- T ◃ dT ]
  }.
Notation "[ Γ |-( dt ) t : T @( dT ) ]" := (Typing Γ dt T dT t).


Section DirectedTypingLemmas.

Context  `{GP:GenericTypingProperties}.
  (* `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!GenericTypingProperties ta _ _ _ _ _ _ _ _ _ _}. *)

Lemma wfCtxEmpty : [|-() εᵈ ].
Proof.
  constructor; cbn; [| constructor]; gen_typing.
Qed.

Lemma wfCtxCons {Θ d A dA} : [|-() Θ] -> [Θ |-(dA) A] -> [|-() Θ ,, d \ A @ dA].
Proof.
  intros [] []; split; [now eapply wfc_cons| now econstructor].
Qed.

Lemma wfCtxWfType {Θ d A} : [ Θ |-( d ) A ] ->  [ |-( ) Θ ].
Proof.
  intros []; econstructor; tea; now eapply wfc_wft.
Qed.

(* TODO: note that I prove rules using naming convention from DeclarativeTyping *)
Lemma wfTypeU {Θ d} : [ |-( ) Θ ] -> [ Θ |-( d ) U ].
Proof.
  intros [].
  constructor; tea.
  - now apply wft_U.
  - now apply dirU'.
Qed.


Lemma wfTypeProd {Γ d} {A B} :
  [ Γ |-( dir_op d ) A ] ->
  [Γ ,, Discr \ A @ dir_op d |-( d ) B ] ->
  [ Γ |-( d ) tProd A B ].
Proof.
  intros [] [].
  constructor; tea.
  - now apply wft_prod.
  - now apply dirProd'.
Qed.

Lemma wfTemWfType `{!GenericConsequences (GP:=GP)} {Θ T dT t dt} : [Θ |-(dt) t : T @(dT) ] -> [Θ |-(dT) T].
Proof.
  intros []; econstructor; tea. now eapply wft_ty.
Qed.

Lemma wfTypeUniv {Θ d dU} {A} :
  [ Θ |-( d ) A : U @( dU ) ] ->
  [ Θ |-( d ) A ].
Proof.
  intros [].
  constructor; tea.
  now apply wft_term.
Qed.

Corollary wfTypeUnivDiscr {Θ d} {A} :
  [ Θ |-( d ) A : U @( Discr ) ] ->
  [ Θ |-( d ) A ].
Proof.
  apply wfTypeUniv.
Qed.


Lemma in_ctx_erased {Θ n} decl :
  in_ctx Θ n decl -> in_ctx (tys Θ) n (ty decl).
Proof.
  induction 1; now constructor.
Qed.

Lemma in_ctx_nth_dir {Θ n} decl :
  in_ctx Θ n decl -> List.nth_error (list_map dir Θ) n = Some (dir decl).
Proof.
  induction 1; tea.
  reflexivity.
Qed.

Lemma in_ctx_nth_ty_dir {Θ n} decl :
  in_ctx Θ n decl -> List.nth_error (list_map ty_dir Θ) n = Some (ty_dir decl).
Proof.
  induction 1; tea.
  reflexivity.
Qed.

Lemma wfTermVar {Θ d'} {n d T dT} :
  [ |-( ) Θ ] ->
  in_ctx Θ n (d \ T @ dT) ->
  dir_leq d d' ->
  [ Θ |-( d' ) tRel n : T @( dT ) ].
Proof.
  intros [] inΘ leq.
  split; tea.
  - apply ty_var; tea.
    now apply (in_ctx_erased (d \ T @ dT)).
  - eapply dirVar'; tea.
    now apply (in_ctx_nth_dir (d \ T @ dT)).
  - eapply dir_ctx_nth_ty; tea.
    + now apply (in_ctx_erased (d \ T @ dT)).
    + now apply (in_ctx_nth_ty_dir (d \ T @ dT)).
Qed.

Lemma wfTermProd {Θ d dU} {A B} :
  [ Θ |-( dir_op d ) A : U @( dU ) ] ->
  [ Θ ,, Discr \ A @ dir_op d |-( d ) B : U @( dU ) ] ->
  [ Θ |-( d ) tProd A B : U @( dU ) ].
Proof.
  intros [] [].
  split; tea.
  - now apply ty_prod.
  - now apply dirProd'.
Qed.

Corollary wfTermProdDiscr {Θ d} {A B} :
  [ Θ |-( dir_op d ) A : U @( Discr ) ] ->
  [ Θ ,, Discr \ A @ dir_op d |-( d ) B : U @( Discr ) ] ->
  [ Θ |-( d ) tProd A B : U @( Discr ) ].
Proof. apply wfTermProd. Qed. 


Lemma wfTermLam {Θ d} {dT A B t} :
  [ Θ |-( dir_op dT ) A ] ->
  [ Θ ,, Discr \ A @ dir_op dT  |-( d ) t : B @( dT ) ] ->
  [ Θ |-( d ) tLambda A t : tProd A B @( dT ) ].
Proof.
  intros [] [].
  split; tea.
  - now apply ty_lam.
  - now apply dirLam'.
  - now apply dirProd'.
Qed.

Lemma wfTermApp {Θ d} {dT f a A B} :
  [ Θ |-( d ) f : tProd A B @( dT ) ] ->
  [ Θ |-( Discr ) a : A @( dir_op dT ) ] ->
  [ Θ |-( d ) tApp f a : B[a..] @( dT ) ].
Proof.
  intros [? ? ? wdProd] [].
  split; tea.
  - now eapply ty_app.
  - now apply dirApp'.
  - eapply dir_subst1; tea.
    inversion wdProd; subst.
    inversion X; subst.
    econstructor; tea.
    etransitivity; tea.
    now eapply MaxDirProp.upper_bound2.
Qed.


(** More derived typing lemmas *)

Lemma wfCtxCons' {Θ d A dA} : [|-() Θ] -> ([|-() Θ] -> [Θ |-(dA) A]) -> [|-() Θ ,, d \ A @ dA].
Proof.
  intros hΘ hA; exact (wfCtxCons hΘ (hA hΘ)).
Qed.

Lemma wfTypeProd' {Γ d} {A B} :
  [ Γ |-( dir_op d ) A ] ->
  ( [|-() Γ ,, Discr \ A @ dir_op d] -> 
    [ Γ |-( dir_op d ) A ] ->
    [Γ ,, Discr \ A @ dir_op d |-( d ) B ]) ->
  [ Γ |-( d ) tProd A B ].
Proof.
  intros hA hB.
  apply wfTypeProd; tea.
  apply hB; tea.
  apply wfCtxCons; tea.
  now eapply wfCtxWfType.
Qed.

Fixpoint shift_n {A} `{Ren1 (nat -> nat) A A} (t : A) n := match n with 0 => t | S m => (shift_n t m)⟨↑⟩ end.

Lemma wfTypeVar {Θ n d d' dU} :
  [ |-( ) Θ ] ->
  in_ctx Θ n (shift_n (d \ U @ dU) n) ->
  dir_leq d d' ->
  [ Θ |-( d' ) tRel n ].
Proof.
  assert (h : forall k, shift_n (d \ U @ dU) k = (d \ U @ dU)).
  by (intros k; induction k as [| ? ih]; cbn; rewrite ?ih; reflexivity).
  rewrite h.
  intros.
  eapply wfTypeUniv.
  now eapply wfTermVar.
Qed.

  
End DirectedTypingLemmas.

Module Examples.

  Module List.
  
  (* Context of parameters for list *)
  Definition ctx := εᵈ ,, Fun \ U @ Discr.
  (* Context of arguments for nil; 
    the parameters of list should form a prefix *)
  Definition nil_ctx := ctx.
  (* Not sure how we will represent inductive occurences
    of the inductive being defined so I abstract that 
    as an arbitrary function tList taking |ctx| arguments of type term
    and producing a term for now *)
  Definition cons_ctx (tList : term -> term) := ctx,, Discr \ tRel 0 @ Fun,, Discr \ tList (tRel 1) @ Fun.

  Section ListTyping.
  Context `{GenericConsequences}.

  Lemma ctxWfCtx : [|-() ctx ].
  Proof.
    eapply wfCtxCons'; [apply wfCtxEmpty |intros; now apply wfTypeU].
  Qed.

  Lemma nil_ctxWfCtx : [|-() nil_ctx ].
  Proof.
    apply ctxWfCtx.
  Qed.

  Lemma cons_ctxWfCtx 
    (tList : term -> term)
    (ih : forall Θ A, [Θ |-(Fun) A] -> [Θ |-(Fun) tList A]) :
    [|-() cons_ctx tList ].
  Proof.
    apply wfCtxCons'; [apply wfCtxCons'|]; intros.
    - apply ctxWfCtx.
    - eapply wfTypeVar; tea; [econstructor| reflexivity].
    - eapply ih.
      eapply wfTypeVar; tea.
      2: reflexivity.
      do 2 econstructor.
  Qed.

  End ListTyping.
  End List.


  Module W.

    Definition ctx := εᵈ ,, Fun \ U @ Discr ,, Cofun \ tProd (tRel 0) U @ Cofun.
    
    Definition sup_ctx (tW : term -> term -> term) :=
      ctx ,, Discr \ tRel 1 @ Fun ,, Discr \ tProd (tApp (tRel 1) (tRel 0)) (tW (tRel 3) (tRel 2)) @ Cofun.
    
    Section WTyping.
    Context `{GenericConsequences}.

    Lemma ctxWfCtx : [|-() ctx ].
    Proof.
      eapply wfCtxCons'; [eapply wfCtxCons'|]; try apply wfCtxEmpty; intros.
      - now apply wfTypeU.
      - apply wfTypeProd'.
        + eapply wfTypeVar; tea; [econstructor| reflexivity].
        + intros; now eapply wfTypeU.
    Qed.

    End WTyping.
  End W.  
  
End Examples.


