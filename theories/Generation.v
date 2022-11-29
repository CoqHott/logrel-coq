From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
From LogRel Require Import Notations Untyped DeclarativeTyping Properties.

#[local] Open Scope untagged_scope.
Import DeclarativeTypingData.

Inductive termGenData Γ : term -> term -> Type :=
  | VarGen n decl :
      [|- Γ] -> nth_error Γ n = Some decl ->
      termGenData Γ (tRel n) (lift0 (S n) decl.(decl_type))
  | ProdGen na A B :
      [Γ |- A : U] ->
      [Γ,, vass na A |- B : U] ->
      termGenData Γ (tProd na A B) U
  | LamGen na A B t :
      [Γ |- A] ->
      [Γ,, vass na A |- t : B] ->
      termGenData Γ (tLambda na A t) (tProd na A B)
  | LamApp na f a A B :
      [Γ |- f : tProd na A B] ->
      [Γ |- a : A] ->
      termGenData Γ (tApp f a) (B{0 := a}).

Lemma termGen Γ t A :
  [Γ |- t : A] ->
  ∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1.
  1-4: solve 
    [eexists ; split ; [now econstructor | left ; reflexivity]].
  destruct IHX as [A' [? [-> | ]]].
  - eexists. split.
    1: eassumption.
    now right.
  - eexists. split.
    1: eassumption.
    right.
    now eapply TypeTrans.
Qed.  

Inductive termRedGenData Γ : term -> term -> term -> Type :=
  | AppRedGen na A B t u a :
      [ Γ |- t ⇒ u : tProd na A B] ->
      [ Γ |- a : A ] ->
    termRedGenData Γ (tApp t a) (tApp u a) (B{0 := a})
  | BRedGen na A B a t :
      [ Γ |- A ] -> 
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- a : A ] ->
      termRedGenData Γ (tApp (tLambda na A t) a) (t{0 := a}) (B{0 := a}).

Lemma termRedGen Γ t u A :
  [Γ |- t ⇒ u : A] ->
  ∑ A', (termRedGenData Γ t u A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1. 
  1-2: solve 
    [eexists ; split ; [now econstructor | left ; reflexivity]].
  destruct IHX as [? [? [-> | ]]].
  all: eexists ; split ; [eassumption | right ].
  1: now eassumption.
  now eapply TypeTrans.
Qed.

Fixpoint fragment (t : term) : bool :=
  match t with
    | tRel _ => true
    | tSort u => eqb Universe.type0 u
    | tProd _ A B => fragment A && fragment B
    | tLambda _ A t => fragment t && fragment A
    | tLetIn _ A t u => fragment u && fragment t && fragment A
    | tApp t u => fragment t && fragment u
    | _ => false
  end.

Lemma fragment_mkApps t l : fragment (mkApps t l) = fragment t && (forallb fragment l).
Proof.
  induction l as [|h l' IHt] using list_ind_rev; cbn.
  - now rewrite andb_true_r.
  - rewrite mkApps_app, forallb_app ; cbn.
    rewrite IHt, andb_true_r.
    now rewrite andb_assoc.
Qed.

Definition fragment_ctx (Γ : context) : bool :=
  forallb
    (fun d => if d.(decl_body) then false else fragment d.(decl_type))
    Γ.

Lemma fragment_lift k n t : fragment (lift k n t) = fragment t.
Proof.
  induction t in k, n |- * ; cbn.
  all:
  repeat match goal with
      | H : forall k n, _ = _ |- _ => rewrite H in * ; cbn in *
    end.
  all: reflexivity.
Qed.

Lemma fragment_subst k t u : fragment t -> fragment u -> fragment (t{k := u}).
Proof.
  unfold subst1.
  induction t in k |- * ; cbn.
  all:
    intros ; repeat match goal with
      | H : is_true (_ && _) |- _ => apply andb_andI in H as []
      | H : forall k, _ -> _ -> is_true _ |- _ => rewrite H in * ; cbn in *
    end ; auto.
  case (k <=? n).
  1: case (n-k) ; cbn ; [..| intros ? ; rewrite nth_error_nil].
  2-3: reflexivity.
  now rewrite fragment_lift.
Qed.

Lemma wfFrag :
  (forall Γ : context, [  |- Γ ] -> fragment_ctx Γ)
  × (forall (Γ : context) (t : term), [Γ |- t] -> fragment_ctx Γ && fragment t)
    × (forall (Γ : context) (t A : term), [Γ |- t : A] -> fragment t && fragment A && fragment_ctx Γ)
    × (forall (Γ : context) (A B : term), [Γ |- A ≅ B] -> fragment A && fragment B && fragment_ctx Γ)
        × (forall (Γ : context) (t u A : term),
          [Γ |- t ≅ u : A] -> fragment t && fragment u && fragment A && fragment_ctx Γ).
Proof.
  eapply WfDeclInduction ; cbn in * ; intros.
  2: fold (fragment_ctx Γ).
  all : intros ;
    repeat match goal with
      | H : is_true (_ && _) |- _ => apply andb_andI in H as []
      | H : is_true _ |- _ => rewrite H in * ; cbn -[fragment_ctx] in *
    end.
  all: try reflexivity.
  2-4: repeat rewrite fragment_subst ; eauto.
  rewrite fragment_lift.
  induction Γ in n, H, H0 |- *.
  - rewrite nth_error_nil in H0. congruence.
  - destruct n ; cbn in *.
    all: apply andb_andI in H as [].
    2: now eapply IHΓ.
    inversion H0 ; subst ; clear H0.
    destruct decl as [? []] ; cbn in *.
    1: congruence.
    now rewrite H.
Qed.

Corollary TypingFrag Γ t A : [Γ |- t : A] -> fragment t.
Proof.
  intros H.
  apply wfFrag in H.
  now repeat apply andb_andI in H as [H _].
Qed.