From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped DeclarativeTyping.

Import DeclarativeTypingData.

Inductive termGenData Γ : term -> term -> Type :=
  | VarGen n decl :
      [|- Γ] -> in_ctx Γ n decl ->
      termGenData Γ (tRel n) decl.(decl_type)
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
      termGenData Γ (tApp f a) (B[a..]).

Lemma termGen Γ t A :
  [Γ |- t : A] ->
  ∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1.
  1-4: solve 
    [eexists ; split ; [now econstructor | left ; reflexivity]].
  destruct IHTypingDecl as [A' [? [-> | ]]].
  - eexists. split.
    1: eassumption.
    now right.
  - eexists. split.
    1: eassumption.
    right.
    now eapply TypeTrans.
Qed.

Lemma prod_ty_inv Γ na A B :
  [Γ |- tProd na A B] ->
  [Γ |- A] × [Γ,, vass na A |- B].
Proof.
  intros Hty.
  inversion Hty ; subst ; clear Hty.
  1: easy.
  eapply termGen in H as [? [Hgen]].
  inversion Hgen ; subst ; clear Hgen.
  split ; now econstructor.
Qed.

Inductive termRedGenData Γ : term -> term -> term -> Type :=
  | AppRedGen na A B t u a :
      [ Γ |- t ⇒ u : tProd na A B] ->
      [ Γ |- a : A ] ->
    termRedGenData Γ (tApp t a) (tApp u a) (B[a..])
  | BRedGen na A B a t :
      [ Γ |- A ] -> 
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- a : A ] ->
      termRedGenData Γ (tApp (tLambda na A t) a) (t[a..]) (B[a..]).

Lemma termRedGen Γ t u A :
  [Γ |- t ⇒ u : A] ->
  ∑ A', (termRedGenData Γ t u A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1. 
  1-2: solve 
    [eexists ; split ; [now econstructor | left ; reflexivity]].
  destruct IHOneRedTermDecl as [? [? [-> | ]]].
  all: eexists ; split ; [eassumption | right ].
  1: now eassumption.
  now eapply TypeTrans.
Qed.