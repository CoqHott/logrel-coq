From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms DeclarativeTyping.

Import DeclarativeTypingData.

Definition termGenData (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl.(decl_type), [|- Γ]& in_ctx Γ n decl]
    | tProd na A B =>  [× T = U, [Γ |- A : U] & [Γ,, vass na A |- B : U]]
    | tLambda na A t => ∑ B, [× T = tProd na A B, [Γ |- A] & [Γ,, vass na A |- t : B]]
    | tApp f a => ∑ na A B, [× T = B[a..], [Γ |- f : tProd na A B] & [Γ |- a : A]]
    | tSort _ => False
  end.

(* Inductive termGenData Γ : term -> term -> Type :=
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
      termGenData Γ (tApp f a) (B[a..]). *)

Ltac prod_splitter :=
  solve [now repeat match goal with
  | |- sigT _ => eexists
  | |- prod _ _ => split 
  | |- and3 _ _ _ => split
  | |- and4 _ _ _ _ => split
  end].

Lemma termGen Γ t A :
  [Γ |- t : A] ->
  ∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1.
  1-4: eexists ; split ; [..|left ; reflexivity] ; cbn ; prod_splitter.
  + destruct IHTypingDecl as [A' [? [-> | ]]].
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
  eapply termGen in H as (?&[-> ]&_).
  split ; now econstructor.
Qed.
