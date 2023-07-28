(** * LogRel.Introductions.Var : Validity of variables. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Irrelevance Reflexivity Transitivity Universe Weakening Neutral Induction NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties Conversion Reflexivity SingleSubst Escape.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Var.
  Context `{GenericTypingProperties}.
  
  Lemma var0Valid {Γ l A} (VΓ : [||-v Γ]) (VA : [Γ ||-v<l> A | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | validSnoc VΓ VA | wk1ValidTy _ VA ].
  Proof.
    constructor; intros; cbn.
    + epose (validHead Vσ); irrelevance.
    + epose (eqHead Vσσ'); irrelevance.
  Qed.
  
  Lemma var0Valid' {Γ l A} (VΓ : [||-v Γ,,A]) (VA : [Γ,,A ||-v<l> A⟨↑⟩ | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | VΓ | VA ].
  Proof.
    pose proof (invValiditySnoc VΓ) as [? [? [? ]]]; subst.
    constructor; intros; cbn.
    + epose (validHead Vσ); irrelevance.
    + epose (eqHead Vσσ'); irrelevance.
  Qed.

  Lemma in_ctx_valid {n} :  forall {Γ A} (VΓ : [||-v Γ]), in_ctx Γ n A -> ∑ l, [Γ ||-v<l> A | VΓ].
  Proof.
    induction n.
    - intros ??? h; inversion h; subst.
      pose proof (invValiditySnoc VΓ) as [? [? [? ]]]; subst.
      eexists.
      erewrite <- wk1_ren_on.
      now eapply wk1ValidTy.
    - intros ??? h; inversion h; subst.
      pose proof (invValiditySnoc VΓ) as [? [? [? ]]]; subst.
      eapply IHn in H13 as [l ?].
      exists l. erewrite <- wk1_ren_on.
      now eapply wk1ValidTy.
  Qed.

  Lemma varnValid {n} :  forall {Γ l A} (VΓ : [||-v Γ]) (h : in_ctx Γ n A) (VA : [Γ ||-v<l> A | VΓ]),
    [Γ ||-v<l> tRel n : _ | VΓ | VA ].
  Proof.
    induction n.
    - intros ???? h ?; inversion h; subst.
      eapply var0Valid'.
    - intros * h ?; inversion h; subst.
      pose proof (invValiditySnoc VΓ) as [? [VΓ0 [? ]]]; subst.
      destruct (in_ctx_valid VΓ0 H13).
      pose proof (h' := H13); eapply IHn, wk1ValidTm in h'; rewrite wk1_ren_on in h'.
      eapply irrelevanceTm'; tea.
      now rewrite wk1_ren_on.
      Unshelve. 1,4: tea.
  Qed.
  
  Lemma var1Valid {Γ l A B} (VΓ : [||-v (Γ,, A) ,, B]) (VA : [_ ||-v<l> A⟨↑⟩⟨↑⟩ | VΓ]) :
    [(Γ,, A) ,, B ||-v<l> tRel 1 : _ | VΓ | VA ].
  Proof.
    eapply varnValid; do 2 constructor.
  Qed.
  
End Var.