From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Universe Weakening.
From LogRel.Substitution Require Import Irrelevance Properties.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* FundCon, FundTy, ... are parameterized by a tag with a bunch of typing
  judgment predicates *)
Definition FundCon `{GenericTypingProperties}
  (Γ : context) : Type := [||-v Γ ].

Module FundTy.
  Record FundTy `{GenericTypingProperties} {Γ : context} {A : term}
  : Type := {
    vΓ : [||-v Γ ];
    vA : [ Γ ||-v< one > A | vΓ ]
  }.

  Arguments FundTy {_ _ _ _ _ _ _ _ _ _}.
End FundTy.

Export FundTy(FundTy,Build_FundTy).

Module FundTyEq.
  Record FundTyEq `{GenericTypingProperties}
    {Γ : context} {A B : term}
  : Type := {
    vΓ : [||-v Γ ];
    vA : [ Γ ||-v< one > A | vΓ ];
    vB : [ Γ ||-v< one > B | vΓ ];
    vAB : [ Γ ||-v< one > A ≅ B | vΓ | vA ]
  }.
  Arguments FundTyEq {_ _ _ _ _ _ _ _ _ _}.
End FundTyEq.

Export FundTyEq(FundTyEq,Build_FundTyEq).

Module FundTm.
  Record FundTm `{GenericTypingProperties}
    {Γ : context} {A t : term}
  : Type := {
    vΓ : [||-v Γ ];
    vA : [ Γ ||-v< one > A | vΓ ];
    vt : [ Γ ||-v< one > t : A | vΓ | vA ];
  }.
  Arguments FundTm {_ _ _ _ _ _ _ _ _ _}.
End FundTm.

Export FundTm(FundTm,Build_FundTm).

Module FundTmEq.
  Record FundTmEq `{GenericTypingProperties}
    {Γ : context} {A t u : term}
  : Type := {
    vΓ : [||-v Γ ];
    vA : [ Γ ||-v< one > A | vΓ ];
    vt : [ Γ ||-v< one > t : A | vΓ | vA ];
    vu : [ Γ ||-v< one > u : A | vΓ | vA ];
    vtu : [ Γ ||-v< one > t ≅ u : A | vΓ | vA ];
  }.
  Arguments FundTmEq {_ _ _ _ _ _ _ _ _ _}.
End FundTmEq.

Export FundTmEq(FundTmEq,Build_FundTmEq).

Module FundSubst.
  Record FundSubst `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
  }.
  Arguments FundSubst {_ _ _ _ _ _ _ _ _ _}.
End FundSubst.

Export FundSubst(FundSubst,Build_FundSubst).

Module FundSubstConv.
  Record FundSubstConv `{GenericTypingProperties}
    {Γ Δ : context} {wfΓ : [|- Γ]} {σ σ' : nat -> term}
  : Type := {
    VΔ : [||-v Δ ] ;
    Vσ : [VΔ | Γ ||-v σ : Δ | wfΓ] ;
    Vσ' : [VΔ | Γ ||-v σ' : Δ | wfΓ ] ;
    Veq : [VΔ | Γ ||-v σ ≅ σ' : Δ | wfΓ | Vσ] ;
  }.
  Arguments FundSubstConv {_ _ _ _ _ _ _ _ _ _}.
End FundSubstConv.

Export FundSubstConv(FundSubstConv,Build_FundSubstConv).

Section Fundamental.
  (* Fundamental is parameterized by a tag that satisfies the generic typing
    properties *)
  Context `{GenericTypingProperties}.

  Lemma TypeRedWf_refl {Γ} {A} : [ Γ |-[ ta ] A ] -> [ Γ |-[ ta ] A :⇒*: A ].
  Proof.
    intro h. econstructor.
    - assumption.
    - assumption.
    - now apply redty_refl.
  Defined.

  Lemma ughhh {a σ ρ} : (tRel 1)[a .: σ⟨ρ⟩] = (tRel 1)[up_term_term σ][a .: ρ >> tRel].
  Proof.
    asimpl. Fail reflexivity.
  Abort.

  Lemma FundPi {l Γ na F G} (vΓ : [||-v Γ])
    (vF : [Γ ||-v< l > F | vΓ])
    (vG : [Γ ,, vass na F ||-v< l > G | validSnoc na vΓ vF])
    : [Γ ||-v< l > tProd na F G | vΓ].
  Proof.
    pose proof (rF := fun Δ σ => validTy (Δ := Δ) (σ := σ) vF).
    pose proof (tF := fun Δ σ tΔ vσ => escape_ (rF Δ σ tΔ vσ)).
    pose proof (tFrefl := fun Δ σ tΔ vσ => escapeEq_ _ (LRTyEqRefl_ (rF Δ σ tΔ vσ))).
    pose proof (rG := fun Δ σ tΔ vσ => validTy (Δ := Δ ,, vass na F[σ])
                                         (σ := up_term_term σ) vG _ (liftSubstS' vΓ tΔ vF vσ)).
    pose proof (tG := fun Δ σ tΔ vσ => escape_ (rG Δ σ tΔ vσ)).
    pose proof (tGrefl := fun Δ σ tΔ vσ => escapeEq_ _ (LRTyEqRefl_ (rG Δ σ tΔ vσ))).
    pose proof (rGa := fun Δ Δ' σ a (tΔ : [ |-[ ta ] Δ ]) (tΔ' : [ |-[ ta ] Δ' ]) ρ vσ ra =>
                         validTy (Δ := Δ') (σ := a .: (σ ⟨ ρ ⟩)) vG _
                           (consSubstS vΓ tΔ' (wkSubstS vΓ tΔ tΔ' ρ vσ) vF ra)).
    unshelve econstructor.
    - intros Δ σ tΔ vσ. cbn.
      unshelve eapply LRPi_.
      + econstructor.
        * apply TypeRedWf_refl.
          exact (wft_prod (tF _ _ tΔ vσ) (tG _ _ tΔ vσ)).
        * exact (tF _ _ tΔ vσ).
        * exact (tG _ _ tΔ vσ).
        * exact (convty_prod I (tF _ _ tΔ vσ) (tFrefl _ _ tΔ vσ) (tGrefl _ _ tΔ vσ)).

          Unshelve.
          ++ intros Δ' ρ tΔ'.
             exact (wk ρ tΔ' (rF Δ σ tΔ vσ)).
          ++ intros Δ' a ρ tΔ' ra.
            admit.

        * intros Δ' a b ρ tΔ' ra rb rab.
          admit.

      + econstructor.
        * fold subst_term. admit.
        * admit.
    - intros Δ σ σ' tΔ vσ vσ' vσσ'. simpl. fold subst_term.
      econstructor.
      + apply TypeRedWf_refl.
        exact (wft_prod (tF _ _ tΔ vσ') (tG _ _ tΔ vσ')).
      + fold subst_term. simpl. admit.
      + fold subst_term. simpl. admit.
      + fold subst_term. simpl. admit.
  Admitted.

  Import DeclarativeTypingData.

  Lemma FundConNil : FundCon ε.
  Proof.
  unshelve econstructor.
  + unshelve econstructor.
    - intros; exact unit.
    - intros; exact unit.
  + constructor.
  Qed.

  Lemma FundConCons (Γ : context) (na : aname) (A : term)
  (tΓ : [ |-[ de ] Γ]) (fΓ : FundCon Γ) (tA : [Γ |-[ de ] A]) (fA : FundTy Γ A) : FundCon (Γ,, vass na A).
  Proof.
    destruct fA as [ vΓ vA ].
    eapply validSnoc. exact vA.
  Qed.

  Lemma FundTyU (Γ : context) (tΓ : [ |-[ de ] Γ]) (fΓ : FundCon Γ) : FundTy Γ U.
  Proof.
    unshelve econstructor.
    - assumption.
    - unshelve econstructor.
      + intros * _. apply LRU_. now econstructor.
      + intros * _ _. simpl. now econstructor.
  Qed.

  Lemma FundTyPi (Γ : context) (na : aname) (F G : term)
    (tF : [Γ |-[ de ] F]) (fF : FundTy Γ F)
    (tG : [Γ,, vass na F |-[ de ] G]) (fG : FundTy (Γ,, vass na F) G)
    : FundTy Γ (tProd na F G).
  Proof.
    destruct fF as [ vΓ vF ]. destruct fG as [ vΓF vG ].
    econstructor.
    unshelve eapply (FundPi vΓ).
    - assumption.
    - now eapply irrelevanceValidity.
  Qed.

  Lemma FundTyUniv (Γ : context) (A : term)
    (tA : [Γ |-[ de ] A : U]) (fA : FundTm Γ U A)
    : FundTy Γ A.
  Proof.
    destruct fA as [ vΓ vU [ rA rAext ] ]. econstructor.
    unshelve econstructor.
    - intros * vσ.
      eapply UnivEq. exact (rA _ _ wfΔ vσ).
    - intros * vσ' vσσ'.
      eapply UnivEqEq. exact (rAext _ _ _ wfΔ vσ vσ' vσσ').
  Qed.

  Lemma FundTmVar : forall (Γ : context) (n : nat) (decl : context_decl),
    [ |-[ de ] Γ] -> FundCon Γ ->
    in_ctx Γ n decl -> FundTm Γ (decl_type decl) (tRel n).
  Proof.
  Admitted.

  Lemma FundTmProd : forall (Γ : context) (na : aname) (A B : term),
    [Γ |-[ de ] A : U] -> FundTm Γ U A ->
    [Γ,, vass na A |-[ de ] B : U] ->
    FundTm (Γ,, vass na A) U B -> FundTm Γ U (tProd na A B).
  Proof.
  Admitted.

  Lemma FundTmLambda : forall (Γ : context) (na : aname) (A B t : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ,, vass na A |-[ de ] t : B] ->
    FundTm (Γ,, vass na A) B t -> FundTm Γ (tProd na A B) (tLambda na A t).
  Proof.
  Admitted.

  Lemma FundTmApp : forall (Γ : context) (na : aname) (f a A B : term),
    [Γ |-[ de ] f : tProd na A B] ->
    FundTm Γ (tProd na A B) f ->
    [Γ |-[ de ] a : A] -> FundTm Γ A a -> FundTm Γ B[a..] (tApp f a).
  Proof.
  Admitted.

  Lemma FundTmConv : forall (Γ : context) (t A B : term),
    [Γ |-[ de ] t : A] -> FundTm Γ A t ->
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTm Γ B t.
  Proof.
  Admitted.

  Lemma FundTyEqPiCong : forall (Γ : context) (na nb : aname) (A B C D : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ |-[ de ] A ≅ B] ->
    FundTyEq Γ A B ->
    [Γ,, vass na A |-[ de ] C ≅ D] ->
    FundTyEq (Γ,, vass na A) C D -> FundTyEq Γ (tProd na A C) (tProd nb B D).
  Proof.
  Admitted.

  Lemma FundTyEqRefl : forall (Γ : context) (A : term),
    [Γ |-[ de ] A] -> FundTy Γ A -> FundTyEq Γ A A.
  Proof.
  Admitted.

  Lemma FundTyEqSym : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B -> FundTyEq Γ B A.
  Proof.
  Admitted.

  Lemma FundTyEqTrans : forall (Γ : context) (A B C : term),
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B ->
    [Γ |-[ de ] B ≅ C] -> FundTyEq Γ B C ->
    FundTyEq Γ A C.
  Proof.
  Admitted.

  Lemma FundTyEqUniv : forall (Γ : context) (A B : term),
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B -> FundTyEq Γ A B.
  Proof.
  Admitted.

  Lemma FundTmEqBRed : forall (Γ : context) (na : aname) (a t A B : term),
    [Γ |-[ de ] A] ->
    FundTy Γ A ->
    [Γ,, vass na A |-[ de ] t : B] ->
    FundTm (Γ,, vass na A) B t ->
    [Γ |-[ de ] a : A] ->
    FundTm Γ A a -> FundTmEq Γ B[a..] (tApp (tLambda na A t) a) t[a..].
  Proof.
  Admitted.

  Lemma FundTmEqPiCong : forall (Γ : context) (na nb : aname) (A B C D : term),
    [Γ |-[ de ] A] -> FundTy Γ A ->
    [Γ |-[ de ] A ≅ B : U] -> FundTmEq Γ U A B ->
    [Γ,, vass na A |-[ de ] C ≅ D : U] -> FundTmEq (Γ,, vass na A) U C D ->
    FundTmEq Γ U (tProd na A C) (tProd nb B D).
  Proof.
  Admitted.

  Lemma FundTmEqAppCong : forall (Γ : context) (na : aname) (a b f g A B : term),
    [Γ |-[ de ] f ≅ g : tProd na A B] -> FundTmEq Γ (tProd na A B) f g ->
    [Γ |-[ de ] a ≅ b : A] -> FundTmEq Γ A a b ->
    FundTmEq Γ B[a..] (tApp f a) (tApp g b).
  Proof.
  Admitted.

  Lemma FundTmEqFunExt : forall (Γ : context) (na nb : aname) (f g A B : term),
    [Γ |-[ de ] A] -> FundTy Γ A ->
    [Γ |-[ de ] f : tProd na A B] -> FundTm Γ (tProd na A B) f ->
    [Γ |-[ de ] g : tProd nb A B] -> FundTm Γ (tProd nb A B) g ->
    [Γ,, vass na A |-[ de ] tApp (f⟨↑⟩) (tRel 0) ≅ tApp (g⟨↑⟩) (tRel 0) : B] -> FundTmEq (Γ,, vass na A) B (tApp (f⟨↑⟩) (tRel 0)) (tApp (g⟨↑⟩) (tRel 0)) ->
    FundTmEq Γ (tProd na A B) f g.
  Proof.
  Admitted.

  Lemma FundTmEqRefl : forall (Γ : context) (t A : term),
    [Γ |-[ de ] t : A] -> FundTm Γ A t ->
    FundTmEq Γ A t t.
  Proof.
  Admitted.

  Lemma FundTmEqSym : forall (Γ : context) (t t' A : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    FundTmEq Γ A t' t.
  Proof.
  Admitted.

  Lemma FundTmEqTrans : forall (Γ : context) (t t' t'' A : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    [Γ |-[ de ] t' ≅ t'' : A] -> FundTmEq Γ A t' t'' ->
    FundTmEq Γ A t t''.
  Proof.
  Admitted.

  Lemma FundTmEqConv : forall (Γ : context) (t t' A B : term),
    [Γ |-[ de ] t ≅ t' : A] -> FundTmEq Γ A t t' ->
    [Γ |-[ de ] A ≅ B] -> FundTyEq Γ A B ->
    FundTmEq Γ B t t'.
  Proof.
  Admitted.

Lemma Fundamental : (forall Γ : context, [ |-[ de ] Γ ] -> FundCon (ta := ta) Γ)
    × (forall (Γ : context) (A : term), [Γ |-[ de ] A] -> FundTy (ta := ta) Γ A)
    × (forall (Γ : context) (A t : term), [Γ |-[ de ] t : A] -> FundTm (ta := ta) Γ A t)
    × (forall (Γ : context) (A B : term), [Γ |-[ de ] A ≅ B] -> FundTyEq (ta := ta) Γ A B)
    × (forall (Γ : context) (A t u : term), [Γ |-[ de ] t ≅ u : A] -> FundTmEq (ta := ta) Γ A t u).
  Proof.
  apply WfDeclInduction.
  + apply FundConNil.
  + apply FundConCons.
  + apply FundTyU.
  + apply FundTyPi.
  + apply FundTyUniv.
  + apply FundTmVar.
  + apply FundTmProd.
  + apply FundTmLambda.
  + apply FundTmApp.
  + apply FundTmConv.
  + apply FundTyEqPiCong.
  + apply FundTyEqRefl.
  + apply FundTyEqUniv.
  + apply FundTyEqSym.
  + apply FundTyEqTrans.
  + apply FundTmEqBRed.
  + apply FundTmEqPiCong.
  + apply FundTmEqAppCong.
  + apply FundTmEqFunExt.
  + apply FundTmEqRefl.
  + apply FundTmEqConv.
  + apply FundTmEqSym.
  + apply FundTmEqTrans.
  Qed.

  Corollary wf_ctx_complete Γ :
    [|-[de] Γ] -> [|-[ta] Γ].
  Proof.
    induction 1 as [| ???? IH HA] ; refold.
    - apply wfc_nil.
    - apply wfc_cons ; tea.
      apply Fundamental in HA as [? [HA _]].
      pose proof (soundCtxId VΓ) as [? Hsubst].
      specialize (HA _ _ _ Hsubst).
      rewrite instId'_term in HA ; tea.
      now eapply escape_ in HA.
  Qed.

  Corollary Fundamental_subst Γ Δ σ (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ : Δ] ->
    FundSubst Γ Δ wfΓ σ.
  Proof.
    intros HΔ.
    induction 1 as [|σ Δ na A Hσ IH Hσ0].
    - exists validEmpty.
      now constructor.
    - inversion HΔ as [|??? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [redΓ [redA'] [redσ0]].
      cbn in *.
      clear validTyExt validTmExt.
      specialize (redσ0 _ _ _ (projT2 (soundCtxId redΓ))).
      set (redA'' := (redA' _ _ _ (projT2 (soundCtxId redΓ)))) in *.
      clearbody redA''.
      clear redA'.
      repeat rewrite instId'_term in *.
      eapply Fundamental in HA as [VΔ' VA].
      unshelve econstructor.
      1: now eapply validSnoc.
      unshelve econstructor.
      + now eapply irrelevanceSubst.
      + cbn.
        eapply RedTmIrrelevant.
        3: now eapply redσ0.
        * now unshelve eapply redA''.
        * rewrite instId'_term.
          unshelve eapply validTy.
  Qed.

  Corollary Fundamental_subst_conv Γ Δ σ σ' (wfΓ : [|-[ta] Γ ]) :
    [|-[de] Δ] ->
    [Γ |-[de]s σ ≅ σ' : Δ] ->
    FundSubstConv Γ Δ wfΓ σ σ'.
  Proof.
    intros HΔ.
    induction 1 as [|σ τ Δ na A Hσ IH Hσ0].
    - unshelve econstructor.
      1: eapply validEmpty.
      all: now econstructor.
    - inversion HΔ as [|??? HΔ' HA] ; subst ; clear HΔ ; refold.
      destruct IH ; tea.
      apply Fundamental in Hσ0 as [redΓ [redA'] [redσ0] [redτ0] [redστ0]] ; cbn in *.
      clear validTyExt validTmExt validTmExt0.
      specialize (redσ0 _ _ _ (projT2 (soundCtxId redΓ))).
      specialize (redτ0 _ _ _ (projT2 (soundCtxId redΓ))).
      specialize (redστ0 _ _ _ (projT2 (soundCtxId redΓ))).
      set (redA'' := (redA' _ _ _ (projT2 (soundCtxId redΓ)))) in *.
      clearbody redA''.
      clear redA'.
      repeat rewrite instId'_term in *.
      eapply Fundamental in HA as [VΔ' VA].
      unshelve econstructor.
      1: now eapply validSnoc.
      + unshelve econstructor.
        * now eapply irrelevanceSubst.
        * cbn.
          eapply RedTmIrrelevant.
          3: now eapply redσ0.
          -- now unshelve eapply redA''.
          -- rewrite instId'_term.
             now eapply validTy.
      + unshelve econstructor.
        * now eapply irrelevanceSubst.
        * cbn.
          eapply RedTmConv.
          4: now eapply redτ0.
          -- now unshelve eapply redA''.
          -- now eapply validTy.
          -- unshelve eapply LRTyEqIrrelevant'.
             4: rewrite instId'_term ; reflexivity.
             2,3: unshelve eapply VA ; tea.
             1-2: now eapply irrelevanceSubst.
             now eapply irrelevanceSubstEq.
      + unshelve econstructor ; cbn in *.
        * now eapply irrelevanceSubstEq.
        * eapply LRTmEqIrrelevant' ; tea.
          now bsimpl.
  Qed.

End Fundamental.
