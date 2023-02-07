From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction.
From LogRel.LogicalRelation Require Import Induction Irrelevance.

Set Universe Polymorphism.

Ltac bsimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress setoid_rewrite wk_to_ren_id
                 | progress setoid_rewrite wk_compose_compose
                 | progress setoid_rewrite id_ren
                 | progress unfold up_term_term, upRen_term_term, up_ren, wk_well_wk_compose, wk_id, wk_step, wk_up, wk_empty (**, _wk_up, _wk_step *)
                 | progress cbn[subst_term ren_term wk wk_to_ren]
                 | progress fsimpl ]).

Ltac bsimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  RenWk_term, RenWk_subst, RenWlWk_term, RenWlWk_subst
                  in *; bsimpl'; minimize.

Ltac irrelevance0 :=
  lazymatch goal with
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevant'
  | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevant'
  | [|- [_ | _ ||- _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevant'
  end.
  
Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].


Section Weakenings.
  Context `{GenericTypingProperties}.


  Lemma wkΠ  {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A])
    (ihdom : forall Δ' (ρ' : Δ' ≤ Δ), [ |- Δ'] -> [Δ' ||-< l > ⟨ρ'⟩ (⟨ρ⟩ (PiRedTyPack.dom ΠA))])
    (ihcod : forall (a : term), [PiRedTyPack.domRed ΠA ρ wfΔ | _ ||- a : _] ->
      forall Δ' (ρ' : Δ' ≤ Δ), [ |- Δ'] ->
      [Δ' ||-< l > ⟨ρ'⟩ (PiRedTyPack.cod ΠA)[a .: ρ >> tRel]]) :
    [Δ ||-Π< l > ⟨ρ⟩ A].
  Proof.
    destruct ΠA as[na dom cod];  cbn -[RenWlWk_term] in *.
    assert (domRed' : forall Δ' (ρ' : Δ' ≤ Δ), [|- Δ'] -> [Δ' ||-< l > ⟨ρ'⟩ (⟨ρ⟩ dom)]).
    {
      intros ? ρ' ?; replace (⟨ _ ⟩ _) with (⟨ρ' ∘w ρ⟩ dom) by now bsimpl.
      econstructor; now unshelve eapply domRed.
    }
    set (cod' := ⟨wk_up na dom ρ⟩cod).
    assert (codRed' : forall Δ' a (ρ' : Δ' ≤ Δ) (h : [|- Δ']),
      [domRed' Δ' ρ' h | _ ||- a : _] -> [Δ' ||-< l > cod'[a .: ρ' >> tRel]]).
    {
      intros ? a ρ' ?.
      replace (cod'[a .: ρ' >> tRel]) with (cod[ a .: (ρ' ∘w ρ) >> tRel]) by (unfold cod'; now bsimpl).
      econstructor; unshelve eapply codRed; [assumption|].
      irrelevance.
    }
    exists na (dom ⟨ρ⟩) cod' domRed' codRed'.
    + unfold cod'; change (tProd ?na _ _) with ((tProd na dom cod)⟨ρ⟩);  gen_typing.
    + gen_typing.
    + unfold cod'; set (ρ1 := wk_up na (dom) ρ); eapply wft_wk; gen_typing.
    + unfold cod'; change (tProd ?na _ _) with ((tProd na dom cod)⟨ρ⟩);  gen_typing.
    + intros Δ' a b ρ' wfΔ' ???. 
      replace (cod'[b .: ρ' >> tRel]) with (cod[ b .: (ρ' ∘w ρ) >> tRel]) by (unfold cod'; now bsimpl).
      subst cod'; unshelve epose (codExt Δ' a b (ρ' ∘w ρ) wfΔ' _ _ _); irrelevance.
  Defined.


  Lemma wk {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    [Γ ||-<l> A] -> [Δ ||-<l> A⟨ρ⟩].
  Proof.
    intros lrA. revert Δ ρ wfΔ . pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros **. cbn. apply LRU_. now econstructor.
    - intros ???[ty]???. apply LRne_. 
      exists (⟨ρ⟩ ty); [|now apply whne_ren|change U with U⟨ρ⟩] ;gen_typing.
    - intros ??? ? ihdom ihcod ???. apply LRPi'; eapply (wkΠ ρ wfΔ ΠA).
      + intros; apply ihdom; assumption.
      + intros; eapply ihcod; eassumption.
  Defined.

  Lemma wkΠ_eq {Γ Δ A l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A]) :
    let ihdom Δ' (ρ' : Δ' ≤ Δ) (h : [ |- Δ']) := wk ρ' h (PiRedTyPack.domRed ΠA ρ wfΔ) in
    let ihcod a (ha : [PiRedTyPack.domRed ΠA ρ wfΔ | _ ||- a : _]) Δ' (ρ' : Δ' ≤ Δ) (h : [ |- Δ']) :=
      wk ρ' h (PiRedTyPack.codRed ΠA ρ wfΔ ha) 
    in
    wk ρ wfΔ (LRPi' l ΠA) = LRPi' l (wkΠ ρ wfΔ ΠA ihdom ihcod).
  Proof. reflexivity. Qed.

  Set Printing Primitive Projection Parameters.

  Lemma wkEq {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (lrA : [Γ ||-<l> A]) : 
    [Γ ||-<l> A ≅ B | lrA] -> [Δ ||-<l> A⟨ρ⟩ ≅ B⟨ρ⟩ | wk ρ wfΔ lrA].
  Proof.
    revert B Δ ρ wfΔ. pattern l, Γ, A, lrA.
    eapply LR_rect_TyUr; clear l Γ A lrA.
    - intros ? ????? [->]; now constructor.
    - intros * [ty]. exists ty⟨ρ⟩.
      1,2: gen_typing. 
      cbn -[RenWlWk_term]; change U with U⟨ρ⟩; eapply convneu_wk; assumption.
    - intros * ihdom ihcod * [na dom cod]. rewrite wkΠ_eq. set (X := wkΠ _ _ _ _ _).
      exists na (dom⟨ρ⟩) (cod⟨wk_up na dom ρ⟩). cbn -[RenWlWk_term] in *.
      + abstract (change (tProd ?na _ _) with ((tProd na dom cod)⟨ρ⟩);  gen_typing).
      + change (tProd na _ _) with ((tProd na dom cod)⟨ρ⟩).
        replace (tProd _ _ _) with ((PiRedTyPack.prod _ ΠA)⟨ρ⟩) by now bsimpl.
        eapply convty_wk; assumption.
      + intros. unshelve eapply LRTyEqIrrelevant.
        3: unshelve eapply ihdom; try eassumption; eapply domRed.
      + intros ? a ρ' ??.
        replace (_[_ .: ρ' >> tRel]) with (cod[ a .: (ρ' ∘w ρ) >> tRel]) by now bsimpl.
        irrelevance0.
        2: unshelve eapply codRed; [eassumption|]; subst X; irrelevance.
        subst X; bsimpl; rewrite scons_comp'; reflexivity.
  Qed.

End Weakenings.
