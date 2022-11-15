From MetaCoq.PCUIC Require Import PCUICAst PCUICRenameConv PCUICSigmaCalculus PCUICInstConv.
From LogRel Require Import Notations Automation Untyped MLTTTyping.

Inductive weakening : Set :=
  | wk_id : weakening
  | wk_step (w : weakening) : weakening
  | wk_lift (w : weakening) : weakening.

(* Transforms an (intentional) weakening into a renaming *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | wk_id => id
    | wk_step ρ' => S ∘ (wk_to_ren ρ')
    | wk_lift ρ' => shiftn 1 (wk_to_ren ρ')
  end.
Coercion wk_to_ren : weakening >-> Funclass.

Inductive well_weakening : weakening -> context -> context -> Type :=
  | well_id (Γ : context) : well_weakening wk_id Γ Γ
  | well_step (Γ Δ : context) (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (wk_step ρ) (Γ,,vass na A) Δ
  | well_lift (Γ Δ : context) (na : aname) (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (wk_lift ρ) (Γ,,vass na (A.[ren ρ])) (Δ,, vass na A).

Fixpoint wk_compose (ρ ρ' : weakening) : weakening :=
  match ρ, ρ' with
    | wk_id, _ => ρ'
    | wk_step ν , _ => wk_step (wk_compose ν ρ')
    | wk_lift ν, wk_id => ρ
    | wk_lift ν, wk_step ν' => wk_step (wk_compose ν ν')
    | wk_lift ν, wk_lift ν' => wk_lift (wk_compose ν ν')
  end.

Lemma wk_compose_compose (ρ ρ' : weakening) : (wk_compose ρ ρ' : nat -> nat) =1 ρ ∘ ρ'.
Proof.
  induction ρ in ρ' |- *.
  - reflexivity.
  - cbn.
    intros ?.
    now rewrite IHρ.
  - destruct ρ'.
    + reflexivity.
    + intros n.
      cbn.
      now rewrite IHρ, Nat.sub_0_r.
    + intros [] ; cbn.
      1: reflexivity.
      repeat rewrite Nat.sub_0_r.
      now rewrite IHρ.
Qed.

Lemma well_wk_compose {ρ ρ' : weakening} {Δ Δ' Δ'' : context} :
  well_weakening ρ Δ Δ' -> well_weakening ρ' Δ' Δ'' -> well_weakening (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - eassumption.
  - now econstructor.
  - inversion H' as [| | ? ? na' A' ν'] ; subst ; clear H'.
    1-2: now econstructor.
    rewrite inst_assoc.
    replace (A'.[ren ν' ∘s ren ν]) with (A'.[ren (wk_compose ν ν')]) by
      now rewrite compose_ren, wk_compose_compose.
    now econstructor.
Qed.

#[projections(primitive)]Record wk_well_wk {Γ Δ : context} :=
  { wk :> weakening ; well_wk :> well_weakening wk Γ Δ}.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).

#[global] Hint Resolve well_wk : core.

Definition wk_well_wk_compose {Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' :=
  {| wk := wk_compose ρ.(wk) ρ'.(wk) ; well_wk := well_wk_compose ρ.(well_wk) ρ'.(well_wk) |}.
Notation "ρ ∘w ρ'" := (wk_well_wk_compose ρ ρ').


Lemma well_length {Γ Δ : context} (ρ : Γ ≤ Δ) : #|Δ| <= #|Γ|.
Proof.
  destruct ρ as [ρ wellρ].
  induction wellρ.
  all: cbn ; lia.
Qed.

(* Testing that the definitions are right *)
Lemma id_ren (Γ : context) (ρ : Γ ≤ Γ) : (wk_to_ren ρ) =1 id.
Proof.
  destruct ρ as [ρ wellρ].
  cbn in *.
  pose proof (@eq_refl _ #|Γ|) as eΓ.
  revert eΓ wellρ.
  generalize Γ at 2 4.
  intros Δ e wellρ.
  induction wellρ in e |- *.
  all: cbn.
  - reflexivity.
  - pose proof (well_length {| wk := ρ ; well_wk := wellρ |}).
    now cbn in * ; lia.
  - etransitivity.
    2: eapply shiftn_id.
    now rewrite IHwellρ.
Qed.

Section TypingWk.

Variable foo : context_decl.

Lemma nth_error_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
  nth_error Γ n = Some decl ->
  {decl' & nth_error Δ (ρ n) = Some decl' ×
    map_decl (rename (ρ ∘ rshiftk (S n))) decl = map_decl (rename (rshiftk (S (ρ n)))) decl'}.
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ] ; cbn.
  induction wfρ in n, Hdecl |- *.
  - exists decl.
    split.
    1: easy.
    reflexivity.
  - cbn.
    edestruct IHwfρ as [decl' [? IH]].
    1: eassumption.
    eexists ; split.
    1: eassumption.
    now rewrite <- rename_compose, <- compose_map_decl, IH, compose_map_decl, rename_compose.
  - destruct n as [ | n].
    + cbn in *.
      inversion Hdecl ; subst ; clear Hdecl.
      eexists ; split.
      1: reflexivity.
      unfold map_decl ; cbn.
      f_equal.
      rewrite <- rename_inst, rename_compose.
      apply rename_ext.
      intros ?.
      now rewrite Nat.sub_0_r.
    + cbn in *.
      edestruct IHwfρ as [decl' [? IH]].
      1: eassumption.
      eexists ; split.
      1: now rewrite Nat.sub_0_r.
      now rewrite <- rename_compose, <- compose_map_decl, IH, compose_map_decl, rename_compose, Nat.sub_0_r.
  Qed.

Let PCon (Γ : context) := True.
Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A.[ren ρ]].
Let PTm (Γ : context) (t A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- t.[ren ρ] : A.[ren ρ]].
Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- A.[ren ρ] ≅ B.[ren ρ]].
Let PTmEq (Γ : context) (t u A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- t.[ren ρ] ≅ u.[ren ρ] : A.[ren ρ]].


Theorem typing_wk : wfInductionType PCon PTy PTm PTyEq PTmEq.
Proof.
  apply wfInduction.
  - red.
    trivial.
  - red. trivial.
  - intros ? ? IH.
    now econstructor.
  - intros Γ na A B HA IHA HB IHB Δ ρ HΔ.
    econstructor ; fold inst.
    1: easy.
    replace (B.[up 1 (ren ρ)]) with (B.[ren (wk_lift ρ)])
      by now rewrite ren_shiftn.
    unshelve eapply (IHB _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    all: now econstructor.
  - intros * _ IHA ? * ?.
    econstructor.
    now eapply IHA.
  - intros * _ IHΓ Hnth ? * ?.
    unshelve eapply nth_error_wk in Hnth as [decl' [? edecl]] ; tea.
    unfold ren at 1.
    cbn.
    eapply termMetaConv.
    1: econstructor ; eassumption.
    rewrite <- rename_inst, ! lift_rename, rename_compose, (map_decl_type _ decl'), (map_decl_type _ decl).
    f_equal.
    rewrite ! lift_renaming_0_rshift, <- edecl.
    eapply map_decl_ext ; intros ; eapply rename_ext ; intros ?.
    now rewrite lift_renaming_0_rshift.
  - intros * _ IHA _ IHB ? ρ ?.
    cbn.
    econstructor.
    1: now eapply IHA.
    replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
    unshelve eapply (IHB _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    1: now econstructor.
    econstructor ; tea.
    econstructor.
    now eapply IHA.
  - intros * _ IHA _ IHt ? ρ ?.
    cbn.
    econstructor.
    1: now eapply IHA.
    red in IHt.
    replace t.[_] with t.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
    replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
    unshelve eapply (IHt _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    1: now econstructor.
    econstructor ; tea.
    now eapply IHA.
  - intros * _ IHf _ IHu ? ρ ?.
    cbn.
    rewrite subst10_inst.
    replace B.[_] with B.[(up 1 (ren ρ))] by (now rewrite up_Up).
    econstructor.
    2: now eapply IHu.
    now eapply IHf.
  - intros * _ IHt _ IHAB ? ρ ?.
    econstructor.
    1: now eapply IHt.
    now eapply IHAB.
  - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
    cbn.
    econstructor.
    + now eapply IHA.
    + now eapply IHAA'.
    + replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      replace B'.[_] with B'.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      unshelve eapply (IHBB' _ {| wk := wk_lift ρ ; well_wk := _ |} _).
      1: now econstructor.
      econstructor ; tea.
      now eapply IHA.
  - intros * _ IHA ? ρ ?.
    eapply TypeRefl.
    now eapply IHA.
  - intros * _ IH ? ρ ?.
    econstructor.
    now eapply IH.
  - intros * _ IHA _ IHB ? ρ ?.
    eapply TypeTrans.
    + now eapply IHA.
    + now eapply IHB.
  - intros * _ IH ? ρ ?.
    eapply convUniv.
    now eapply IH.
  - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
    cbn.
    econstructor.
    + now eapply IHA.
    + now eapply IHAA'.
    + replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      replace B'.[_] with B'.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      unshelve eapply (IHBB' _ {| wk := wk_lift ρ ; well_wk := _ |} _).
      all: now econstructor.
  - intros Γ ? u u' f f' A B _ IHf _ IHu ? ρ ?.
    cbn.
    rewrite subst10_inst.
    replace B.[_] with B.[(up 1 (ren ρ))] by (now rewrite up_Up).
    now econstructor.
  - intros Γ ? u t A B _ IHA _ IHt _ IHu ? ρ ?.
    cbn. 
    rewrite ! subst10_inst.
    replace t.[⇑ _] with t.[(up 1 (ren ρ))] by (now rewrite up_Up).
    replace t.[_] with t.[ren (wk_lift ρ)] by (now rewrite ren_shiftn).
    replace B.[_] with B.[ren (wk_lift ρ)] by (now rewrite <- up_Up, ren_shiftn).
    econstructor.
    1,3: easy.
    unshelve eapply (IHt _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    all: now econstructor.
  - intros Γ ? ? f f' A B _ IHA _ IHf _ IHg _ IHe ? ρ ?.
    cbn.
    econstructor.
    1-3: easy.
    unshelve epose proof (IHe _ {| wk := wk_lift ρ ; well_wk := _ |} _) as IHe'.
    2: now econstructor.
    1: now econstructor.
    cbn in *.
    unfold ren in IHe' at 3 5.
    unfold eta_expand.
    cbn in *.
    rewrite ! lift0_inst, ! inst_assoc in IHe' |- *.
    replace B.[_] with B.[ren (shiftn 1 ρ)] by (now rewrite ren_shiftn).
    unshelve erewrite (inst_ext _ _ _ f), (inst_ext _ _ _ f').
    5: eassumption.
    all: rewrite <- Upn_ren.
    all: change 1 with (0 + 1).
    all: rewrite <- subst_shift_comm.
    all: cbn.
    all: now rewrite Upn_0.
  - intros * _ IHt ? ρ ?.
    now econstructor.
  - intros * _ IHt ? ρ ?.
    now econstructor.
  - intros * _ IHt _ IHt' ? ρ ?.
    now eapply TermTrans.
  - intros * _ IHt _ IHA ? ρ ?.
    now eapply TermConv.
Qed.

End TypingWk.