(** * LogRel.LogicalRelation.Definition.Sig : Definition of the logical relation for dependent sums *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Poly Ne Pi.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of dependent sum types *)

Definition WRedTyPack `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta} :=
  ParamRedTyPack (T:=tW).

Definition WRedTyAdequate@{i j} `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} (R : RedRel@{i j}) (WA : WRedTyPack@{i} Γ A B)
  : Type@{j} := PolyRedPackAdequate R WA.

Module WRedTyPack := ParamRedTyPack.


Module WRedTmEq.
Section WRedTmEq.
  Context `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    `{Typing ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedTerm ta}
    {Γ : context} {A B : term} {WA : WRedTyPack Γ A B}.


  Notation ContRedTm ρ a Ra wred k :=
    (ArrRedTm _ (WRedTyPack.codL WA)[a .: ρ >> tRel] (WRedTyPack.outTy WA)⟨ρ⟩
      (fun Ξ ρ' wfΞ => LRPack.eqTm (WA.(PolyRedPack.posRed) (ρ' ∘w ρ) wfΞ (Ra ρ' wfΞ)))
      wred k).


  Inductive WRedTmEq {Δ} {ρ : Δ ≤ Γ} : term -> term -> Type :=
  | Build_WRedTmEq {t u}
      (nfL : term)
      (nfR : term)
      (redL : [ Δ |- t :⤳*: nfL : (WRedTyPack.outTy WA)⟨ρ⟩ ])
      (redR : [ Δ |- u :⤳*: nfR : (WRedTyPack.outTy WA)⟨ρ⟩ ])
      (* really useful ? *)
      (eq : [ Δ |- nfL ≅ nfR : (WRedTyPack.outTy WA)⟨ρ⟩ ])
      (prop : @WPropEq Δ ρ nfL nfR) : WRedTmEq t u

  with WPropEq {Δ} {ρ : Δ ≤ Γ} : term -> term -> Type :=
  | supReq {A A' B B' a a' k k'}
    (* (wtA : [Γ |- A])
    (wtA' : [Γ |- A'])
    (wtB : [Γ,, A |- B])
    (wtB : [Γ,, A' |- B']) *)
    (convtyA : [Δ |- (WRedTyPack.domL WA)⟨ρ⟩ ≅ A])
    (convtyA' : [Δ |- (WRedTyPack.domL WA)⟨ρ⟩ ≅ A'])
    (* (convtyB : [Γ ,, WRedTyPack.domL WA |- WRedTyPack.codL WA ≅ B])
    (convtyB' : [Γ ,, WRedTyPack.domL WA |- WRedTyPack.codL WA ≅ B']) *)
    (* (convtyBa : [Γ |- (WRedTyPack.codL WA)[a..] ≅ B[a..]])
    (convtyBa' : [Γ |- (WRedTyPack.codL WA)[a..] ≅ B'[a'..]]) *)
    (Ra : forall {Ξ} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
      [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _ ≅ _])
    (* (PW := mkPolyRedPackWk1 (instPos WA ρ (@Ra)) (fun Ξ ρ' wfΞ => Build_LRPack Ξ (WRedTyPack.outTy WA)⟨ρ⟩⟨ρ'⟩ (WRedTyPack.outTy WA)⟨ρ⟩⟨ρ'⟩  (@WPropEq _ (ρ' ∘w ρ))))
    (Rk : PiRedTm PW k) *)
    (* (Rk : ArrRedTm Δ (WRedTyPack.domL WA) (WRedTyPack.codL WA)
     (fun Ξ ρ' wfΞ => LRPack.eqTm (WA.(PolyRedPack.posRed) (ρ' ∘w ρ) wfΞ (Ra ρ' wfΞ)))
     (fun Ξ ρ' wfΞ => @WPropEq _ (ρ' ∘w ρ)) k) *)
    (Rk : ContRedTm ρ a Ra (fun Ξ ρ' wfΞ => @WRedTmEq _ (ρ' ∘w ρ)) k)
    (Rk' : ContRedTm ρ a Ra (fun Ξ ρ' wfΞ => @WRedTmEq _ (ρ' ∘w ρ)) k')
    (Rkk' : forall {Ξ b b'} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
      [WA.(PolyRedPack.posRed) (ρ' ∘w ρ) wfΞ (Ra ρ' wfΞ) | _ ||- b ≅ b' : _ ≅ _] ->
      @WRedTmEq Ξ (ρ' ∘w ρ) (tApp k⟨ρ'⟩ b) (tApp k'⟨ρ'⟩ b')) :
    WPropEq (tSup A B a k) (tSup A' B' a' k')
  | neReq {ne ne'} :
    [Δ ||-NeNf ne ≅ ne' : (WRedTyPack.outTy WA)⟨ρ⟩] -> WPropEq ne ne'.


  Definition ContRedTmε
    (P : forall [Δ] (ρ : Δ ≤ Γ) [t u], @WRedTmEq _ ρ t u -> Type)
    [Δ] (ρ : Δ ≤ Γ) [a a']
    (Ra : forall {Ξ} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _ ≅ _])
    [k] (Rk : ContRedTm ρ a Ra (fun Ξ ρ' wfΞ => @WRedTmEq _ (ρ' ∘w ρ)) k) : Type.
  Proof.
    destruct Rk as [?? [???? Rt|]]; [| exact unit].
    refine (forall [Ξ b b'] (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ])
      (Rb : [PolyRedPack.posRed WA (ρ' ∘w ρ) wfΞ (Ra Ξ ρ' wfΞ) | _ ||- b ≅ b' : _ ≅ _]), _).
    eapply P, Rt, Rb.
  Defined.

  Section Eliminator.
    Context
      (P : forall [Δ] (ρ : Δ ≤ Γ) [t u], @WRedTmEq _ ρ t u -> Type)
      (Q : forall [Δ] (ρ : Δ ≤ Γ) [t u], @WPropEq _ ρ t u -> Type)
      (hred : forall [Δ] (ρ : Δ ≤ Γ) [t u] nfL nfR redL redR eq (prop : @WPropEq Δ ρ nfL nfR),
        Q ρ prop -> @P _ ρ t u (Build_WRedTmEq nfL nfR redL redR eq prop))
      (hne : forall [Δ] (ρ : Δ ≤ Γ) ne ne' (Rne : [Δ ||-NeNf ne ≅ ne' : (WRedTyPack.outTy WA)⟨ρ⟩]),
        Q ρ (neReq Rne))
      (hsup : forall [Δ] (ρ : Δ ≤ Γ) {A A' B B' a a' k k'}
        (convtyA : [Δ |- (WRedTyPack.domL WA)⟨ρ⟩ ≅ A])
        (convtyA' : [Δ |- (WRedTyPack.domL WA)⟨ρ⟩ ≅ A'])
        (Ra : forall {Ξ} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _ ≅ _])
        (Rk : ContRedTm ρ a Ra (fun Ξ ρ' wfΞ => @WRedTmEq _ (ρ' ∘w ρ)) k)
        (Rk' : ContRedTm ρ a Ra (fun Ξ ρ' wfΞ => @WRedTmEq _ (ρ' ∘w ρ)) k')
        (Rkk' : forall {Ξ b b'} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
          [WA.(PolyRedPack.posRed) (ρ' ∘w ρ) wfΞ (Ra ρ' wfΞ) | _ ||- b ≅ b' : _ ≅ _] ->
          @WRedTmEq Ξ (ρ' ∘w ρ) (tApp k⟨ρ'⟩ b) (tApp k'⟨ρ'⟩ b')),
        ContRedTmε P ρ (@Ra) Rk ->
        ContRedTmε P ρ (@Ra) Rk' ->
        (forall Ξ b b' (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]) (Rb : [WA.(PolyRedPack.posRed) (ρ' ∘w ρ) wfΞ (Ra ρ' wfΞ) | _ ||- b ≅ b' : _ ≅ _]),
          P (ρ' ∘w ρ) (Rkk' ρ' wfΞ Rb)) ->
        Q ρ (supReq (B:=B) (B':=B') convtyA convtyA' (@Ra) Rk Rk' (@Rkk'))).

    Arguments P [_] _ [_ _].
    Arguments Q [_] _ [_ _].

    Fixpoint WRedTmEq_mut_rect [Δ] (ρ : Δ ≤ Γ) [t t'] (Rt : @WRedTmEq _ ρ t t') : P ρ Rt
    with WPropEq_mut_rect [Δ] (ρ : Δ ≤ Γ) [t t'] (Rt : @WPropEq _ ρ t t') : Q ρ Rt.
    Proof.
      all: destruct Rt.
      - apply hred, WPropEq_mut_rect.
      - apply hsup.
        + unfold ContRedTmε; destruct Rk as [?? isfun]; destruct isfun; [|easy].
          intros; apply WRedTmEq_mut_rect.
        + unfold ContRedTmε; destruct Rk' as [?? isfun]; destruct isfun; [|easy].
          intros; apply WRedTmEq_mut_rect.
        + intros; apply WRedTmEq_mut_rect.
      - apply hne.
    Defined.

  Let WRedEqInductionType0 :=
    (forall Δ (ρ : Δ ≤ Γ) [t t'] (Rt : @WRedTmEq _ ρ t t'), P ρ Rt) ×
    (forall Δ (ρ : Δ ≤ Γ) [t t'] (Rt : @WPropEq _ ρ t t'), Q ρ Rt).

  Definition WRedEqInductionType := WRedEqInductionType0.
  Definition WRedEqInduction : WRedEqInductionType0 := (@WRedTmEq_mut_rect, @WPropEq_mut_rect).

  End Eliminator.


(* Scheme WRedTmEq_mut_rect := Induction for WRedTmEq Sort Type with
    WPropEq_mut_rect := Induction for WPropEq Sort Type.

Combined Scheme _WRedInduction from
  WRedTmEq_mut_rect,
  WPropEq_mut_rect.

Combined Scheme _WRedEqInduction from
  WRedTmEq_mut_rect,
  WPropEq_mut_rect.

Let _WRedEqInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _WRedEqInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let WRedEqInductionType :=
  ltac: (let ind := eval cbv delta [_WRedEqInductionType] zeta
    in _WRedEqInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma WRedEqInduction : WRedEqInductionType.
Proof.
  intros PRedEq PPropEq **; split; now apply (_WRedEqInduction PRedEq PPropEq).
Defined. *)

End WRedTmEq.
Arguments WRedTmEq {_ _ _ _ _ _ _ _ _ _ _ _} _ {_}.
Arguments WPropEq {_ _ _ _ _ _ _ _ _ _ _ _} _ {_}.

Section Lemmas.
  Context `{GenericTypingProperties} {Γ A B} {WA : WRedTyPack Γ A B}.

  Lemma wred_isW {Δ} {ρ : Δ ≤ Γ} {t u} : WPropEq WA ρ t u -> isW t <&> isW u.
  Proof.
    intros [| ?? []]; split ; constructor.
    all: eapply convneu_whne; tea; now symmetry.
  Qed.

  Lemma whredtm_both {Δ} {ρ : Δ ≤ Γ} {t u} : WRedTmEq WA ρ t u -> [Δ |- t ↘  (WRedTyPack.outTy WA)⟨ρ⟩ ] <&> [Δ |- u ↘  (WRedTyPack.outTy WA)⟨ρ⟩ ].
  Proof.
    intros []; split; econstructor; tea;
    eapply isW_whnf; [eapply nfst|eapply nsnd]; now eapply wred_isW.
  Defined.

  Lemma whredtm_both_id {t u} : WRedTmEq WA (@wk_id Γ) t u -> [Γ |- t ↘  (WRedTyPack.outTy WA) ] <&> [Γ |- u ↘  (WRedTyPack.outTy WA) ].
  Proof.
    intros [[] []]%whredtm_both; split; econstructor.
    1,3: erewrite <-(wk_id_ren_on Γ (WRedTyPack.outTy _)); tea.
    all: tea.
  Defined.

End Lemmas.

End WRedTmEq.

Export WRedTmEq(WRedTmEq,Build_WRedTmEq, WPropEq, WRedEqInduction).
