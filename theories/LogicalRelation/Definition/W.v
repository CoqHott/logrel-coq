(** * LogRel.LogicalRelation.Definition.Sig : Definition of the logical relation for dependent sums *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Poly Ne.

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

  Inductive WRedTmEq {Δ} {ρ : Δ ≤ Γ} : term -> term -> Type :=
  | Build_WRedTmEq {t u}
      (nfL : term)
      (nfR : term)
      (redL : [ Δ |- t :⤳*: nfL : (WRedTyPack.outTy WA)⟨ρ⟩ ])
      (redR : [ Δ |- u :⤳*: nfR : (WRedTyPack.outTy WA)⟨ρ⟩ ])
      (* really useful ? *)
      (eq : [ Γ |- nfL ≅ nfR : (WRedTyPack.outTy WA)⟨ρ⟩ ])
      (prop : @WPropEq Δ ρ nfL nfR) : WRedTmEq t u

  with WPropEq {Δ} {ρ : Δ ≤ Γ} : term -> term -> Type :=
  | supReq {A A' B B' a a' k k'}
    (* (wtA : [Γ |- A])
    (wtA' : [Γ |- A']) *)
    (convtyA : [Γ |- WRedTyPack.domL WA ≅ A])
    (convtyA' : [Γ |- WRedTyPack.domL WA ≅ A'])
    (convtyB : [Γ ,, WRedTyPack.domL WA |- WRedTyPack.codL WA ≅ B])
    (convtyB' : [Γ ,, WRedTyPack.domL WA |- WRedTyPack.codL WA ≅ B'])
    (Ra : forall {Ξ} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
      [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _ ≅ _])
    (Rk : forall {Ξ b b'} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
      [WA.(PolyRedPack.posRed) (ρ' ∘w ρ) wfΞ (Ra ρ' wfΞ) | _ ||- b ≅ b' : _ ≅ _] ->
      @WRedTmEq Ξ (ρ' ∘w ρ) (tApp k⟨ρ'⟩ b) (tApp k'⟨ρ'⟩ b')) :
    WPropEq (tSup A B a k) (tSup A' B' a' k')
  | neReq {ne ne'} :
    [Γ ||-NeNf ne ≅ ne' : (WRedTyPack.outTy WA)⟨ρ⟩] -> WPropEq ne ne'.

Scheme WRedTmEq_mut_rect := Induction for WRedTmEq Sort Type with
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
Defined.

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
