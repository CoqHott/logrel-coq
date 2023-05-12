
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeTyping DeclarativeInstance Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity Reduction Application Universe NormalRed SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var.

Set Universe Polymorphism.

Section List.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma listRed@{i j k l} {Γ A l} :
 [LogRel@{i j k l} l | Γ ||- A] ->
 [LogRel@{i j k l} l | Γ ||- tList A].
Proof.
  intros.
  unshelve eapply LRList'.
  escape.
  econstructor. 2: eapply escape ; eassumption.
  - eapply redtywf_refl. gen_typing.
  - eapply convty_list. unshelve eapply escapeEq. 2: eassumption.
    eapply LRTyEqRefl_.
  - assumption.
Defined.


Lemma listEqRed {Γ A A' l}
  (RA: [Γ ||-<l> A]) (RA': [Γ |- A'])
  (RLA: [Γ ||-<l> tList A])
  :
  [Γ ||-<l> A ≅ A' | RA] -> [Γ ||-<l> tList A ≅ tList A' | RLA ].
Proof.
  intros.
  enough ([ normList RLA | Γ ||- tList A ≅ tList A']) by irrelevance.
  econstructor.
  - eapply redtywf_refl. now eapply wft_list.
  - cbn. eapply convty_list. escape. assumption.
  - irrelevance.
Defined.

Lemma listValid {Γ A l} (VΓ : [||-v Γ]) (h: [Γ ||-v<l> A | VΓ]) : [Γ ||-v<l> tList A | VΓ].
Proof.
  unshelve econstructor; intros.
  + eapply listRed.
    now eapply validTy.
  + eapply listEqRed ; tea.
    (* now eapply validTyExt. *)
    1-2: now instAllValid vσ vσ' vσσ' ; escape.
Defined.

Lemma listCongValid {l Γ A A'} (VΓ : [||-v Γ])
  (VA : [Γ ||-v< l > A | VΓ ])
  (VA' : [Γ ||-v< l > A' | VΓ ])
  (VeqA : [Γ ||-v< l > A ≅ A' | VΓ | VA]) :
  [Γ ||-v<l> tList A ≅ tList A' | VΓ | listValid _ VA].
Proof.
  constructor; intros.
  pose (h:=validTy VA _ Vσ).
  eapply listEqRed; tea.
  1-2: now instValid Vσ; escape.
Qed.

(* this is a copy paste from Nat.v *)
Lemma redUOne {Γ} : [|- Γ] -> [Γ ||-U<one> U].
Proof.
  intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
Defined.


(* We need one more level h < i and cumulativity of the logical relation
   to be able to reuse the lemma listRed at the smaller level zero *)
Lemma listTermRed@{h i j k l} {Δ A} (wfΔ : [|-Δ])
  : [Δ ||-<one> A : U | LRU_@{i j k l} (redUOne wfΔ)] ->
    [Δ ||-<one> tList A : U | LRU_@{i j k l} (redUOne wfΔ)].
Proof.
  intros.
  escape.
  econstructor.
  + eapply redtmwf_refl.
    now eapply ty_list.
  + constructor.
  + apply tm_nf_list. now eapply reifyTerm.
  + eapply convtm_list.
    eapply escapeEqTerm.
    eapply LREqTermRefl_.
    eassumption.
  + refine (LRCumulative@{Set l i j k l h i j k } _).
    eapply (listRed@{i j k l} (l:=zero)); tea.
    now eapply UnivEq'.
Defined.

Lemma listTermValid@{h i j k l} {Γ A}
  (VΓ : [VR@{i j k l}| ||-v Γ]) :
  termValidity@{i j k l} Γ one A U VΓ (UValid@{i j k i j k l l} VΓ) ->
  termValidity@{i j k l} Γ one (tList A) U VΓ (UValid@{i j k i j k l l} VΓ).
Proof.
  constructor ; intros.
  - eapply listTermRed@{h i j k l}.
    fold subst_term.
    instValid Vσ.
    irrelevance.
  - instAllValid Vσ Vσ' Vσσ'.
    assert [LogRel0@{i j k} | Δ ||- tList A[σ]].
    1:{
      refine (LRCumulative@{Set l i j k l h i j k } _).
      eapply (listRed@{i j k l} (l:=zero)); tea.
      now eapply UnivEq'.
    }
    unshelve econstructor; fold subst_term; cbn.
    1,2: eapply listTermRed ; irrelevance.
    2: cbn; eapply convtm_list; now escape.
    + tea.
    + refine (LRCumulative@{Set l i j k l h i j k } _).
      eapply (listRed@{i j k l} (l:=zero)); tea.
      now eapply UnivEq'.
    + refine (LRTyEqIrrelevantCum@{i j k l h i j k } _ _ _ _ _ _ _ _).
      eapply (listEqRed (l:=zero)); tea.
      1: now eapply escape; eapply UnivEq'.
      now eapply UnivEqEq.
      Unshelve.
      1: irrelevanceCum.
      now eapply UnivEq'.
Qed.


(* TODO: cleanup!! *)
Lemma nilRed' {Γ A A' l}
  (RA: [Γ ||-< l > A])
  (wtyA' : [Γ |- A'])
  (RAA' : [Γ ||-< l > A ≅ A' | RA])
  (RLA: [Γ ||-< l > tList A]) :
  [Γ ||-<l> tNil A' : tList A | normList RLA].
Proof.
  econstructor.
  + eapply redtmwf_refl. eapply ty_conv. 1: now apply ty_nil.
    eapply convty_list. symmetry. now escape.
  + eapply convtm_conv.
    * eapply convtm_nil. etransitivity. 1: symmetry.
      1-2: now eapply escapeEq.
    * symmetry. eapply convty_list. now eapply escapeEq.
  + constructor ; tea. irrelevance.
Defined.

Lemma nilRed {Γ A A' l}
  (RA: [Γ ||-< l > A])
  (wtyA' : [Γ |- A'])
  (RAA' : [Γ ||-< l > A ≅ A' | RA])
  (RLA: [Γ ||-< l > tList A]) :
  [Γ ||-<l> tNil A' : tList A | RLA].
Proof.
  enough [ normList RLA | Γ ||- tNil A' : _] by irrelevance.
  now eapply nilRed'.
Defined.

Lemma nilEqRed {Γ A A' B l}
  (RB: [Γ ||-< l > B])
  (wtyA : [Γ |- A])
  (wtyA' : [Γ |- A'])
  (RLB: [Γ ||-< l > tList B]) :
  [RB | Γ ||- B ≅ A] ->
  [RB | Γ ||- B ≅ A'] ->
  [RLB | Γ ||- tNil A ≅ tNil A' : tList B].
Proof.
  intros. escape.
  enough [normList RLB | Γ ||- tNil A ≅ tNil A' : _] by irrelevance.
  unshelve econstructor.
  + change [ normList RLB | Γ ||- tNil A : _].
    eapply nilRed' ; tea.
  + change [ normList RLB | Γ ||- tNil A' : _].
    eapply nilRed' ; tea.
  + cbn. eapply convtm_conv. 2: eapply convty_list; symmetry; tea.
    eapply convtm_nil. etransitivity; tea.
    symmetry; tea.
  + cbn. econstructor ; tea.
    all: irrelevance.
Qed.

Lemma nilValid {Γ A l}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  {VLA : [Γ ||-v<l> tList A | VΓ]} :
  [Γ ||-v<l> tNil A : tList A | VΓ | VLA].
Proof.
  split; intros.
  - instValid Vσ.
    unshelve eapply nilRed ; tea.
    + unshelve eapply escape; eassumption.
    + apply LRTyEqRefl_.
  - instAllValid Vσ Vσ' Vσσ'.
    eapply nilEqRed.
    + unshelve eapply escape; eassumption.
    + unshelve eapply escape; eassumption.
    + apply LRTyEqRefl_.
    + eassumption.
Qed.

Lemma consRed' {Γ A A' hd tl l}
  (RA: [Γ ||-< l > A])
  (wtyA' : [Γ |- A'])
  (RAA' : [Γ ||-< l > A ≅ A' | RA])
  (RLA: [Γ ||-< l > tList A]) :
  [RA | Γ ||- hd : A] ->
  [RLA | Γ ||- tl : tList A] ->
  [normList RLA | Γ ||- tCons A' hd tl : tList A ].
Proof.
  econstructor.
  + eapply redtmwf_refl. eapply ty_conv.
    1: {
      apply ty_cons; tea; eapply ty_conv; escape; tea.
      now eapply convty_list.
    }
    symmetry. eapply convty_list. now escape.
  + eapply convtm_conv. 2: (symmetry; eapply convty_list; now escape).
    eapply convtm_cons.
    * etransitivity. 1: symmetry. all: now escape.
    * eapply convtm_conv. 2: now escape.
      eapply escapeEqTerm ; tea.
      now apply LREqTermRefl_.
    * eapply convtm_conv. 2: (eapply convty_list; now escape).
      eapply escapeEqTerm ; tea.
      now apply LREqTermRefl_.
  + constructor. 1: escape ; tea.
    * irrelevance.
    * irrelevance.
    * change [ normList RLA | Γ ||- tl : tList A].
      irrelevance.
Defined.

Lemma consRed {Γ A A' hd tl l}
  (RA: [Γ ||-< l > A])
  (wtyA' : [Γ |- A'])
  (RAA' : [Γ ||-< l > A ≅ A' | RA])
  (RLA: [Γ ||-< l > tList A]) :
  [RA | Γ ||- hd : A] ->
  [RLA | Γ ||- tl : tList A] ->
  [RLA | Γ ||- tCons A' hd tl : tList A ].
Proof.
  intros. enough [ normList RLA | Γ ||- tCons A' hd tl : _] by irrelevance.
  now eapply consRed'.
Qed.

Lemma consEqRed {Γ A A' P P' hd hd' tl tl' l}
  (RA: [Γ ||-< l > A])
  (RA': [Γ ||-< l > A'])
  (RLA: [Γ ||-< l > tList A]) 
  (RLA': [Γ ||-< l > tList A']) :
  [Γ |- P] ->
  [Γ |- P'] ->
  [RA | Γ ||- A ≅ A'] ->
  [RA | Γ ||- A ≅ P] ->
  [RA' | Γ ||- A' ≅ P'] ->
  [RA | Γ ||- hd : A] ->
  [RA' | Γ ||- hd' : A'] ->
  [RA | Γ ||- hd ≅ hd' : A] ->
  [RLA | Γ ||- tl ≅ tl' : tList A] ->
  [RLA | Γ ||- tl : tList A] ->
  [RLA' | Γ ||- tl' : tList A'] ->
  [RLA | Γ ||- tCons P hd tl ≅ tCons P' hd' tl' : tList A ].
Proof.
  intros; escape.
  assert [normList RLA | Γ ||- tList A ≅ tList A' ]
    by now unshelve eapply listEqRed.
  enough [ normList RLA | Γ ||- tCons P hd tl ≅ tCons P' hd' tl' : _] by irrelevance.
  unshelve econstructor.
  - now eapply consRed'.
  - eapply consRed'; tea.
    + eapply LRTransEq; [| tea]; tea.
    + eapply LRTmRedConv; tea.
      now eapply LRTyEqSym.
    + eapply LRTmRedConv; tea. 
      now eapply LRTyEqSym.
  - cbn. eapply convtm_conv.
    1: eapply convtm_cons.
    + etransitivity; tea; etransitivity; tea; now symmetry.
    + now eapply convtm_conv.
    + eapply convtm_conv; tea.
      now eapply convty_list.
    + symmetry; now eapply convty_list.
  - econstructor; tea; cbn; try solve [ irrelevance | eapply LRTyEqRefl_ ].
    1: eapply LRTransEq; [| tea]; irrelevance.
    change [normList RLA | Γ ||- tl ≅ tl' : tList A].
    irrelevance.
Qed.

Lemma consValid {Γ A hd tl l}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  {VLA : [Γ ||-v<l> tList A | VΓ]}
  (Vhd : [Γ ||-v<l> hd : A | VΓ | VA ])
  (Vtl : [Γ ||-v<l> tl : tList A | VΓ | VLA ]) :
  [Γ ||-v<l> tCons A hd tl : tList A | VΓ | VLA].
Proof.
  split; intros.
  - instValid Vσ.
    eapply consRed.
    all: escape; tea.
    eapply LRTyEqRefl_.
  - instAllValid Vσ Vσ' Vσσ'.
    escape. eapply consEqRed; refold; tea.
    all: eapply LRTyEqRefl_.
Qed.

Definition mapProp {Γ L l} (A B f x: term) {LL : [Γ ||-List<l> L]} (p : ListProp _ _ LL x) : term.
Proof.
  destruct p as [  | | x ].
  - exact (tNil B).
  - exact (tCons B (tApp f hd) (tMap A B f tl)).
  - exact (tMap A B f x).
Defined.


Lemma mapRedAux {Γ A B f l}
  {RA : [Γ ||-<l> A]}
  {RB : [Γ ||-<l> B]}
  {LA : [Γ ||-List<l> tList A]}
  (LA' := normList0 LA : [Γ ||-List<l> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<l> tList A] )
  {RLB : [Γ ||-<l> tList B]}
  {RFAB : [Γ ||-<l> arr A B]}
  (Rf: [Γ ||-<l> f : arr A B | RFAB]) :
  (forall x (Rx: ListRedTm _ _ LA' x),
        [Γ ||-<l> tMap A B f x : tList B | RLB] ×
        [Γ ||-<l> tMap A B f x ≅ tMap A B f (ListRedTm.nf Rx) : tList B | RLB])
    ×
    (forall x (Rx: ListProp _ _ LA' x),
        [Γ ||-<l> tMap A B f x : tList B | RLB] ×
          [Γ ||-<l> tMap A B f x ≅ mapProp A B f x Rx : tList B | RLB]).
Proof.
  escape.
  apply ListRedInduction.
  - intros.
    apply redSubstTerm. 1: intuition.
    apply redtm_map ; tea.
    eapply redtm_conv. 1: now apply red.
    destruct LA. cbn in *. gen_typing.
  - intros.
    apply redSubstTerm.
    + unshelve eapply nilRed; tea.
      eapply LRTyEqRefl_.
    + eapply redtm_map_nil; tea.
      unshelve eapply escapeEq.
      3: eassumption.
  - intros.
    apply redSubstTerm.
    + unshelve eapply consRed; tea.
      * eapply LRTyEqRefl_.
      * now eapply simple_appTerm.
      * intuition.
    + eapply redtm_map_cons; tea.
      * now eapply escapeEq.
      * now eapply escapeTerm.
      * change [LRList' LA' | Γ ||- tl : _ ] in l0.
        now eapply escapeTerm.

  - intros. cbn.
    eapply redSubstTerm.
    + enough [normList RLB | Γ ||- tMap A B f l0 : tList B] by irrelevance.
      econstructor.
      * cbn. apply redtmwf_refl. apply ty_map; tea.
        match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
      * { unshelve eapply escapeEqTerm; tea;
          eapply neuTermEq.
          - eapply tm_ne_map;
                  try solve [ eapply reifyType; tea | eapply reifyTerm; tea ];
                  now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
          - eapply tm_ne_map;
                  try solve [ eapply reifyType; tea | eapply reifyTerm; tea ];
                  now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
          - eapply ty_map; try now escape.
            now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
          - eapply ty_map; try now escape.
            now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
          - eapply convneu_map.
            + unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
            + unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
            + eapply escapeEqTerm. now eapply LREqTermRefl_.
            + now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
        }
      * { constructor. cbn. constructor.
          - apply tm_ne_map; try solve [ eapply reifyType; tea | eapply reifyTerm; tea ].
            now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
          - apply ty_map; tea.
            now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
          - eapply convneu_map; try solve [ eapply escapeEq; eapply LRTyEqRefl_
                                          | eapply escapeEqTerm; eapply LREqTermRefl_; tea ].
            now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => destruct H end.
        }
    + apply redtm_refl ; apply ty_map ; tea.
      now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.

      Unshelve.
      all: tea.
Qed.

Lemma mapEqRedAux {Γ A A' B B' f f' l}
  {RA : [Γ ||-<l> A]}
  {RA' : [Γ ||-<l> A']}
  {REA : [RA | Γ ||- A ≅ A' ]}
  {RB : [Γ ||-<l> B]}
  {RB' : [Γ ||-<l> B']}
  {REB : [RB | Γ ||- B ≅ B' ]}
  {LA : [Γ ||-List<l> tList A]}
  (LA_ := normList0 LA : [Γ ||-List<l> tList A])
  {LA' : [Γ ||-List<l> tList A']}
  (LA'_ := normList0 LA' : [Γ ||-List<l> tList A'])
  (RLA := LRList' LA_ : [Γ ||-<l> tList A] )
  {RLB : [Γ ||-<l> tList B]}
  {RLB' : [Γ ||-<l> tList B']}
  {RELA : [Γ ||-<l> tList A ≅ tList A' | RLA ]}
  {RELB : [Γ ||-<l> tList B ≅ tList B' | RLB ]}
  {RFAB : [Γ ||-<l> arr A B]}
  {RFAB' : [Γ ||-<l> arr A' B']}
  (Rf: [Γ ||-<l> f : arr A B | RFAB])
  (Rf': [Γ ||-<l> f' : arr A' B' | RFAB'])
  {Rff: [Γ ||-<l> f ≅ f' : arr A B | RFAB]} :
  (forall x x' (Rxx': ListRedTmEq _ _ LA_ x x'),
        [Γ ||-<l> tMap A B f x ≅ tMap A' B' f' x' : tList B | RLB])
    ×
    (forall x x' (Rxx': ListPropEq _ _ LA_ x x'), 
        [ LRList' LA_ | _ ||- x : _ ] ->
        [ LRList' LA_ | _ ||- x' : _ ] ->
          [Γ ||-<l> tMap A B f x ≅ tMap A' B' f' x' : tList B | RLB]).
Proof.
  apply ListRedEqInduction.
  - intros.
    unshelve eapply LREqTermHelper.
    8: {
      apply X.
      - eapply redTmFwd. exact Rt.
        1-2: admit.
      - eapply redTmFwd. exact Ru.
        1-2: admit.
    }
    3: now unshelve eapply mapRedAux.
    4: eassumption. 1: eassumption.
    unshelve epose (Ru' := _ : ListRedTm Γ (tList A') LA'_ u).
    {
      change ([LRList' LA'_ | Γ ||- u : _ ]).
      unshelve eapply (fst (ListIrrelevanceTm LA_ LA'_ _ _ _) _ Ru).
      1-2: now escape.
      eapply LRIrrelevantCum.
      3: {
        cbn. now irrelevanceRefl.
      }
      1-2: eapply LRAd.adequate.
    }
    replace (ListRedTm.nf Ru) with (ListRedTm.nf Ru').
    2: destruct Ru; reflexivity.
    now unshelve eapply mapRedAux.
  - intros.
    eapply LREqTermHelper.
    3: eassumption.
    + unshelve eapply mapRedAux ; tea.
      econstructor ; tea.
      irrelevance.
    + unshelve eapply mapRedAux ; tea.
      constructor; tea.
      unshelve eapply LRTransEq.
      5: eassumption.
      eapply LRTyEqSym ; tea.
    + cbn. escape. eapply nilEqRed; tea.
      eapply LRTyEqRefl_.

  - intros.
    eapply LREqTermHelper.
    + unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LA_) | Γ ||- tCons P hd tl : _ ].
      irrelevance.
    + unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LA'_) | Γ ||- tCons P' hd' tl' : _ ].
      eapply LRTmRedConv; tea.
    + tea.
    + admit.
  - intros.
    enough [normList RLB | Γ ||- tMap A B f l0 ≅ tMap A' B' f' l' : tList B] by irrelevance.
    unshelve econstructor.
    + change [normList RLB | Γ ||- tMap A B f l0 : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
      change [LRList' (normList0 LA_) | Γ ||- l0 : tList A].
      match goal with H : [Γ ||-NeNf _ ≅ _ : tList _] |- _ => destruct H end.
      irrelevance.
    + enough [normList RLB' | Γ ||- tMap A' B' f' l' : _ ].
      1:{
        change [normList RLB | Γ ||- tMap A' B' f' l' : _ ].
        eapply LRTmRedConv. 1: eapply LRTyEqSym ; tea.
        eassumption.
      }
      econstructor.
      * eapply redtm_refl. apply ty_map; escape; tea.
        unshelve eapply ty_conv. 2-3: tea.
      * { eapply convneu_map.
          - eapply escapeEq. eapply LRTyEqRefl_.
          - cbn. eapply escapeEq. eapply LRTyEqRefl_.
          - cbn. admit.
          - admit.
        }
      * { constructor. constructor.
          - eapply tm_ne_map.
            1-2: now eapply reifyType.
            1: now eapply reifyTerm.
            eapply tm_ne_conv; escape; tea.
            now eapply NeNf.neR.
            eapply escape.
            exact (LRList' LA'_).
          - eapply ty_map; escape; tea.
            eapply ty_conv; escape; tea.
          - eapply convneu_map.
            + eapply escapeEq. eapply LRTyEqRefl_.
            + eapply escapeEq. eapply LRTyEqRefl_.
            + eapply escapeEqTerm. now eapply LREqTermRefl_.
            + eapply convneu_conv. 2: now eapply escapeEq.
              match goal with H : [Γ ||-NeNf _ ≅ _ : tList _] |- _ => destruct H end.
              etransitivity; tea. now symmetry.
        }

        all: admit.
Admitted.

(* TODO: move; also wk_arr vs arr_wk *)
Lemma subst_arr A B σ : (arr A B)[σ] = arr (subst_term σ A) (subst_term σ B).
Proof. now bsimpl. Qed.

Lemma mapValid {Γ A B f x i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VB : [Γ ||-v<i> B | VΓ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VFAB : [Γ ||-v<i> arr A B | VΓ]}
  (Vf : [Γ ||-v<i> f : arr A B | VΓ | VFAB ])
  (Vx : [Γ ||-v<i> x : tList A | VΓ | VLA ]) :
  [Γ ||-v<i> tMap A B f x : tList B | VΓ | VLB].
Proof.
  split; intros.
  - instValid Vσ.
    unshelve eapply (fst (mapRedAux _)) ; tea ; fold subst_term.
    + now eapply invLRList.
    + now eapply ArrRedTy.
    + irrelevance0 ; tea.
      apply subst_arr.
    + change [normList RVLA | Δ ||- x[σ] : (tList A)[σ]]. irrelevance.

  - instAllValid Vσ Vσ' Vσσ'.
    unshelve eapply (fst (mapEqRedAux _ _)) ; tea ; fold subst_term.
    + now eapply invLRList.
    + now eapply invLRList.
    + irrelevance.
    + now eapply ArrRedTy.
    + now eapply ArrRedTy.
    + irrelevance0 ; tea.
      apply subst_arr.
    + irrelevance0 ; tea.
      apply subst_arr.
    + change [ArrRedTy RVA RVB | Δ ||- f[σ] ≅ f[σ'] : _].
      irrelevance.
    + change [normList RVLA | Δ ||- x[σ] ≅ x[σ'] : _]. irrelevance.
Qed.

Lemma mapCongValid {Γ A A' B B' f f' x x' i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VA' : [Γ ||-v<i> A' | VΓ]}
  {VAA' : [Γ ||-v<i> A ≅ A' | VΓ | VA ]}
  {VB : [Γ ||-v<i> B | VΓ]}
  {VB' : [Γ ||-v<i> B' | VΓ]}
  {VBB' : [Γ ||-v<i> B ≅ B' | VΓ | VB ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {VLA' : [Γ ||-v<i> tList A' | VΓ]}
  {VLALA' : [Γ ||-v<i> tList A ≅ tList A' | VΓ | VLA ]}
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VLB' : [Γ ||-v<i> tList B' | VΓ]}
  {VLBLB' : [Γ ||-v<i> tList B ≅ tList B' | VΓ | VLB ]}
  {VFAB : [Γ ||-v<i> arr A B | VΓ]}
  {VFAB' : [Γ ||-v<i> arr A' B' | VΓ]}
  {Vf : [Γ ||-v<i> f : arr A B | VΓ | VFAB ]}
  {Vf' : [Γ ||-v<i> f' : arr A' B' | VΓ | VFAB' ]}
  {Vff' : [Γ ||-v<i> f ≅ f' : arr A B | VΓ | VFAB ]}
  {Vx : [Γ ||-v<i> x : tList A | VΓ | VLA ]}
  {Vx' : [Γ ||-v<i> x' : tList A' | VΓ | VLA' ]}
  {Vxx' : [Γ ||-v<i> x ≅ x' : tList A | VΓ | VLA ]} :
  [Γ ||-v<i> tMap A B f x ≅ tMap A' B' f' x' : tList B | VΓ | VLB].
Proof.
  split. intros.
  instValid Vσ.
  unshelve eapply (fst (mapEqRedAux _ _)) ; tea ; fold subst_term.
  + now eapply invLRList.
  + now eapply invLRList.
  + irrelevance.
  + admit.
  + admit.
  + cbn. admit.
  + admit.
  + admit.
  + admit.
Admitted.

Lemma mapRedNilValid {Γ A B f i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VB : [Γ ||-v<i> B | VΓ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VFAB : [Γ ||-v<i> arr A B | VΓ]}
  {Vf : [Γ ||-v<i> f : arr A B | VΓ | VFAB ]} :
  [Γ ||-v<i> tMap A B f (tNil A) ≅ tNil B : tList B | VΓ | VLB].
Proof.
  split. intros.
  instValid Vσ.
  cbn.
  epose (snd (mapRedAux _) (tNil A[σ]) _).
  (* 6: exact RVB. *)
  (* 4: { *)
  (*   now eapply invLRList. *)
  (* } *)
  (* 7: { *)
  (*   constructor. *)
  (*   - escape; tea. *)
  (*   - cbn. irrelevance. *)
  (* } *)
Admitted.

Lemma mapRedConsValid {Γ A B f hd tl i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VB : [Γ ||-v<i> B | VΓ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VFAB : [Γ ||-v<i> arr A B | VΓ]}
  {Vf : [Γ ||-v<i> f : arr A B | VΓ | VFAB ]} :
  [Γ ||-v<i> tMap A B f (tCons A hd tl) ≅ tCons B (tApp f hd) (tMap A B f tl) : tList B | VΓ | VLB].
Proof.
  (* should be a simple consequence of mapRedAux? *)
  (* NOTE: missing hypotheses on hd and tl *)
Admitted.

Lemma mapRedCompValid {Γ A B C f g l l' i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VB : [Γ ||-v<i> B | VΓ]}
  {VC : [Γ ||-v<i> C | VΓ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VLC : [Γ ||-v<i> tList C | VΓ]}
  {VFBC : [Γ ||-v<i> arr B C | VΓ]}
  {VFAB' : [Γ ||-v<i> arr A B | VΓ]}
  {Vf : [Γ ||-v<i> f : arr B C | VΓ | VFBC ]}
  {Vg : [Γ ||-v<i> g : arr A B | VΓ | VFAB' ]}
  {Vl : [Γ ||-v<i> l : tList A | VΓ | VLA ]}
  {Vl' : [Γ ||-v<i> l' : tList A | VΓ | VLA ]} :
  [Γ ||-v<i> tMap B C f (tMap A B g l') ≅ tMap A C (comp A f g) l' : tList C | VΓ | VLC].
Proof.
Admitted.

Lemma mapPropRedIdAux {Γ A i}
  {RA : [Γ ||-<i> A]}
  {LA : [Γ ||-List<i> tList A]}
  (LA' := normList0 LA : [Γ ||-List<i> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<i> tList A] )
  {RFAA : [Γ ||-<i> arr A A]}
  (Rid: [Γ ||-<i> (idterm A) : arr A A | RFAA]) :
  (forall l (Rx: ListRedTm _ _ LA' l),
      [Γ ||-<i> tMap A A (idterm A) (ListRedTm.nf Rx) ≅ l : tList A | RLA]) ×
   (forall l (Rx: ListProp _ _ LA' l),
       [Γ ||-<i> mapProp A A (idterm A) l Rx ≅ l : tList A | RLA]).
Proof.
  apply ListRedInduction.
  - intros.
    eapply transEqTerm; cycle 1.
    + eapply transEqTerm. 1: now eassumption.
      eapply LRTmEqSym.
      eapply redTmFwdConv; tea. 1: now econstructor.
      now eapply ListProp_whnf.
    + unshelve eapply mapRedAux; tea.
  - intros. eapply nilEqRed ; tea.
    + now escape.
    + eapply LRTyEqRefl_.
  - intros. eapply consEqRed.
    5: eassumption.
    all: try solve [ escape; tea | eapply LRTyEqRefl_ ].
    + eapply simple_appTerm; tea.
    + eapply redSubstTerm. 1: now irrelevance.
      apply redtm_id_beta.
      * escape ; tea.
      * unshelve eapply escapeEq ; tea.
        eapply LRTyEqRefl_.
      * unshelve eapply escapeTerm ; tea.
        irrelevance.
    + eapply transEqTerm. 2: now eassumption.
      now unshelve eapply mapRedAux.
    + unshelve eapply (fst (mapRedAux _)) ; tea.
      change [LRList' LA' | Γ ||- tl : _ ] in l.
      change [LRList' (normList0 LA') | Γ ||- tl : _ ].
      irrelevance.
    + change [LRList' LA' | Γ ||- tl : _ ] in l.
      eapply LRTmRedConv.
      2: eassumption.
      eapply listEqRed ; escape; tea.
      eapply LRTyEqRefl_.
  - intros.
    eapply neuTermEq.
    + apply tm_ne_map.
      1-2: now eapply reifyType.
      * now eapply reifyTerm.
      * now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
    + now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
    + eapply ty_map; escape; tea.
      now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
    + now match goal with H : [Γ ||-NeNf _ : tList _] |- _ => apply H end.
    + apply convneu_map_id. 1: now escape; tea.
      now eapply NeNf.refl.

    Unshelve.
    all: tea.
Qed.

Lemma mapRedIdValid {Γ A l' l i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {Vl : [Γ ||-v<i> l : tList A | VΓ | VLA ]}
  {Vl' : [Γ ||-v<i> l' : tList A | VΓ | VLA ]}
  {Vll' : [Γ ||-v<i> l ≅ l' : tList A | VΓ | VLA ]} :
  [Γ ||-v<i> tMap A A (idterm A) l ≅ l' : tList A | VΓ | VLA].
Proof.
  split; intros.
  instValid Vσ.
  cbn in *. change (tLambda _ _) with (idterm A[σ]).
  eapply transEqTerm. 2: eassumption.
  eapply transEqTerm; cycle 1.
  - unshelve epose (fst (mapPropRedIdAux _) _ _).
    10: irrelevance.
    all: tea.
    + now apply invLRList.
    + now apply ArrRedTy.
    + eapply idred.
    + change [normList RVLA | Δ ||- l[σ] : (tList A)[σ]].
      irrelevance.
  - fold subst_term.
    unshelve eapply mapRedAux ; tea.
    2: now unshelve eapply idred.
Qed.

End List.
