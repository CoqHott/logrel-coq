
From Coq Require Import ssrbool.
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
  - intros; now eapply wk.
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
  - intros. irrelevanceRefl; now unshelve eapply wkEq.
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

Lemma listEqTermRed@{h i j k l} {Δ A A'} (wfΔ : [|-Δ]) :
    [Δ ||-<one> A : U | LRU_@{i j k l} (redUOne wfΔ)] ->
    [Δ ||-<one> A' : U | LRU_@{i j k l} (redUOne wfΔ)] ->
    [Δ ||-<one> A ≅ A' : U | LRU_@{i j k l} (redUOne wfΔ)] ->
    [Δ ||-<one> tList A ≅ tList A' : U | LRU_@{i j k l} (redUOne wfΔ)].
Proof.
  unshelve econstructor; intros.
  - now eapply listTermRed.
  - now eapply listTermRed.
  (* - eapply listRed. *)
  - refine (LRCumulative@{Set l i j k l h i j k } _).
    eapply (listRed@{i j k l} (l:=zero)); tea.
    now eapply UnivEq'.
  - cbn. eapply convtm_list.
    now escape.
  - refine (LRCumulative@{Set l i j k l h i j k } _).
    eapply (listRed@{i j k l} (l:=zero)); tea.
    now eapply UnivEq'.
  - unshelve eapply (LRTyEqIrrelevantCum@{i j k l h i j k } _).
    3: { unshelve eapply (listEqRed (l:=zero)).
         + now eapply UnivEq.
         + unshelve eapply (escape (l:= zero)). now eapply UnivEq.
         + now eapply UnivEqEq.
    }
    now eapply listRed; eapply UnivEq.
Qed.


Lemma listCongTermValid@{h i j k l} {Γ A A'}
  (VΓ : [VR@{i j k l}| ||-v Γ]) :
  termValidity@{i j k l} Γ one A U VΓ (UValid@{i j k i j k l l} VΓ) ->
  termValidity@{i j k l} Γ one A' U VΓ (UValid@{i j k i j k l l} VΓ) ->
  termEqValidity@{i j k l} Γ one A A' U VΓ (UValid@{i j k i j k l l} VΓ) ->
  termEqValidity@{i j k l} Γ one (tList A) (tList A') U VΓ (UValid@{i j k i j k l l} VΓ).
Proof.
  constructor; intros.
  eapply listEqTermRed; refold.
  - instValid Vσ. eassumption.
  - instValid Vσ. eassumption.
  - instValid Vσ. eassumption.
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
  + unshelve eapply ListRedTm.nilR; [gen_typing|tea| irrelevance].
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
  + cbn. unshelve econstructor; tea. 1: gen_typing.
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


Lemma nilCongValid {Γ A A' l}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  {VA' : [Γ ||-v<l> A' | VΓ]}
  {VAA' : [Γ ||-v<l> A ≅ A' | VΓ | VA ]}
  {VLA : [Γ ||-v<l> tList A | VΓ]} :
  [Γ ||-v<l> tNil A ≅ tNil A' : tList A | VΓ | VLA].
Proof.
  split; intros.
  instValid Vσ.
  eapply nilEqRed; refold; tea.
  - now escape.
  - now escape.
  - eapply LRTyEqRefl_.
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
  + unshelve eapply ListRedTm.consR.
    * gen_typing.
    * escape ; tea.
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
  - unshelve econstructor; tea; cbn; try solve [ irrelevance | eapply LRTyEqRefl_ ].
    1: gen_typing.
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


Lemma consCongValid {Γ A A' hd hd' tl tl' l}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  {VA' : [Γ ||-v<l> A' | VΓ]}
  {VAA' : [Γ ||-v<l> A ≅ A' | VΓ | VA ]}
  {VLA : [Γ ||-v<l> tList A | VΓ]}
  {VLA' : [Γ ||-v<l> tList A' | VΓ]}
  (Vhd : [Γ ||-v<l> hd : A | VΓ | VA ])
  (Vhd' : [Γ ||-v<l> hd' : A' | VΓ | VA' ])
  (Vhdhd' : [Γ ||-v<l> hd ≅ hd' : A | VΓ | VA ])
  (Vtl : [Γ ||-v<l> tl : tList A | VΓ | VLA ])
  (Vtl' : [Γ ||-v<l> tl' : tList A' | VΓ | VLA' ])
  (Vtltl' : [Γ ||-v<l> tl ≅ tl' : tList A | VΓ | VLA ]) :
  [Γ ||-v<l> tCons A hd tl ≅ tCons A' hd' tl' : tList A | VΓ | VLA].
Proof.
  split; intros.
  instValid Vσ.
  eapply consEqRed; solve [ escape; tea | eapply LRTyEqRefl_].
Qed.

Definition mapProp {Γ L l} (A B f x: term) {LL : [Γ ||-List<l> L]} (p : ListProp _ _ LL x) : term.
Proof.
  destruct p as [  | | x ].
  - exact (tNil B).
  - exact (tCons B (tApp f hd) (tMap A B f tl)).
  - destruct (Map.into_view x) as [A' B' f' x'| y].
    + exact (tMap A' B (comp A' f f') x').
    + exact (tMap A B f y).
Defined.

Lemma instKripke {Γ A l} (wfΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]) : [Γ ||-<l> A].
Proof.
  specialize (h Γ wk_id wfΓ); now rewrite wk_id_ren_on in h.
Qed.

Lemma redfun_kripke_neutrals {Γ l A B f} 
  (RA : [Γ ||-<l> A])
  (RAB : [Γ ||-<l> arr A B])
  (RLB : [Γ ||-<l> tList B])
  (RLB' := (normList0 (invLRList RLB)))
  (Rf : [Γ ||-<l> f : _ | RAB])
  {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) n :
  [Δ |- n : A⟨ρ⟩] ->
  [Δ |- n ~ n : A⟨ρ⟩] ->
  [ListRedTyPack.parRed RLB' ρ wfΔ | Δ ||- tApp f⟨ρ⟩ n : _].
Proof.
  intros. eapply simple_appTerm.
  2: now eapply neuTerm.
  irrelevance0.
  2: now eapply wkTerm.
  now rewrite <- wk_arr.
  Unshelve. 3: tea. 2: apply ArrRedTy.
    all: eapply wk; tea.
    unshelve eapply instKripke.
    1: escape; gen_typing.
    intros. now eapply ListRedTy.parRed.
Qed.

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
  assert [Γ ||-<l> A]
    by (apply instKripke; [gen_typing| intros; now apply (ListRedTy.parRed LA')]).
  assert [Γ |- B ≅ B]
    by (unshelve eapply escapeEq; [|tea| eapply LRTyEqRefl_]).
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
      unshelve eapply escapeEq; tea.
      irrelevance.
  - intros.
    apply redSubstTerm.
    + unshelve eapply consRed; tea.
      * eapply LRTyEqRefl_.
      * eapply simple_appTerm; tea; try irrelevance.
        Unshelve. tea.
      * intuition.
    + eapply redtm_map_cons; tea.
      * unshelve eapply escapeEq; tea; irrelevance.
      * unshelve eapply escapeTerm; try irrelevance.
        2: tea.
      * change [LRList' LA' | Γ ||- tl : _ ] in l0.
        now eapply escapeTerm.

  - intros. cbn.
    destruct (Map.into_view l0) as [A' B' f' l'|l'].
    + assert (whne l') by 
        (eapply convneulist_whne_list in refl; inversion refl; tea; inv_whne).
      destruct tyconv; eapply redSubstTerm; cycle 1.
      1: eapply redtm_map_comp; tea.
      match goal with
      | [ |- [ LRAd.pack ?R | _ ||- ?t : _ ] ] => enough [normList R | _ ||- t : _] by irrelevance
      end.
      assert [Γ |- f : arr B' B]
        by (eapply ty_conv; tea; eapply convty_simple_arr; tea).
      assert [Γ |- comp A' f f' : arr A' B]
      by (eapply ty_comp; cycle 3; tea).
      pose (RB' := (fun Δ => ListRedTy.parRed (normList0 (invLRList RLB)) (Δ:=Δ))).
      assert (hcomp: forall Δ (ρ : Δ ≤ Γ) (wfΔ: [|- Δ]) n, 
        [Δ |- n : A'⟨ρ⟩] ->
        [Δ |- n ~ n : A'⟨ρ⟩] ->
        [RB' _ ρ wfΔ | _ ||- tApp f⟨ρ⟩ (tApp f'⟨ρ⟩ n) : _ ]
      ).
      1:{
        intros.
        unshelve eapply simple_appTerm; cycle 3.
        + irrelevance0.
          2: unshelve eapply wkTerm; cycle 3; tea.
          now rewrite <- wk_arr.
        + now unshelve eapply redfn.
        + eapply ArrRedTy; eapply wk; tea; gen_typing.
      }
      assert (RBwk : [Γ,, A' ||-<l> B⟨↑⟩])
       by (erewrite <- wk1_ren_on; eapply wk; tea; gen_typing).
      assert [RBwk | _ ||- tApp f⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : _ ].
      1:{ irrelevance0.
          2: erewrite <- 2!wk1_ren_on; eapply hcomp.
          all: rewrite wk1_ren_on; try easy.
          2: eapply convneu_var.
          1,2: now eapply ty_var0.
      }
      assert [Γ,, A' |-[ ta ] tApp f⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) ≅ tApp f⟨↑⟩ (tApp f'⟨↑⟩ (tRel 0)) : B⟨↑⟩].
      1:{
        unshelve eapply escapeEqTerm.
        3: now eapply LREqTermRefl_.
      }
      eapply neuListTerm.
      1: eapply ty_map; tea.
      * eapply convneulist_map; tea.
        eapply convtm_comp_app ; cycle 4; tea; gen_typing.
      * split; tea; intros.
        eapply redSubstTerm.
        1: now eapply hcomp.
        rewrite wk_comp.
        eapply redtm_comp_beta; tea.
        1-3: eapply wft_wk; tea.
        1,2: rewrite wk_arr; now eapply ty_wk.
        Unshelve. gen_typing.
    + enough [normList RLB | Γ ||- tMap A B f l' : tList B].
      1: split; [| eapply LREqTermRefl_ ]; irrelevance.
      assert [Γ |- A ≅ A]
       by (unshelve eapply escapeEq; tea; eapply LRTyEqRefl_).
      assert [Γ |- l' ~ l' : tList A].
      1:{ eapply convneulist_whne; tea.
        1,2: eapply whne_list_not_map; tea; now eapply convneulist_whne_list.
      }
      eapply neuListTerm.
      1: eapply ty_map; now escape.
      1: eapply convneulist_map; tea.
      2: split; tea.
      * unshelve eapply escapeEqTerm; try eapply LREqTermRefl_.
        2: erewrite <- wk1_ren_on; eapply wk; tea; gen_typing.
        unshelve eapply simple_appTerm.
        5: now eapply var0.
        3: irrelevance0.
        4: erewrite <- wk1_ren_on; now eapply wkTerm.
        3:now rewrite <- wk_arr, !wk1_ren_on.
        1: erewrite <- wk1_ren_on; eapply wk; gen_typing.
        apply ArrRedTy; erewrite <- wk1_ren_on; eapply wk; tea; gen_typing.
        Unshelve. gen_typing.
      * intros; now eapply redfun_kripke_neutrals.
Qed.

Lemma ListPropIrrelevance {Γ lA lA' A A' t} (wfΓ : [|- Γ])
  (LA : [Γ ||-List< lA > A]) (LA' : [Γ ||-List< lA' > A']) 
  (Rpar := instKripke wfΓ (fun Δ => ListRedTy.parRed LA (Δ:=Δ))):
  [Rpar | Γ ||- ListRedTy.par LA ≅ ListRedTy.par LA'] ->
  ListProp Γ A LA t -> ListProp Γ A' LA' t.
Proof.
  intros conv.
  apply ListIrrelevanceTm.
  1: escape; now eapply convty_list.
  1: now escape.
  intros; eapply LRIrrelevantPack; irrelevanceRefl; unshelve eapply wkEq; tea.
Defined.

Lemma ListRedTmIrrelevance {Γ lA lA' A A' t} (wfΓ : [|- Γ])
  (LA : [Γ ||-List< lA > A]) (LA' : [Γ ||-List< lA' > A']) 
  (Rpar := instKripke wfΓ (fun Δ => ListRedTy.parRed LA (Δ:=Δ))):
  [Rpar | Γ ||- ListRedTy.par LA ≅ ListRedTy.par LA'] ->
  [LRList' LA | Γ ||- t : A] -> [LRList' LA' | Γ ||- t : A'].
Proof.
  intros conv.
  apply ListIrrelevanceTm.
  1: escape; now eapply convty_list.
  1: now escape.
  intros; eapply LRIrrelevantPack; irrelevanceRefl; unshelve eapply wkEq; tea.
Defined.


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
        (* [ LRList' LA_ | _ ||- x : _ ] -> *)
        (* ListProp _ _ LA_ x -> *)
        (* [ LRList' LA_ | _ ||- x' : _ ] -> *)
        (* ListProp _ _ LA_ x' -> *)
        [Γ ||-<l> tMap A B f x ≅ tMap A' B' f' x' : tList B | RLB])
    ×
    (forall x x' (Rxx': ListPropEq _ _ LA_ x x'),
        [ LRList' LA_ | _ ||- x : _ ] ->
        ListProp _ _ LA_ x ->
        [ LRList' LA_ | _ ||- x' : _ ] ->
        ListProp _ _ LA_ x' ->
          [Γ ||-<l> tMap A B f x ≅ tMap A' B' f' x' : tList B | RLB]).
Proof.
  apply ListRedEqInduction.
  - intros.
    unshelve eapply LREqTermHelper.
    8: {
      apply X.
      - eapply redTmFwd. exact Rt.
        + destruct Rt. assumption.
        + eapply ListProp_whnf; destruct Rt. eassumption.
      - destruct Rt; assumption.
      - eapply redTmFwd. exact Ru.
        + destruct Ru. assumption.
        + eapply ListProp_whnf; destruct Ru. eassumption.
      - destruct Ru; assumption.
    }
    3: now unshelve eapply mapRedAux.
    4: eassumption. 1: eassumption.
    unshelve epose (Ru' := _ : ListRedTm Γ (tList A') LA'_ u).
    {
      unshelve eapply ListRedTmIrrelevance.
      6: tea.
      2: irrelevance.
      1: escape; gen_typing.
    }
    replace (ListRedTm.nf Ru) with (ListRedTm.nf Ru').
    2: destruct Ru; reflexivity.
    now unshelve eapply mapRedAux.
  - intros.
    unshelve eapply LREqTermHelper.
    7: eassumption.
    4:{ unshelve eapply mapRedAux ; tea.
        unshelve econstructor ; tea.
        irrelevance.
    }
    3:{ unshelve eapply mapRedAux ; tea.
        unshelve eapply ListRedTm.nilR; tea.
        unshelve eapply LRTransEq.
        5: eassumption.
        pose proof (ListRedTyEq.parRed (normListEq RLA RELA) wk_id wfΓ).
        unshelve eapply LRTyEqSym.
        3: irrelevance.
        2: now eapply (ListRedTy.parRed LA_).
    }
    1: tea.
    cbn. escape. eapply nilEqRed; tea.
    eapply LRTyEqRefl_.

  - intros. unshelve eapply LREqTermHelper.
    7: eassumption.
    4:{
      unshelve eapply (snd (mapRedAux _)); tea.
      econstructor; tea; (inversion X5; subst; [| eapply convneulist_whne_list in refl; inv_whne ]).
      + irrelevance.
      + irrelevance.
      + escape; unshelve eapply ListRedTmIrrelevance.
        3,6: tea. now eapply LRTyEqRefl_. Unshelve. tea.
    }
    3:{
      unshelve eapply (snd (mapRedAux _)); tea.
      eapply ListIrrelevanceTm.
      4: eassumption.
      1-2: now cbn; escape; tea.
      intros; eapply LRIrrelevantPack.
      pose proof (ListRedTyEq.parRed (normListEq RLA RELA) ρ wfΔ).
      irrelevance.
    }
    + eassumption.
    + cbn; inversion X5; subst;
      dependent inversion X7; subst; cbn.
      { eapply consEqRed. 3: eassumption.
        all: try solve [ escape ; tea | eapply LRTyEqRefl_ ].
        - unshelve eapply simple_appTerm; cycle 3; tea; irrelevance.
        - unshelve eapply simple_appTerm; cycle 3;  tea.
          eapply LRTmRedConv; tea. irrelevance.
        - unshelve eapply simple_appcongTerm; cycle 3; tea; irrelevance.
        - eapply (fst (mapRedAux _)); tea.
        - unshelve eapply (fst (mapRedAux _)); tea.
          change [LRList' (normList0 LA'_) | Γ ||- tl' : _ ].
          eapply LRTmRedConv; tea.
      }
      * unshelve epose proof (convneulist_whne_list _); cycle 4 ; tea ; inv_whne.
      * unshelve epose proof (convneulist_whne_list _); cycle 4 ; tea ; inv_whne.
      * unshelve epose proof (convneulist_whne_list _); cycle 4 ; tea ; inv_whne.
        Unshelve. all: tea.

  - intros.
    destruct (Map.into_view l0) as [Ap Bp fp lp|lp], (Map.into_view l') as [Ap' Bp' fp' lp'|lp']; cycle 3.
    + pose proof conv as ?%convneulist_whne.
      2,3: eapply whne_list_not_map; tea; eapply convneulist_whne_list; now symmetry + tea.
      enough [normList RLB | Γ ||- tMap A B f lp ≅ tMap A' B' f' lp' : tList B] by irrelevance.
      escape.  
      apply neuListTermEq.
      * now eapply ty_map.
      * eapply ty_conv. 2: now symmetry.
        eapply ty_map; tea.
        now eapply ty_conv.
      * eapply convneulist_map; tea.
        1: eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
        eapply escapeEqTerm.
        eapply simple_appcongTerm.
        4: eapply LREqTermRefl_.
        2-4: eapply var0; tea; reflexivity.
        irrelevance0.
        2: erewrite <- 2! wk1_ren_on; now eapply wkTermEq.
        now rewrite <- wk_arr, 2!wk1_ren_on.
        Unshelve.
        5: gen_typing.
        4: apply ArrRedTy.
        2-5: erewrite <- wk1_ren_on; eapply wk; tea; gen_typing.
      * split; tea; cbn.
        1-3: etransitivity; tea; now symmetry.
        intros. eapply redfun_kripke_neutrals; cycle 1; tea.
      * split; tea. 
        -- eapply ty_conv; tea.
        -- now eapply urefl.
        -- eapply convneu_conv; tea; now eapply urefl.
        -- intros; eapply LRTmRedConv.
          2: eapply redfun_kripke_neutrals; cycle 1; tea.
          cbn; eapply LRTyEqSym; now eapply wkEq.
          Unshelve. all: tea.
      * split; tea.
        admit.
    + eapply LREqTermHelper.
      1,2: unshelve eapply mapRedAux; tea; eapply ListPropIrrelevance; tea; cbn.
      2: irrelevance.
      1: eapply LRTyEqRefl_.
      1: tea.
      dependent inversion X0; cbn; dependent inversion X2; cbn.
      enough [normList RLB | Γ ||- tMap Ap B (comp Ap f fp) lp ≅ tMap Ap' B' (comp Ap' f' fp') lp' : tList B] by irrelevance.
      destruct tyconv, tyconv0, tyconv1; escape.
      eapply neuListTermEq.
      1,2,4,5: admit. (* duplicate of what happens in mapRedAux *)
      * eapply convneulist_map; cbn; tea.
        2: eapply ty_conv.
        1,2: eapply ty_comp.
        4: tea. 4: eapply ty_conv; [tea|].
        8: tea. 8: eapply ty_conv; [tea|].
        1-6: tea. 1,3,4: eapply convty_simple_arr; tea.
        1: now eapply lrefl. 
        1: cbn in wconvcod1; etransitivity; [|tea]; now symmetry.
        1: now symmetry.
        2: now eapply lrefl.
        2: tea.
        1: now symmetry.
        1: admit.
      * split; tea.
        1: admit.
    Unshelve. all: tea; escape; gen_typing.
    + admit.
    + admit.
Admitted.
(* Qed. *)

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
  + now apply ArrRedTy.
  + now apply ArrRedTy.
  + cbn. irrelevance.
  + cbn. irrelevance.
  + cbn. irrelevance.
  + cbn. change [normList RVLA | Δ ||- x[σ] ≅ x'[σ] : _].
    irrelevance.
Qed.

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
  unshelve epose (X := snd (mapRedAux _) (tNil A[σ]) _).
  12:{
    eapply ListRedTm.nilR.
    - escape. eassumption.
    - cbn. irrelevance0. 2:eapply LRTyEqRefl_.
      1: now rewrite wk_id_ren_on.
      Unshelve.
      1,3: tea.
  }
  10: now apply X.
  all: try solve [ tea | now apply invLRList ].
  + rewrite <- subst_arr. exact RVFAB.
  + irrelevance.
Qed.

Lemma mapRedConsValid {Γ A B f hd tl i}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<i> A | VΓ]}
  {VB : [Γ ||-v<i> B | VΓ]}
  {VLA : [Γ ||-v<i> tList A | VΓ]}
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VFAB : [Γ ||-v<i> arr A B | VΓ]}
  {Vhd : [Γ ||-v<i> hd : A | VΓ | VA ]}
  {Vcons : [Γ ||-v<i> tl : tList A | VΓ | VLA ]}
  {Vf : [Γ ||-v<i> f : arr A B | VΓ | VFAB ]} :
  [Γ ||-v<i> tMap A B f (tCons A hd tl) ≅ tCons B (tApp f hd) (tMap A B f tl) : tList B | VΓ | VLB].
Proof.
  split. intros.
  instValid Vσ.
  cbn.
  unshelve epose (X := snd (mapRedAux _) (tCons A[σ] hd[σ] tl[σ]) _).
  12:{
    eapply ListRedTm.consR.
    - now escape.
    - irrelevance0. 2:eapply LRTyEqRefl_.
      1: now rewrite wk_id_ren_on.
      Unshelve. 1,3: tea.
    - irrelevance. now rewrite wk_id_ren_on.
    - enough (X : [normList RVLA | Δ ||- tl[σ] : _]) by exact X.
      irrelevance.
  }
  8: now eapply X.
  all: tea.
  + rewrite <- subst_arr. exact RVFAB.
  + irrelevance.
Qed.

Definition ListProp_of_mapProp {Γ l} (A B f x: term)
  (RA: [Γ ||-<l> A])
  (RLA : [Γ ||-List<l> tList A])
  (RB: [Γ ||-<l> B])
  (RLB : [Γ ||-List<l> tList B])
  (RAB : [Γ ||-<l> arr A B ])
  (Rf: [RAB | Γ ||- f : arr A B])
  (p : ListProp _ _ (normList0 RLA) x) :
  ListProp _ _ (normList0 RLB) (mapProp A B f x p).
Proof.
  destruct p as [ | | x].
  - cbn. eapply ListRedTm.nilR. 1: now escape.
    irrelevance0. 2:eapply LRTyEqRefl_.
    now rewrite wk_id_ren_on.
    Unshelve. 1,3: tea.
  - cbn. eapply ListRedTm.consR. 1: now escape.
    + irrelevance0. 2:eapply LRTyEqRefl_.
      now rewrite wk_id_ren_on.
      Unshelve. 1,3: tea.
    + eapply simple_appTerm; tea.
      irrelevance0; tea. f_equal; now rewrite wk_id_ren_on.
      Unshelve. now rewrite 2!wk_id_ren_on.
    + change [LRList' (normList0 RLB) | Γ ||- tMap A B f tl : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
  - cbn; destruct (Map.into_view _).
    * admit. (* new case *)
    * constructor; cbn in *. 
      + eapply ty_map ; tea.
      1-3: now escape.
      + escape; eapply convneulist_map; tea.
        1-2: now unshelve eapply escapeEq ; solve [ eapply LRTyEqRefl_ | tea ].
        2: now eapply convneulist_is_not_map_convneu.
        (* The following lines should be stated as a lemma *)
        eapply escapeEqTerm; eapply LREqTermRefl_; eapply simple_appTerm.
        2: now eapply var0.
        irrelevance0. 2: erewrite <- wk1_ren_on; now eapply wkTerm.
        refold; now rewrite <- wk_arr, 2! wk1_ren_on.
        Unshelve. 4: eapply ArrRedTy.
        2-5: erewrite <- wk1_ren_on; eapply wk.
        2-10: tea; gen_typing.
        (* 2: now unshelve eapply escapeEqTerm ; solve [ now eapply LREqTermRefl_ | tea ].
        easy. *)
Admitted.
(* Defined. *)

Lemma mapPropRedCompAux {Γ A B C f g i}
  {RA : [Γ ||-<i> A]}
  {RB : [Γ ||-<i> B]}
  {RC : [Γ ||-<i> C]}
  {LA : [Γ ||-List<i> tList A]}
  (LA' := normList0 LA : [Γ ||-List<i> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<i> tList A] )
  {LB : [Γ ||-List<i> tList B]}
  (LB' := normList0 LB : [Γ ||-List<i> tList B])
  (RLB :=  LRList' LB' : [Γ ||-<i> tList B] )
  {LC : [Γ ||-List<i> tList C]}
  (LC' := normList0 LC : [Γ ||-List<i> tList C])
  (RLC :=  LRList' LC' : [Γ ||-<i> tList C] )
  {RFBC : [Γ ||-<i> arr B C]}
  {RFAB : [Γ ||-<i> arr A B]}
  {RFAC : [Γ ||-<i> arr A C]}
  (Rf: [Γ ||-<i> f : arr B C | RFBC])
  (Rg: [Γ ||-<i> g : arr A B | RFAB])
  (Rcomp: [Γ ||-<i> comp A f g : arr A C | RFAC]) :
  (forall l (Rx: ListRedTm _ _ LA' l),
      [Γ ||-<i> tMap B C f (tMap A B g (ListRedTm.nf Rx)) ≅ tMap A C (comp A f g) (ListRedTm.nf Rx) : tList C | RLC]) ×
   (forall l (Rx: ListProp _ _ LA' l),
       [Γ ||-<i> mapProp B C f _ (ListProp_of_mapProp A _ g _ RA LA RB LB _ Rg Rx) ≅ mapProp A C (comp A f g) l Rx : tList C | RLC]).
Proof.
  apply ListRedInduction.
  - intros.
    unshelve eapply LREqTermHelper.
    8: eassumption.
    5: apply LRTyEqRefl_.
    1: tea.
    + eapply transEqTerm; cycle 1.
      * unshelve eapply (snd (mapRedAux _)); tea.
      * unshelve eapply (fst (mapEqRedAux _ _)); tea.
        all: try solve [ eapply LRTyEqRefl_ | now eapply LREqTermRefl_ ].
        change [ LRList' (normList0 LB') | Γ ||-
                                  tMap A B g (ListRedTm.nf (Build_ListRedTm nf red eq prop))
                                  ≅
                                  mapProp A B g nf prop : _ ].
        unshelve eapply (snd (mapRedAux _)); tea.
    + unshelve eapply (snd (mapRedAux _)); tea.
  - intros. cbn.
    admit. (* Fix ListProp_of_mapProp *)
    (* change [ LRList' LC' | Γ ||- tNil C ≅ tNil C : _ ].
    unshelve eapply nilEqRed; tea; solve [ now escape | eapply LRTyEqRefl_ ]. *)
  - intros. cbn.
    admit. (* Fix ListProp_of_mapProp *)
    (* change [ LRList' LC' | Γ ||- tCons C (tApp f (tApp g hd)) (tMap B C f (tMap A B g tl)) ≅
                             tCons C (tApp (comp A f g) hd) (tMap A C (comp A f g) tl) : _ ].
    unshelve eapply consEqRed; try eapply LRTyEqRefl_; tea; try now escape.
    + eapply simple_appTerm; tea.
      eapply simple_appTerm; tea.
    + eapply simple_appTerm; tea.
    + eapply LRTmEqSym. eapply redSubstTerm.
      2: eapply redtm_comp_beta; escape; cycle 2; tea.
      2: now eapply escapeTerm.
      eapply simple_appTerm; tea.
      eapply simple_appTerm; tea.
    + eapply LREqTermHelper.
      4: irrelevance.
      3: eapply LRTyEqRefl_.
      2: now unshelve eapply (fst (mapRedAux _)); tea.
      unshelve eapply (fst (mapEqRedAux _ _)); tea.
      all: try solve [ eapply LRTyEqRefl_ | now eapply LREqTermRefl_ ].
      change [ LRList' (normList0 LB') | Γ ||- tMap A B g tl ≅ tMap A B g (ListRedTm.nf l) : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
    + unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LB') | Γ ||- tMap A B g tl : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LA') | Γ ||- tl : _ ].
      change [ LRList' LA' | Γ ||- tl : _ ] in l.
      irrelevance.
    + unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LA') | Γ ||- tl : _ ].
      change [ LRList' LA' | Γ ||- tl : _ ] in l.
      irrelevance. *)
  - intros. cbn.
    admit. (* Fix ListProp_of_mapProp *)
    (* change [ LRList' LC' | Γ ||- tMap B C f (tMap A B g l) ≅ tMap A C (comp A f g) l : _ ].
    eapply neuListTermEq.
    + eapply ty_map.
      1-3: now escape.
      eapply ty_map.
      1-3: now escape.
      easy.
    + eapply ty_map.
      1-2: now escape.
      * eapply ty_comp.
        4-5: escape; tea. all: now escape.
      * easy.
    + eapply convneulist_map_comp ; tea.
      1-3: now eapply escape.
      all: now eapply escapeTerm.

      Unshelve.
      all: tea. *)
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
  {VFAB : [Γ ||-v<i> arr A B | VΓ]}
  {VFAC : [Γ ||-v<i> arr A C | VΓ]}
  {Vf : [Γ ||-v<i> f : arr B C | VΓ | VFBC ]}
  {Vg : [Γ ||-v<i> g : arr A B | VΓ | VFAB ]}
  {Vl : [Γ ||-v<i> l : tList A | VΓ | VLA ]}
  {Vl' : [Γ ||-v<i> l' : tList A | VΓ | VLA ]}
  {Vll' : [Γ ||-v<i> l ≅ l' : tList A | VΓ | VLA ]} :
  [Γ ||-v<i> tMap B C f (tMap A B g l) ≅ tMap A C (comp A f g) l' : tList C | VΓ | VLC].
Proof.
  split; intros.
  instValid Vσ.
  assert (Rx : [normList (validTy VLA wfΔ Vσ) | Δ ||- l'[σ] : tList A[σ]]) by irrelevance; refold.
  unshelve eapply LREqTermHelper.
  8:{
    epose (fst (mapPropRedCompAux _ _ _) _ Rx).
    irrelevance.
  }
  all: refold.
  5: eapply LRTyEqRefl_.
  1: eassumption.
  - cbn.
    unshelve eapply (fst (mapEqRedAux _ _)).
    all: try solve [ now eapply LRTyEqRefl_ ].
    all: try solve [ tea | eapply invLRList; tea | now eapply ArrRedTy ].
    + irrelevance. apply subst_arr.
    + clear Rx. irrelevance.
    + eapply LREqTermRefl_. irrelevance. apply subst_arr.
    + enough (X : [ normList RVLB | Δ ||- tMap A[σ] B[σ] g[σ] l[σ] ≅ tMap A[σ] B[σ] g[σ] (ListRedTm.nf Rx) : _ ]) by exact X; refold.
      eapply transEqTerm.
      2: {
        unshelve eapply (fst (mapRedAux _)); tea.
        - rewrite subst_arr in *; tea.
        - cbn. irrelevance.
      }
      unshelve eapply (fst (mapEqRedAux _ _)); tea.
      all: try solve [ eapply LRTyEqRefl_
                     | eapply invLRList; tea
                     | rewrite subst_arr in *; tea
                     |  try eapply LREqTermRefl_; irrelevance
             ].
      change [ normList RVLA | Δ ||- l[σ] ≅ l'[σ] : _ ].
      irrelevance.
  - cbn.
    (* TODO: lemma + rewrite *)
    replace (tLambda A[σ] (tApp f⟨↑⟩[up_term_term σ] (tApp g⟨↑⟩[up_term_term σ] (tRel var_zero))))
      with (comp A[σ] f[σ] g[σ]) by now asimpl.
    cbn.
    unshelve eapply (fst (mapRedAux _)); tea; refold.
    + rewrite subst_arr in *; tea.
    + irrelevanceRefl.
      eapply compred.
      1-2: irrelevance; eapply subst_arr.

      Unshelve.
      all: tea.
      all: try eapply invLRList; tea.
      all: try rewrite subst_arr in *; tea.
      1-3: cbn; try irrelevance.
      irrelevanceRefl. eapply compred.
      1-2: irrelevance; eapply subst_arr.

      Unshelve.
      all: tea.
Qed.

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
    + irrelevance. Unshelve. tea.
  - intros. eapply consEqRed.
    5: eassumption.
    all: try solve [ escape; tea | eapply LRTyEqRefl_ ].
    + rewrite wk_id_ren_on; eapply LRTyEqRefl_.
    + eapply simple_appTerm; tea. irrelevance.
      Unshelve. 2: rewrite wk_id_ren_on. all: tea.
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
      eapply listEqRed ; escape; rewrite wk_id_ren_on; tea.
      eapply LRTyEqRefl_.
  - intros. cbn. destruct (Map.into_view _).
    * admit. (* new case*)
    * eapply neuListTermEq.
      + eapply ty_map; escape; tea.
      + eassumption. 
      + escape; eapply convneulist_map_id; tea.
        1,2: eapply escapeEq; eapply LRTyEqRefl_.
        1: admit. (* there should be a lemma somewhere on the evaluation of id *)
        now eapply convneulist_is_not_map_convneu.
      Unshelve.
      all: tea.
Admitted.

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