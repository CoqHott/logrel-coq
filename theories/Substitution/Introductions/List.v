
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
  (AA' : [Γ |- A ≅ A'])
  (RLA: [Γ ||-< l > tList A]) :
  [Γ ||-<l> tNil A' : tList A | normList RLA].
Proof.
  econstructor.
  + eapply redtmwf_refl. eapply ty_conv. 1: now apply ty_nil.
    eapply convty_list. symmetry. now escape.
  + eapply convtm_conv.
    * eapply convtm_nil. etransitivity; tea; now symmetry.
    * symmetry. eapply convty_list; now cbn.
  + escape; unshelve eapply ListRedTm.nilR; cbn; gen_typing.
Defined.

Lemma nilRed {Γ A A' l}
  (RA: [Γ ||-< l > A])
  (wtyA' : [Γ |- A'])
  (RAA' : [Γ ||-< l > A ≅ A' | RA])
  (RLA: [Γ ||-< l > tList A]) :
  [Γ ||-<l> tNil A' : tList A | RLA].
Proof.
  enough [ normList RLA | Γ ||- tNil A' : _] by irrelevance.
  escape; now eapply nilRed'.
Defined.

Lemma nilEqRed {Γ A A' B l}
  (RB: [Γ ||-< l > B])
  (wtyA : [Γ |- A])
  (wtyA' : [Γ |- A'])
  (RLB: [Γ ||-< l > tList B]) :
  [Γ |- B ≅ A] ->
  [Γ |- B ≅ A'] ->
  [RLB | Γ ||- tNil A ≅ tNil A' : tList B].
Proof.
  intros. escape.
  enough [normList RLB | Γ ||- tNil A ≅ tNil A' : _] by irrelevance.
  unshelve econstructor.
  + change [ normList RLB | Γ ||- tNil A : _].
    eapply nilRed' ; tea.
  + change [ normList RLB | Γ ||- tNil A' : _].
    eapply nilRed' ; tea.
  + cbn. eapply convtm_conv.
    1: eapply convtm_nil; etransitivity; tea; now symmetry. 
    eapply convty_list; symmetry; tea.
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
    eapply nilEqRed; refold; escape; tea.
    unshelve eapply escapeEq; cycle 1; tea; apply LRTyEqRefl_.
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
  eapply nilEqRed; refold; escape; tea.
  unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
Qed.

Lemma consRed' {Γ A A' hd tl l}
  (RA: [Γ ||-< l > A])
  (wtyA' : [Γ |- A'])
  (AA' : [Γ |- A ≅ A'])
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
    * etransitivity; tea; now symmetry. 
    * eapply convtm_conv. 2: now escape.
      eapply escapeEqTerm ; tea.
      now apply LREqTermRefl_.
    * eapply convtm_conv. 2: (eapply convty_list; now escape).
      eapply escapeEqTerm ; tea.
      now apply LREqTermRefl_.
  + unshelve eapply ListRedTm.consR.
    * gen_typing.
    * escape ; tea.
    * cbn; now escape.
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
  escape; now eapply consRed'.
Qed.

Lemma consEqRed {Γ A A' P P' hd hd' tl tl' l}
  (RA: [Γ ||-< l > A])
  (RA': [Γ ||-< l > A'])
  (RLA: [Γ ||-< l > tList A])
  (RLA': [Γ ||-< l > tList A']) :
  [Γ |- P] ->
  [Γ |- P'] ->
  [RA | Γ ||- A ≅ A'] ->
  [Γ |- A ≅ P] ->
  [Γ |- A' ≅ P'] ->
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
    + etransitivity; tea.
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
    1: now etransitivity.
    change [normList RLA | Γ ||- tl ≅ tl' : tList A].
    irrelevance.
    Unshelve. tea.
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
    all: unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
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
  eapply consEqRed; solve [ escape; tea | unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_].
Qed.

Definition mapProp {Γ L l} (A B f x: term) {LL : [Γ ||-List<l> L]} (p : ListProp _ _ LL x) : term.
Proof.
  destruct p as [  | | x ].
  - exact (tNil B).
  - exact (tCons B (tApp f hd) (tMap A B f tl)).
  - clear ty refl tyconv. destruct (Map.into_view x) as [A' B' f' x'| y].
    + exact (tMap A' B (comp A' f f') x').
    + exact (tMap A B f y).
Defined.

Lemma instKripke {Γ A l} (wfΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩]) : [Γ ||-<l> A].
Proof.
  specialize (h Γ wk_id wfΓ); now rewrite wk_id_ren_on in h.
Qed.


Section FunctionLemmas.
  Context {Γ l A B f}
    (RA : [Γ ||-<l> A])
    (RAB : [Γ ||-<l> arr A B])
    (RLB : [Γ ||-List<l> tList B])
    (RLB' := (normList0 RLB))
    (Rpar := fun Δ => ListRedTy.parRed RLB' (Δ := Δ))
    (Rf : [Γ ||-<l> f : _ | RAB]).

  Definition kripke_neutral_app X {Y} g (RY : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> Y⟨ρ⟩]) :=
   forall [Δ] (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) n,
    [Δ |- n : X⟨ρ⟩] ->
    [Δ |- n ~ n : X⟨ρ⟩] ->
    [RY ρ wfΔ | Δ ||- tApp g⟨ρ⟩ n : _].

  Definition kripke_neutral_app_eq X {Y} g g' (RY : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> Y⟨ρ⟩]) :=
   forall [Δ] (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) n,
    [Δ |- n : X⟨ρ⟩] ->
    [Δ |- n ~ n : X⟨ρ⟩] ->
    [RY ρ wfΔ | Δ ||- tApp g⟨ρ⟩ n ≅ tApp g'⟨ρ⟩ n : _].

  Lemma redfun_kripke_neutrals : kripke_neutral_app A f Rpar.
  Proof.
    red. intros. eapply simple_appTerm.
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

  Lemma redfun_postcomp_kripke {X g} (RAwk : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩]) :
    kripke_neutral_app X g RAwk ->
    forall [Δ] (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) n,
      [Δ |- n : X⟨ρ⟩] ->
      [Δ |- n ~ n : X⟨ρ⟩] ->
      [Rpar _ ρ wfΔ | Δ ||- tApp f⟨ρ⟩ (tApp g⟨ρ⟩ n) : _].
  Proof.
    intros redfn **.
    unshelve eapply simple_appTerm; cycle 3.
    + irrelevance0.
      2: unshelve eapply wkTerm; cycle 3; tea.
      now rewrite <- wk_arr.
    + now unshelve eapply redfn.
    + eapply ArrRedTy; eapply wk; tea.
      eapply instKripke.
      1: escape; gen_typing.
      exact Rpar.
  Qed.

  Lemma redfun_comp_kripke {X g} (RAwk : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩]) :
    [Γ |- X] ->
    [Γ |- g : arr X A] ->
    kripke_neutral_app X g RAwk ->
    kripke_neutral_app X (comp X f g) Rpar.
  Proof.
    intros ?? redfn; red; intros **.
    assert (wfΓ : [|- Γ]) by gen_typing.
    pose proof (h := instKripke wfΓ Rpar); cbn in h.
    escape.
    eapply redSubstTerm.
    2: rewrite wk_comp; eapply redtm_comp_beta; cbn; tea.
    5,6: erewrite wk_arr; now eapply ty_wk.
    2-4: gen_typing.
    now eapply redfun_postcomp_kripke.
  Qed.

  Context {f'} (Rff' : [Γ ||-<l> f ≅ f' : _ | RAB]).

  Lemma redconvfun_kripke_neutrals : kripke_neutral_app_eq A f f' Rpar.
  Proof.
    red; intros.
    eapply simple_appcongTerm.
    2-3: now eapply neuTerm.
    2: now eapply neuTermEq.
    irrelevance0.
    2: now eapply wkTermEq.
    now rewrite <- wk_arr.
    Unshelve. 3: tea. 2: apply ArrRedTy.
      all: eapply wk; tea.
      unshelve eapply instKripke.
      1: escape; gen_typing.
      intros. now eapply ListRedTy.parRed.
  Qed.

  Lemma kripke_neutral_app_conv {X X' A' g}
    (RA' : [Γ ||-<l> A'])
    (RAA' : [Γ ||-<l> A ≅ A' | RA])
    (RAwk : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A'⟨ρ⟩])
    (RAwk' : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩]) :
    [Γ |- X ≅ X'] ->
    kripke_neutral_app X g RAwk ->
    kripke_neutral_app X' g RAwk'.
  Proof.
    intros ? redg; red; intros.
    eapply LRTmRedConv.
    2: eapply redg; eapply ty_conv + eapply convneu_conv; tea.
    2,3: eapply convty_wk; tea; now symmetry.
    irrelevanceRefl; eapply wkEq; now eapply LRTyEqSym.
    Unshelve. all: tea.
  Qed.

  Context {A' B'}
    (RA' : [Γ ||-<l> A'])
    (RAA' : [Γ ||-<l> A ≅ A' | RA])
    (RAB' : [Γ ||-<l> arr A' B'])
    (Rf' : [Γ ||-<l> f' : _ | RAB']).

  Lemma redconvfun_postcomp_kripke {X X' g g'}
    (RAwk : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩])
    (RAwk' : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A'⟨ρ⟩]) :
    [Γ |- X ≅ X'] ->
    kripke_neutral_app X g RAwk ->
    kripke_neutral_app X' g' RAwk' ->
    kripke_neutral_app_eq X g g' RAwk ->
    forall [Δ] (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) n,
      [Δ |- n : X⟨ρ⟩] ->
      [Δ |- n ~ n : X⟨ρ⟩] ->
      [Rpar _ ρ wfΔ | Δ ||- tApp f⟨ρ⟩ (tApp g⟨ρ⟩ n) ≅ tApp f'⟨ρ⟩ (tApp g'⟨ρ⟩ n) : _].
  Proof.
    intros ? redg redg' redgg' **.
    assert (wfΓ : [|- Γ]) by gen_typing.
    pose proof (h := instKripke wfΓ Rpar); cbn in h.
    eapply simple_appcongTerm.
    2: now eapply redg.
    2: eapply kripke_neutral_app_conv; cycle 3; tea.
    2: now symmetry.
    1: irrelevance0; [|now eapply wkTermEq]; now rewrite wk_arr.
    irrelevance0.
    2: now eapply redgg'.
    reflexivity.
    Unshelve. all: tea.
    eapply ArrRedTy; eapply wk; tea.
  Qed.
End FunctionLemmas.


Lemma redconvfun_comp_kripke {Γ l A B f}
  (RA : [Γ ||-<l> A])
  (RAB : [Γ ||-<l> arr A B])
  (RLB : [Γ ||-List<l> tList B])
  (RLB_ := (normList0 RLB))
  (Rpar := fun Δ => ListRedTy.parRed RLB_ (Δ := Δ))
  (Rf : [Γ ||-<l> f : _ | RAB])
  {f'} (Rff' : [Γ ||-<l> f ≅ f' : _ | RAB])
  {A' B'}
  (RA' : [Γ ||-<l> A'])
  (RAA' : [Γ ||-<l> A ≅ A' | RA])
  (RAB' : [Γ ||-<l> arr A' B'])
  (Rf' : [Γ ||-<l> f' : _ | RAB'])
  (RB : [Γ ||-<l> B])
  (RB' : [Γ ||-<l> B'])
  (RLB' : [Γ ||-List<l> tList B'])
  (RBB' : [Γ ||-<l> B ≅ B' | RB])
  {X X' g g'}
  (RAwk : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A⟨ρ⟩])
  (RAwk' : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), [Δ ||-<l> A'⟨ρ⟩]) :
  [Γ |- X] ->
  [Γ |- X'] ->
  [Γ |- X ≅ X'] ->
  [Γ |- g : arr X A] ->
  [Γ |- g' : arr X' A'] ->
  kripke_neutral_app X g RAwk ->
  kripke_neutral_app X' g' RAwk' ->
  kripke_neutral_app_eq X g g' RAwk ->
  kripke_neutral_app_eq X (comp X f g) (comp X' f' g') Rpar.
Proof.
  intros; red; intros **.
  assert (wfΓ : [|- Γ]) by gen_typing.
  pose proof (h := instKripke wfΓ Rpar); cbn in h.
  assert [Γ |- X ≅ X] by now eapply lrefl.
  escape.
  assert [Γ |- g' : arr X A'] by (eapply ty_conv; tea; eapply convty_simple_arr; tea; [now symmetry| now eapply urefl]).
  eapply LREqTermHelper.
  1,2: eapply redSubstTerm; [|rewrite wk_comp; eapply redtm_comp_beta; cbn; tea].
  5,6,11,12: erewrite wk_arr; now eapply ty_wk.
  2-4,6-8: gen_typing.
  4: cbn;irrelevanceRefl; now eapply wkEq.
  3: eapply ty_conv; tea; now eapply convty_wk.
  + eapply redfun_postcomp_kripke; cycle 1; tea.
  + eapply redfun_postcomp_kripke; cycle 1; tea.
    1: eapply ty_conv; tea.
    2: eapply convneu_conv; tea.
    all: now eapply convty_wk.
    Unshelve. all: tea.
  + eapply redconvfun_postcomp_kripke.
    1,5,6,7,8,9: tea.
    all: tea.
  Qed.


Lemma eta_expand_redfuneq {Γ A B f f' l}
  {RA : [Γ ||-<l> A]}
  {RB : [Γ ||-<l> B]}
  {RFAB : [Γ ||-<l> arr A B]}
  (Rf: [Γ ||-<l> f ≅ f' : arr A B | RFAB])  :
  [Γ,, A |-[ ta ] tApp f⟨↑⟩ (tRel 0) ≅ tApp f'⟨↑⟩ (tRel 0) : B⟨↑⟩].
Proof.
  escape; unshelve eapply escapeEqTerm.
  2: erewrite <- wk1_ren_on; eapply wk; tea; gen_typing.
  eapply simple_appcongTerm.
  4: eapply LREqTermRefl_.
  2-4: eapply var0; tea; reflexivity.
  irrelevance0.
  2: erewrite <- 2! wk1_ren_on; now eapply wkTermEq.
  now rewrite <- wk_arr, 2!wk1_ren_on.
  Unshelve.
  2: apply ArrRedTy.
  1-3: erewrite <- wk1_ren_on; eapply wk; tea.
  all: gen_typing.
Qed.

Lemma eta_expand_redfun {Γ A B f l}
  {RA : [Γ ||-<l> A]}
  {RB : [Γ ||-<l> B]}
  {RFAB : [Γ ||-<l> arr A B]}
  (Rf: [Γ ||-<l> f : arr A B | RFAB])  :
  [Γ,, A |-[ ta ] tApp f⟨↑⟩ (tRel 0) ≅ tApp f⟨↑⟩ (tRel 0) : B⟨↑⟩].
Proof.
  unshelve eapply eta_expand_redfuneq; cycle 1; tea.
  now eapply LREqTermRefl_.
Qed.



Lemma mapCompRedAux {Γ A B f l A' B' f' l'}
  {RA : [Γ ||-<l> A]}
  {RB : [Γ ||-<l> B]}
  {LA : [Γ ||-List<l> tList A]}
  (LA' := normList0 LA : [Γ ||-List<l> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<l> tList A] )
  {RLB : [Γ ||-List<l> tList B]}
  (RLB' := (normList0 RLB))
  {RFAB : [Γ ||-<l> arr A B]}
  (Rf: [Γ ||-<l> f : arr A B | RFAB])  :
  [Γ |- tMap A' B' f' l' : tList (ListRedTyPack.par LA')] ->
  [Γ |- tMap A' B' f' l' ~ tMap A' B' f' l' :List ListRedTyPack.par LA'] ->
  ListRedTm.map_inv LA' (tMap A' B' f' l') ->
  whne l' ->
  [Γ |-[ ta ] tMap A' B (comp A' f f') l' : tList B] ×
  [Γ |-[ ta ] tMap A' B (comp A' f f') l' ~ tMap A' B (comp A' f f') l' :List B ] ×
  ListRedTm.map_inv RLB' (tMap A' B (comp A' f f') l').
Proof.
  intros ty refl [] whl'. escape.
  cbn in *.
  assert [Γ |- B ≅ B]
    by (unshelve eapply escapeEq; [|tea| eapply LRTyEqRefl_]).
  assert [Γ |- f : arr B' B]
    by (eapply ty_conv; tea; eapply convty_simple_arr; tea).
  assert [Γ |- comp A' f f' : arr A' B]
  by (eapply ty_comp; cycle 3; tea).
  pose (RB' := (fun Δ => ListRedTy.parRed (normList0 RLB) (Δ:=Δ))).
  pose proof (hcomp := redfun_postcomp_kripke RA RFAB RLB Rf _ redfn).
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
  split; [|split].
  * eapply ty_map; tea.
  * eapply convneulist_map; tea.
    eapply convtm_comp_app ; cycle 4; tea; gen_typing.
  * split; tea; intros.
    eapply redfun_comp_kripke; cycle 1; tea.
    eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
  Unshelve. gen_typing.
Qed.

Lemma mapCompProp {Γ A B f l A' B' f' l'}
  {RA : [Γ ||-<l> A]}
  {RB : [Γ ||-<l> B]}
  {LA : [Γ ||-List<l> tList A]}
  (LA' := normList0 LA : [Γ ||-List<l> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<l> tList A] )
  {RLB : [Γ ||-List<l> tList B]}
  (RLB' := (normList0 RLB))
  {RFAB : [Γ ||-<l> arr A B]}
  (Rf: [Γ ||-<l> f : arr A B | RFAB])  :
  [Γ |- tMap A' B' f' l' : tList (ListRedTyPack.par LA')] ->
  [Γ |- tMap A' B' f' l' ~ tMap A' B' f' l' :List ListRedTyPack.par LA'] ->
  ListRedTm.map_inv LA' (tMap A' B' f' l') ->
  whne l' ->
  ListRedTm.ListProp _ _ RLB'  (tMap A' B (comp A' f f') l').
Proof.
  intros.
  edestruct @mapCompRedAux as [? []].
  8: econstructor; tea.
  all: cycle 3; tea.
Qed.

Lemma mapCompRed {Γ A B f l A' B' f' l'}
  {RA : [Γ ||-<l> A]}
  {RB : [Γ ||-<l> B]}
  {LA : [Γ ||-List<l> tList A]}
  (LA' := normList0 LA : [Γ ||-List<l> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<l> tList A] )
  {RLB : [Γ ||-<l> tList B]}
  {RFAB : [Γ ||-<l> arr A B]}
  (Rf: [Γ ||-<l> f : arr A B | RFAB])  :
  [Γ |- tMap A' B' f' l' : tList (ListRedTyPack.par LA')] ->
  [Γ |- tMap A' B' f' l' ~ tMap A' B' f' l' :List ListRedTyPack.par LA'] ->
  ListRedTm.map_inv LA' (tMap A' B' f' l') ->
  whne l' ->
  [RLB | Γ ||- tMap A' B (comp A' f f') l' : tList B].
Proof.
  intros.
  match goal with
  | [ |- [ LRAd.pack ?R | _ ||- ?t : _ ] ] => enough [normList R | _ ||- t : _] by irrelevance
  end.
  edestruct @mapCompRedAux as [? []].
  8: eapply neuListTerm; tea.
  all: cycle 3; tea.
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
  - intros.
    apply redSubstTerm.
    + unshelve eapply consRed; tea.
      * eapply LRTyEqRefl_.
      * eapply simple_appTerm; tea; try irrelevance.
        Unshelve. tea.
      * intuition.
    + eapply redtm_map_cons; tea.
      * unshelve eapply escapeTerm; try irrelevance.
        2: tea.
      * change [LRList' LA' | Γ ||- tl : _ ] in l0.
        now eapply escapeTerm.

  - intros. cbn.
    destruct (Map.into_view l0) as [A' B' f' l'|l'].
    + assert (whne l') by
        (eapply convneulist_whne_list in refl; inversion refl; tea; inv_whne).
      eapply redSubstTerm; cycle 1.
      1: destruct tyconv; eapply redtm_map_comp; tea.
      unshelve eapply mapCompRed; cycle 6; tea.
    + enough [normList RLB | Γ ||- tMap A B f l' : tList B].
      1: split; [| eapply LREqTermRefl_ ]; irrelevance.
      assert [Γ |- A ≅ A]
       by (unshelve eapply escapeEq; tea; eapply LRTyEqRefl_).
      assert [Γ |- l' ~ l' : tList A] by now eapply convneulist_is_not_map_convneu.
      eapply neuListTerm.
      1: eapply ty_map; now escape.
      1: eapply convneulist_map; tea.
      2: split; tea.
      * unshelve eapply eta_expand_redfun; cycle 4; tea.
      * intros; eapply redfun_kripke_neutrals; cycle 1; tea.
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

Lemma ListRedTm_map_inv_conv {Γ X X' l A B f r}
  (wfΓ : [|- Γ])
  (RX : [Γ ||-List<l> X])
  (RX' : [Γ ||-List<l> X'])
  (RXX' : [Γ ||-<l> ListRedTy.par RX ≅ ListRedTy.par RX' |  instKripke wfΓ (fun Δ =>ListRedTy.parRed RX (Δ:=Δ))]) :
  ListRedTm.map_inv RX (tMap A B f r) -> ListRedTm.map_inv RX' (tMap A B f r).
Proof.
  escape.
  intros [??????? redfn]; split; tea.
  1: etransitivity; tea; now symmetry.
  intros; eapply LRTmRedConv.
  2: now eapply redfn.
  cbn.  irrelevanceRefl.
  now eapply wkEq.
  Unshelve. all: tea.
Qed.

From LogRel Require Import UntypedReduction.

Lemma mapCompEqRedAux {Γ A Ap A' Ap' B Bp B' Bp' f fp f' fp' r r' l}
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
  {Rff': [Γ ||-<l> f ≅ f' : arr A B | RFAB]} :
  [Γ |- tMap Ap Bp fp r : tList (ListRedTyPack.par LA_)] ->
  [Γ |- tMap Ap' Bp' fp' r' : tList (ListRedTyPack.par LA'_)] ->
  ListRedTm.map_inv LA_ (tMap Ap Bp fp r) ->
  ListRedTm.map_inv LA'_ (tMap Ap' Bp' fp' r') ->
  whne r ->
  whne r' ->
  [Γ |- tMap Ap Bp fp r ~ tMap Ap Bp fp r :List ListRedTyPack.par LA_] ->
  [Γ |- tMap Ap' Bp' fp' r' ~ tMap Ap' Bp' fp' r' :List ListRedTyPack.par LA'_] ->
  [Γ |- tMap Ap Bp fp r ~ tMap Ap' Bp' fp' r' :List ListRedTyPack.par LA_] ->
  ListRedTmEq.map_inv_eq LA_ (tMap Ap Bp fp r) (tMap Ap' Bp' fp' r') ->
  ListProp Γ (tList A) LA_ (tMap Ap Bp fp r) ->
  ListProp Γ (tList A') LA'_ (tMap Ap' Bp' fp' r') ->
  [RLB | Γ ||- tMap Ap B (comp Ap f fp) r ≅ tMap Ap' B' (comp Ap' f' fp') r' : tList B].
Proof.
  assert [|- Γ ] by (escape; gen_typing).
  intros tymap tymap' hinv hinv' wh wh' convrefl convrefl' tyconv hinveq hprop hprop'.
  enough [normList RLB | Γ ||- tMap Ap B (comp Ap f fp) r ≅ tMap Ap' B' (comp Ap' f' fp') r' : tList B] by irrelevance.
  unshelve epose proof (mapCompRedAux Rf tymap convrefl hinv wh) as [? []]; tea; [now eapply invLRList|].
  unshelve epose proof (mapCompRedAux Rf' tymap' convrefl' hinv' wh') as [? []]; tea; [now eapply invLRList|].
  destruct hinv, hinv', hinveq; escape.
  pose (RAwk := fun Δ => ListRedTy.parRed LA_ (Δ:=Δ)).
  pose (RLB_ := (normList0 (invLRList RLB))).
  assert (convredfn' : kripke_neutral_app_eq Ap fp fp' RAwk).
  1:{
    red; intros; irrelevanceRefl.
    now eapply convredfn.
    Unshelve. tea.
  }
  unshelve epose proof (hcomp := redconvfun_comp_kripke RA RFAB (invLRList RLB) Rf Rff' RA' REA RFAB' Rf' RB RB' (invLRList RLB') REB _ _ _ _ _ _ _ redfn redfn0 convredfn'); tea.
  1,2: eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
  eapply neuListTermEq; tea.
  * now eapply ty_conv.
  * eapply convneulist_map; cbn; tea.
    2: eapply ty_conv.
    1,2: eapply ty_comp.
    4: tea. 4: eapply ty_conv; [tea|].
    8: tea. 8: eapply ty_conv; [tea|].
    1-6: tea. 1,3,4: eapply convty_simple_arr; tea.
    1: now eapply lrefl.
    1,2: now symmetry.
    1: now eapply lrefl.
    1: tea.
    unshelve epose proof (hcomp0 := hcomp _ (@wk1 Γ Ap) _ (tRel 0) _ _); tea.
    1: gen_typing.
    2: eapply convneu_var.
    1,2: rewrite wk1_ren_on; now eapply ty_var0.
    eapply escapeEqTerm in hcomp0.
    rewrite !wk1_ren_on in hcomp0.
    exact hcomp0.
  * eapply ListRedTm_map_inv_conv; tea.
    eapply LRTyEqSym; irrelevance.
    Unshelve. 1,3: tea.
  * split; tea.
Qed.

Lemma not_map_is_not_Map {l} (p : ~~Map.is_map l) : Map.into_view l = Map.IsNotMap p.
Proof.
  destruct l; try discriminate p; cbn; f_equal.
  all: rewrite (Eqdep_dec.UIP_refl_bool true is_true_true), (Eqdep_dec.UIP_refl_bool true p); reflexivity.
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
  assert [|-Γ] by (escape; gen_typing).
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
    assert (eqPar : ListRedTyPack.par LA_ = A).
    1:{ destruct LA as [? red]; pose proof (e := redtywf_whnf red whnf_tList); injection e; now intros ->. }
    unshelve eapply LREqTermHelper.
    7: eassumption.
    4:{ unshelve eapply mapRedAux ; tea.
        unshelve econstructor ; tea.
    }
    3:{ unshelve eapply mapRedAux ; tea.
        unshelve eapply ListRedTm.nilR; tea.
        etransitivity; cbn; tea; rewrite eqPar; symmetry; now escape.
    }
    1: tea.
    cbn. escape. eapply nilEqRed; tea.
    etransitivity; tea; now symmetry.

  - intros. unshelve eapply LREqTermHelper.
    7: eassumption.
    4:{
      unshelve eapply (snd (mapRedAux _)); tea.
      econstructor; tea; (inversion X3; subst; [| eapply convneulist_whne_list in refl; do 2 inv_whne ]).
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
    + cbn; dependent inversion X5; subst; cbn; inversion X3; subst; cbn.
      * {
        eapply consEqRed. 3: eassumption.
        all: try (escape; solve [ tea | etransitivity; tea; now symmetry ]).
        - unshelve eapply simple_appTerm; cycle 3; tea; irrelevance.
        - unshelve eapply simple_appTerm; cycle 3;  tea.
          eapply LRTmRedConv; tea. irrelevance.
        - unshelve eapply simple_appcongTerm; cycle 3; tea; irrelevance.
        - eapply (fst (mapRedAux _)); tea.
        - unshelve eapply (fst (mapRedAux _)); tea.
          change [LRList' (normList0 LA'_) | Γ ||- tl' : _ ].
          eapply LRTmRedConv; tea.
      }
      * unshelve epose proof (convneulist_whne_list _); cycle 4 ; tea ; do 2 inv_whne.
      * unshelve epose proof (convneulist_whne_list _); cycle 4 ; tea ; do 2 inv_whne.
      * unshelve epose proof (convneulist_whne_list _); cycle 4 ; tea ; do 2 inv_whne.
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
        now unshelve eapply eta_expand_redfuneq.
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
          Unshelve. all: tea. now eapply invLRList.
      * split; tea. intros.
        eapply redconvfun_kripke_neutrals; cycle 1; tea.
    + eapply LREqTermHelper.
      1,2: unshelve eapply mapRedAux; tea; eapply ListPropIrrelevance; tea; cbn.
      2: irrelevance.
      1: eapply LRTyEqRefl_.
      1: tea.
      dependent inversion X0; cbn; dependent inversion X2; cbn.
      Unshelve. 2: tea. 2,3: escape; gen_typing.
      enough [normList RLB | Γ ||- tMap Ap B (comp Ap f fp) lp ≅ tMap Ap' B' (comp Ap' f' fp') lp' : tList B] by irrelevance.
      assert [Γ |- A ≅ A'] by now escape.
      eapply mapCompEqRedAux; tea.
      3: eapply convneulist_whne_list in refl; inversion refl; tea; inv_whne.
      3: eapply convneulist_whne_list in refl0; inversion refl0; tea; inv_whne.
      2:{
        eapply ListRedTm_map_inv_conv; tea.
        cbn. irrelevance.
        Unshelve. all: tea. irrelevance.
      }
      * eapply ty_conv; tea; cbn; now eapply convty_list.
      * eapply convneulist_conv; tea.
      * eapply ListPropIrrelevance; tea.
        cbn. irrelevance.
      Unshelve. tea.
    + eapply transEqTerm.
      1:{
        unshelve eapply mapRedAux; tea.
        unshelve eapply ListPropIrrelevance; cycle 5; tea.
        cbn; eapply LRTyEqRefl_.
      }
      dependent inversion X0; cbn.
      cbn in tyconv. rewrite (not_map_is_not_Map i) in tyconv.
      assert (whlp : whne lp) by (eapply convneulist_whne_list in refl; inversion refl; tea; inv_whne).
      unshelve epose proof (mapCompRedAux Rf ty refl tyinv whlp) as [? []]; tea; [now eapply invLRList|].
      destruct tyinv, tyconv; escape.
      pose (RLB_ := normList0 (invLRList RLB)).
      enough [LRList' RLB_ | Γ ||- tMap Ap B (comp Ap f fp) lp ≅ tMap A' B' f' lp' : tList B] by irrelevance.
      assert [Γ |-[ ta ] comp Ap f fp : arr Ap B].
      1:{
        eapply ty_comp; cycle 2; tea.
        eapply ty_conv; tea.
        eapply convty_simple_arr; tea; now eapply lrefl.
      }
      assert [Γ |-[ ta ] Ap ≅ A'].
      1: cbn in *; etransitivity; tea; etransitivity; [|tea]; now symmetry.
      assert (hcomp: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (n : term),
          [Δ |-[ ta ] n : Ap⟨ρ⟩] ->
          [Δ |-[ ta ] n ~ n : Ap⟨ρ⟩] ->
          [ListRedTyPack.parRed RLB_ ρ wfΔ | Δ ||- tApp (comp Ap f fp)⟨ρ⟩ n ≅ tApp f'⟨ρ⟩ n :_ ]).
      1: {
        intros.
        eapply transEqTerm.
        + eapply redSubstTerm ; [|rewrite wk_comp; eapply redtm_comp_beta; cbn; tea].
          5,6: erewrite wk_arr; eapply ty_wk; tea;
            eapply ty_conv; tea; eapply convty_simple_arr; tea; now eapply lrefl.
          2-4: gen_typing.
          eapply redfun_postcomp_kripke; cycle 1; tea.
        + irrelevance0.
          2: eapply simple_appcongTerm.
          2: irrelevance0; [|now eapply wkTermEq]; now rewrite <- wk_arr.
          1: reflexivity.
          * now eapply redfn.
          * eapply neuTerm; cbn; eapply ty_conv + eapply convneu_conv; tea.
            1,2: eapply convty_wk; tea; etransitivity; tea; now symmetry.
            Unshelve. all: tea. 2: rewrite wk_arr. all: eapply wk; tea.
          * now eapply convredfn_id.
      }
      eapply neuListTermEq; tea.
      * eapply ty_conv.
        1: eapply ty_map; tea.
        1: now eapply ty_conv.
        eapply convty_list; now symmetry.
      * eapply convneulist_map; tea.
        1: eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
        unshelve epose proof (e := hcomp _ (@wk1 Γ Ap) _ (tRel 0) _ _).
        1: gen_typing.
        2: eapply convneu_var.
        1,2: rewrite wk1_ren_on; now eapply ty_var0.
        eapply escapeEqTerm in e.
        rewrite !wk1_ren_on in e.
        exact e.
      * split; tea.
        1: now eapply ty_conv.
        1: now eapply urefl.
        1: eapply convneu_conv; [now eapply urefl| now eapply convty_list].
        intros.
        eapply LRTmRedConv.
        2: eapply redfun_kripke_neutrals; cycle 1; tea.
        irrelevanceRefl; eapply wkEq.
        now eapply LRTyEqSym.
        Unshelve. all: tea. now eapply invLRList.
      * split; tea.
    + (* this part is symmetric with respect to the previous + bullet *)
      eapply transEqTerm.
      2:{
        eapply LRTmEqSym.
        eapply LRTmEqRedConv.
        2: unshelve eapply mapRedAux; tea.
        1: now eapply LRTyEqSym.
        unshelve eapply ListPropIrrelevance; cycle 5; tea.
        cbn; irrelevance.
        Unshelve. tea.
      }
      dependent inversion X2; cbn.
      assert (whlp : whne lp') by (eapply convneulist_whne_list in refl; inversion refl; tea; inv_whne).
      unshelve epose proof (mapCompRedAux Rf' _  _ _ whlp) as [? []].
      10:{ eapply ListRedTm_map_inv_conv; tea. irrelevance. Unshelve. tea. }
      5: eapply ty_conv; tea; now escape.
      5: eapply convneulist_conv; tea; now escape.
      1-4: tea; now eapply invLRList.
      red in tyconv; rewrite (not_map_is_not_Map i) in tyconv; cbn in tyconv.
      destruct tyinv', tyconv; escape.
      pose (RLB_ := normList0 (invLRList RLB)).
      enough [LRList' RLB_ | Γ ||- tMap A B f lp ≅ tMap Ap' B' (comp Ap' f' fp') lp' : tList B] by irrelevance.
      assert [Γ |- A' ≅ Bp'].
      1: etransitivity ; [now symmetry| tea].
      assert [Γ |-[ ta ] comp Ap' f' fp' : arr Ap' B'].
      1:{
        eapply ty_comp; cycle 2; tea.
        eapply ty_conv; tea.
        eapply convty_simple_arr; tea; now eapply urefl.
      }
      assert [Γ |-[ ta ] A ≅ Ap'].
      1: cbn in *; transitivity Bp'; now symmetry.
      assert (hcomp: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]) (n : term),
            [Δ |-[ ta ] n : A⟨ρ⟩] ->
            [Δ |-[ ta ] n ~ n : A⟨ρ⟩] ->
            [ListRedTyPack.parRed RLB_ ρ wfΔ | Δ ||- tApp f⟨ρ⟩ n ≅ tApp (comp Ap' f' fp')⟨ρ⟩ n : _]).
      1: {
        intros.
        eapply transEqTerm; cycle 1.
        + eapply LRTmEqSym.
          eapply redSubstTerm ; [|rewrite wk_comp; eapply redtm_comp_beta; cbn; tea].
          eapply LRTmRedConv.
          2: eapply redfun_postcomp_kripke.
          3: tea.
          1: cbn; eapply LRTyEqSym; now eapply wkEq.
          1: tea.
          1:{ eapply kripke_neutral_app_conv; cycle 3; tea; now eapply LRTyEqSym. }
          6,7: erewrite wk_arr; eapply ty_wk; tea;
            eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
          3-5: gen_typing.
          1,3: eapply ty_conv; tea; now eapply convty_wk.
          eapply convneu_conv; tea; now eapply convty_wk.
          Unshelve. all: tea. 1: now eapply invLRList.
            intros; now eapply wk.
        + assert [Δ |- n : Ap'⟨ρ⟩] by (eapply ty_conv; tea ; now eapply convty_wk).
          assert [Δ |- n ~ n : Ap'⟨ρ⟩] by (eapply convneu_conv; tea ; now eapply convty_wk).
          irrelevance0.
          2: eapply simple_appcongTerm.
          2: irrelevance0; [|now eapply wkTermEq]; now rewrite <- wk_arr.
          1: reflexivity.
          * now eapply neuTerm.
          * now eapply redfn.
          * eapply LRTmEqSym; now eapply convredfn_id.
            Unshelve. all: tea. 2: rewrite wk_arr.
              all: now eapply wk.
      }
      eapply neuListTermEq; tea.
      * now eapply ty_map.
      * eapply ty_conv.
        1: eapply ty_map; tea.
        now symmetry.
      * eapply convneulist_map; tea.
        1: eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
        2: eapply convneu_conv;[now symmetry|]; symmetry; now eapply convty_list.
        unshelve epose proof (e := hcomp _ (@wk1 Γ A) _ (tRel 0) _ _).
        1: gen_typing.
        2: eapply convneu_var.
        1,2: rewrite wk1_ren_on; now eapply ty_var0.
        eapply escapeEqTerm in e.
        rewrite !wk1_ren_on in e.
        exact e.
      * split; tea.
        1,2: now eapply lrefl.
        1: eapply convneu_conv; [now eapply urefl|]; symmetry; now eapply convty_list.
        intros; eapply redfun_kripke_neutrals; cycle 1; tea.
      * eapply ListRedTm_map_inv_conv; tea.
        eapply LRTyEqSym; irrelevance.
        Unshelve. all: tea.
      * split; tea.
        eapply convneu_conv; [now symmetry|]; symmetry; now eapply convty_list.
Qed.

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
  8: now apply invLRList.
  all: refold.
  8:{
    escape; eapply ListRedTm.nilR; tea; cbn; refold.
    unshelve eapply escapeEq; cycle 1; tea.
    eapply LRTyEqRefl_.
  }
  8: apply X.
  all: try solve [ tea ].
  + rewrite <- subst_arr. exact RVFAB.
  + irrelevance; refold; now rewrite subst_arr.
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
  8: now apply invLRList.
  all: refold.
  8:{
    escape; eapply ListRedTm.consR; tea; cbn.
    - unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
    - irrelevance. 
    - enough (X : [normList RVLA | Δ ||- tl[σ] : _]) by exact X.
      irrelevance.
  }
  8: now eapply X.
  all: tea.
  + rewrite <- subst_arr. exact RVFAB.
  + irrelevance; now rewrite subst_arr.
  Unshelve. tea.
Qed.

Definition ListProp_of_mapProp {Γ l A B f x}
  (RA: [Γ ||-<l> A])
  (RLA : [Γ ||-List<l> tList A])
  (RB: [Γ ||-<l> B])
  (RLB : [Γ ||-List<l> tList B])
  (RAB : [Γ ||-<l> arr A B ])
  (Rf: [RAB | Γ ||- f : arr A B])
  (p : ListProp _ _ (normList0 RLA) x) :
  ListProp _ _ (normList0 RLB) (mapProp A B f x p).
Proof.
  assert (wfΓ: [ |- Γ ]) by (escape; gen_typing).
  destruct p as [ | | x].
  - cbn. escape; eapply ListRedTm.nilR; tea; cbn.
    unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
  - cbn. escape; eapply ListRedTm.consR; tea ; cbn.
    + unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
    + eapply simple_appTerm; tea.
      irrelevance0; tea. f_equal; now rewrite wk_id_ren_on.
      Unshelve. 1:tea. now rewrite 2!wk_id_ren_on.
    + change [LRList' (normList0 RLB) | Γ ||- tMap A B f tl : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
  - cbn; destruct (Map.into_view _).
    * eapply mapCompProp; tea.
      1: eapply convneulist_whne_list in refl; inversion refl; tea; inv_whne.
    * assert [Γ |- A ≅ A] by (unshelve eapply escapeEq; tea; eapply LRTyEqRefl_).
      assert [Γ |- B ≅ B] by (unshelve eapply escapeEq; tea; eapply LRTyEqRefl_).
      assert [Γ |- u ~ u : tList A] by now eapply convneulist_is_not_map_convneu.
      constructor; cbn in *.
      + escape; eapply ty_map ; tea.
      + escape; eapply convneulist_map; tea.
        now unshelve eapply eta_expand_redfun.
        Unshelve. all: tea.
      + escape; split; tea.
        intros; eapply redfun_kripke_neutrals ; cycle 1; tea.
Defined.

(* TODO: same lemma with weakening, also reduction of weakened functions? *)

Lemma comp_assoc_app_neutral
        {Γ A B C A0 f g h n l}
        (RA : [Γ ||-<l> A])
        (RB : [Γ ||-<l> B])
        (RC : [Γ ||-<l> C])
        (tyA0 : [Γ |- A0])
        (RFBC : [Γ ||-<l> arr B C])
        (RFAB : [Γ ||-<l> arr A B])
        (Rf : [RFBC | Γ ||- f : arr B C])
        (Rg : [RFAB | Γ ||- g : arr A B])
        (tyh : [Γ |- h : arr A0 A])
        (Rapp : [RA | Γ ||- tApp h n : A ])
        (tycompgh : [Γ |- comp A0 g h : arr A0 B])
        (Rapp' : [RB | Γ ||- tApp (comp A0 g h) n : B])
  : [Γ |- n : A0] -> [Γ |- n ~ n : A0] ->
    [RC | Γ ||- tApp (comp A0 f (comp A0 g h)) n ≅ tApp (comp A0 (comp A f g) h) n : _ ].
Proof.
  intros; escape.
  eapply (transEqTerm (u:= tApp f (tApp g (tApp h n)))).
  + eapply transEqTerm.
    2: eapply simple_appcongTerm.
    - eapply redSubstTerm.
      2: eapply redtm_comp_beta; cycle 3; tea.
      unshelve eapply simple_appTerm; cycle 2; tea.
    - now eapply LREqTermRefl_.
    - eapply redSubstTerm.
      2: eapply redtm_comp_beta; cycle 3; tea.
      unshelve eapply simple_appTerm; cycle 3; tea.
    - unshelve eapply simple_appTerm; cycle 3; tea.
    - eapply redSubstTerm.
      * unshelve eapply simple_appTerm; cycle 3; tea.
      * eapply redtm_comp_beta; cycle 3; tea.
  + eapply LRTmEqSym.
    eapply redSubstTerm.
    - unshelve eapply simple_appTerm; cycle 3; tea.
      unshelve eapply simple_appTerm; cycle 3; tea.
    - etransitivity.
      * eapply redtm_comp_beta; cycle 3; tea.
        eapply ty_comp; cycle 3; tea.
      * eapply redtm_comp_beta; cycle 3; tea.

  Unshelve. now tea.
Qed.


Lemma comp_assoc_app_neutral_wk
        {Γ Δ A B C A0 f g h n l}
        {ρ : Δ ≤ Γ}
        {wfΔ : [|- Δ]}
        (RA' : [Δ ||-<l> A⟨ρ⟩])
        (RB' : [Δ ||-<l> B⟨ρ⟩])
        (RC' : [Δ ||-<l> C⟨ρ⟩])
        (tyA0 : [Γ |- A0])
        (RFBC : [Γ ||-<l> arr B C])
        (RFAB : [Γ ||-<l> arr A B])
        (Rf : [RFBC | Γ ||- f : arr B C])
        (Rg : [RFAB | Γ ||- g : arr A B])
        (tyh : [Γ |- h : arr A0 A])
        (Rapp : [RA' | Δ ||- tApp h⟨ρ⟩ n : A⟨ρ⟩ ])
        (tycompgh : [Γ |- comp A0 g h : arr A0 B])
        (Rapp' : [RB' | Δ ||- tApp (comp A0 g h)⟨ρ⟩ n : B⟨ρ⟩])
  : [Δ |- n : A0⟨ρ⟩] -> [Δ |- n ~ n : A0⟨ρ⟩] ->
    [RC' | Δ ||- tApp (comp A0⟨ρ⟩ f⟨ρ⟩ (comp A0⟨ρ⟩ g⟨ρ⟩ h⟨ρ⟩)) n ≅ tApp (comp A0⟨ρ⟩ (comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩) h⟨ρ⟩) n : _ ].
Proof.
  intros. eapply comp_assoc_app_neutral; tea.
  - now eapply wft_wk.
  - eapply wkTerm in Rf. irrelevance.
    now rewrite<- wk_arr.
  - eapply wkTerm in Rg. irrelevance.
  - rewrite wk_arr. now eapply ty_wk.
  - rewrite <-wk_comp, wk_arr. now eapply ty_wk.
  - now rewrite <-wk_comp.

  Unshelve.
  all: tea.
  all: rewrite wk_arr; now eapply wk.
Qed.

Lemma mapPropRedCompAux {Γ A B C f g i}
  {wfΓ: [|- Γ]}
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
       [Γ ||-<i> mapProp B C f _ (ListProp_of_mapProp RA LA RB LB _ Rg Rx) ≅ mapProp A C (comp A f g) l Rx : tList C | RLC]).
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
    change [ LRList' LC' | Γ ||- tNil C ≅ tNil C : _ ].
    unshelve eapply nilEqRed; tea; solve [ now escape | unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_ ].
  - intros. cbn in *.
    change [ LRList' LC' | Γ ||- tCons C (tApp f (tApp g hd)) (tMap B C f (tMap A B g tl)) ≅
                             tCons C (tApp (comp A f g) hd) (tMap A C (comp A f g) tl) : _ ].
    unshelve eapply consEqRed; try eapply LRTyEqRefl_; tea; try now escape.
    1,2: unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
    + unshelve eapply simple_appTerm; cycle 3; tea.
      unshelve eapply simple_appTerm; cycle 3; tea.
      replace A with A⟨@wk_id Γ⟩. 2: now eapply wk_id_ren_on.
      irrelevance.
    + unshelve eapply simple_appTerm; cycle 3; tea.
      replace A with A⟨@wk_id Γ⟩. 2: now eapply wk_id_ren_on.
      irrelevance.
    + eapply LRTmEqSym. eapply redSubstTerm.
      2: eapply redtm_comp_beta; escape; cycle 2; tea.
      2: replace A with A⟨@wk_id Γ⟩ ; [now eapply escapeTerm | now eapply wk_id_ren_on].
      unshelve eapply simple_appTerm; cycle 3; tea.
      unshelve eapply simple_appTerm; cycle 3; tea.
      replace A with A⟨@wk_id Γ⟩. 2: now eapply wk_id_ren_on.
      irrelevance.
    + eapply LREqTermHelper.
      4: exact X.
      3: eapply LRTyEqRefl_.
      2: now unshelve eapply (fst (mapRedAux _)); tea.
      unshelve eapply (fst (mapEqRedAux _ _)); tea.
      all: try solve [ eapply LRTyEqRefl_ | now eapply LREqTermRefl_ ].
      change [ LRList' (normList0 LB') | Γ ||- tMap A B g tl ≅ tMap A B g (ListRedTm.nf l) : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
      Unshelve. tea.
    + unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LB') | Γ ||- tMap A B g tl : _ ].
      unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LA') | Γ ||- tl : _ ].
      change [ LRList' LA' | Γ ||- tl : _ ] in l.
      irrelevance.
    + unshelve eapply (fst (mapRedAux _)); tea.
      change [ LRList' (normList0 LA') | Γ ||- tl : _ ].
      change [ LRList' LA' | Γ ||- tl : _ ] in l.
      irrelevance.

  - intros.
    set (x := ListProp_of_mapProp _ _ _ _ _ _ _); clearbody x.
    dependent inversion x; destruct (Map.into_view l); try discriminate.
    + cbn. change [ LRList' LC' | Γ ||- (tMap A0 C (comp A0 f (comp A0 g f0)) l) ≅ (tMap A0 C (comp A0 (comp A f g) f0) l) : _ ].
      assert (whne l) by (destruct tyconv; now eapply convneu_whne).
      eapply neuListTermEq.
      3:{
        destruct tyconv0, tyconv. escape.
        eapply convneulist_map; tea.
        4:{
          set (X:= comp _ _ _).
          do 3 erewrite<- wk1_ren_on.
          subst X.
          eapply escapeEqTerm.
          repeat rewrite wk_comp.
          eapply comp_assoc_app_neutral_wk; tea.
          2: eapply redfn0.
          4: eapply redfn.
          3,5,7: eapply convneu_var.
          2-7: rewrite wk1_ren_on; now eapply ty_var0.
          eapply ty_conv; tea. now eapply convty_simple_arr.
        Unshelve.
        1: eapply ListRedTy.parRed.
        all: gen_typing.
        }
        - eapply ty_comp; cycle 3; tea.
        - eapply ty_comp; cycle 3; tea.
          eapply ty_conv.
          eapply ty_comp; cycle 3; tea.
          eapply convty_simple_arr; tea.
          unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
        - unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
      }
      5:{
        destruct tyconv0, tyconv.
        constructor; tea.
        - unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
        - intros.
          repeat rewrite wk_comp.
          eapply comp_assoc_app_neutral_wk; tea.
          2: now eapply redfn0.
          2: now eapply redfn.
          eapply ty_conv; tea. now eapply convty_simple_arr.
          Unshelve. all: tea.
      }
      * destruct tyconv0, tyconv. escape. eapply ty_map; tea.
        eapply ty_comp; cycle 3; tea.
      * destruct tyconv0, tyconv. escape. eapply ty_map; tea.
        eapply ty_comp; cycle 3; tea.
        eapply ty_conv.
        eapply ty_comp; cycle 3; tea.
        eapply convty_simple_arr; tea.
        unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
      * eapply mapCompRedAux; cbn in *; tea.
      * eapply mapCompRedAux; tea.
        Unshelve. all: tea.
    + cbn. rewrite (not_map_is_not_Map i0).
      change [LRList' LC' | Γ ||- tMap A C (comp A f g) u ≅ tMap A C (comp A f g) u : _ ].
      eapply LREqTermRefl_.
      eapply (fst (mapRedAux _ (LA:=LA'))).
      change [ LRList' (normList0 LA') | Γ ||- u : _ ].
      eapply neuTerm; tea.
      now eapply convneulist_is_not_map_convneu.
      Unshelve.
      all: tea.
Qed.


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


Lemma comp_id_app_neutral
        {Γ A A0 f n l}
        (RA : [Γ ||-<l> A])
        (tyA0 : [Γ |- A0])
        (tyh : [Γ |- f : arr A0 A])
        (Rapp : [RA | Γ ||- tApp f n : A ])
  : [Γ |- n : A0] -> [Γ |- n ~ n : A0] ->
    [RA | Γ ||- tApp (comp A0 (idterm A) f) n ≅ tApp f n : A ].
Proof.
  intros. escape.
  eapply redSubstTerm; tea.
  etransitivity.
  eapply redtm_comp_beta; cycle 3; tea.
  + eapply ty_id'. now escape.
  + eapply redtm_id_beta; tea.
    unshelve eapply escapeEq; tea.
    eapply LRTyEqRefl_.
Qed.

Lemma comp_id_app_neutral_wk
        {Γ Δ A A0 f n l}
        {ρ : Δ ≤ Γ}
        {wfΔ : [|- Δ]}
        (RA' : [Δ ||-<l> A⟨ρ⟩])
        (tyA0 : [Γ |- A0])
        (tyh : [Γ |- f : arr A0 A])
        (Rapp : [RA' | Δ ||- tApp f⟨ρ⟩ n : A⟨ρ⟩ ])
  : [Δ |- n : A0⟨ρ⟩] -> [Δ |- n ~ n : A0⟨ρ⟩] ->
    [RA' | Δ ||- tApp (comp A0⟨ρ⟩ (idterm A⟨ρ⟩) f⟨ρ⟩) n ≅ tApp f⟨ρ⟩ n : A⟨ρ⟩ ].
Proof.
  intros. eapply comp_id_app_neutral; tea.
  - eapply wft_wk; tea.
  - rewrite wk_arr. now eapply ty_wk.
Qed.


Lemma mapPropRedIdAux {Γ A i}
  {wfΓ: [ |- Γ ]}
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
    + unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_.
  - intros. eapply consEqRed.
    5: eassumption.
    all: try solve [ escape; tea | cbn; unshelve eapply escapeEq; cycle 1; tea; eapply LRTyEqRefl_ |  eapply LRTyEqRefl_ ].
    + eapply redSubstTerm. 1: now irrelevance.
      apply redtm_id_beta.
      * escape ; tea.
      * unshelve eapply escapeEq ; tea.
        eapply LRTyEqRefl_.
      * unshelve eapply escapeTerm ; tea.
        irrelevance.
    + irrelevance.
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
      eapply listEqRed.
      1: cbn; now escape.
      eapply LRTyEqRefl_.
    Unshelve. all: tea.
  - intros. cbn. destruct (Map.into_view _).
    * change [ LRList' LA' | Γ ||- (tMap A0 A (comp A0 (idterm A) f) l)
                               ≅ (tMap A0 B f l) : _ ].
      assert (whne l) by (destruct tyconv; now eapply convneu_whne).
      eapply neuListTermEq; tea.
      + destruct tyconv. eapply ty_map; escape; tea.
        eapply ty_comp; tea.
        eapply ty_conv; tea; eapply convty_simple_arr; tea; now symmetry.
      + destruct tyconv. eapply convneulist_map; escape; tea.
        { eapply ty_comp; cycle 3; tea.
          eapply ty_conv; tea; eapply convty_simple_arr; tea.
          unshelve eapply escapeEq; tea; eapply LRTyEqRefl_.
        }
        { eapply ty_conv; tea. eapply convty_simple_arr; tea; now symmetry. }
        { erewrite<- wk1_ren_on.
          erewrite<- wk1_ren_on.
          rewrite wk_comp.
          replace f⟨↑⟩ with f⟨@wk1 Γ A0⟩. 2: now rewrite wk1_ren_on.
          eapply escapeEqTerm.
          eapply comp_id_app_neutral_wk; tea.
          2: eapply redfn.
          3,5: eapply convneu_var.
          2-5: rewrite wk1_ren_on; eapply ty_var0; tea.
          eapply ty_conv; tea.
          eapply convty_simple_arr; tea. now symmetry.
        }
      + eapply mapCompRedAux; tea.
      + destruct tyconv. constructor; tea.
        intros.
        rewrite wk_comp.
        eapply comp_id_app_neutral_wk; tea.
        2: now eapply redfn.
        eapply ty_conv; tea.
        eapply convty_simple_arr; tea.
        now symmetry.

    * eapply neuListTermEq.
      + eapply ty_map; escape; tea.
      + eassumption.
      + escape; eapply convneulist_map_id; tea.
        1,2: eapply escapeEq; eapply LRTyEqRefl_.
        1: {
          assert [ |- Γ ,, A ] by (eapply wfc_cons; tea).
          unshelve eapply escapeEqTerm; tea.
          1:{ erewrite<- wk1_ren_on. eapply wk; tea. }
          eapply redSubstTerm.
          - now apply var0.
          - eapply redtm_id_beta.
            + erewrite<- wk1_ren_on. apply wft_wk; tea.
            + erewrite<- wk1_ren_on. apply convty_wk; tea.
              unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
            + eapply ty_var; tea. constructor.
        }
        now eapply convneulist_is_not_map_convneu.
      + cbn. constructor; escape; tea.
        2: cbn. 1-2: unshelve eapply escapeEq; tea; eapply LRTyEqRefl_.
        2:{
          intros.
          unshelve eapply simple_appTerm.
          5: now eapply neuTerm.
          - now eapply wk.
          - eapply ArrRedTy; now eapply wk.
          - cbn. eapply idred.
        }
        1: now eapply convneulist_is_not_map_convneu.
      + eapply ListRedTm_map_inv_whne. eapply whne_list_not_map; tea.
        eapply convneulist_whne_list; tea.
      + cbn. destruct (Map.into_view u); try discriminate.
        constructor; tea.
        3:{ (* TODO: check the lemmas above! *)
          intros.
          eapply redSubstTerm.
          - cbn. now eapply neuTerm.
          - eapply redtm_id_beta; tea.
            + apply wft_wk; escape; tea.
            + apply convty_wk; tea.
              unshelve eapply escapeEq; tea. eapply LRTyEqRefl_.
        }
        1: unshelve eapply escapeEq; tea; eapply LRTyEqRefl_.
        now eapply convneulist_is_not_map_convneu.

      Unshelve.
      all: tea.
      all: gen_typing.
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
    11: irrelevance.
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
