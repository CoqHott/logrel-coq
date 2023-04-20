
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
 [|- Γ] ->
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
  (RA: [Γ ||-<l> A]) (RA': [Γ ||-<l> A'])
  (RLA: [Γ ||-<l> tList A])
  :
  [|- Γ] -> [Γ ||-<l> A ≅ A' | RA] -> [Γ ||-<l> tList A ≅ tList A' | RLA ].
Proof.
  intros.
  enough ([ normList RLA | Γ ||- tList A ≅ tList A']) by irrelevance.
  econstructor.
  - eapply redtywf_refl. escape. gen_typing.
  - cbn. eapply convty_list. escape. assumption.
  - irrelevance.
Defined.

Lemma listValid {Γ A l} (VΓ : [||-v Γ]) (h: [Γ ||-v<l> A | VΓ]) : [Γ ||-v<l> tList A | VΓ].
Proof.
  unshelve econstructor; intros.
  + eapply listRed. 1: easy.
    now eapply validTy.
  + eapply listEqRed ; tea.
    (* now eapply validTyExt. *)
    1-2: now instAllValid vσ vσ' vσσ'.
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
  1-2: now instValid Vσ.
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
      1: now eapply UnivEq'.
      now eapply UnivEqEq.
      Unshelve.
      1: irrelevanceCum.
      now eapply UnivEq'.
Qed.

Lemma nilRed {Γ A l}
  (RA: [Γ ||-< l > A])
  (RLA: [Γ ||-< l > tList A]) :
  [RLA | Γ ||- tNil A : tList A].
Proof.
  enough [ normList RLA | Γ ||- tNil A : _] by irrelevance.
  econstructor.
  + eapply redtmwf_refl. escape. now apply ty_nil.
  + eapply convtm_nil. unshelve eapply escapeEq ; tea.
    apply LRTyEqRefl_.
  + constructor. 1: escape ; tea.
    apply LRTyEqRefl_.
Qed.

Lemma nilEqRed {Γ A A' l}
  (RA: [Γ ||-< l > A])
  (RA': [Γ ||-< l > A'])
  (RLA: [Γ ||-< l > tList A])
  (RLA': [Γ ||-< l > tList A']) :
  [RA | Γ ||- A ≅ A'] ->
  [RLA | Γ ||- tList A ≅ tList A'] ->
  [RLA | Γ ||- tNil A ≅ tNil A' : tList A].
Proof.
  intros.
  enough [normList RLA | Γ ||- tNil A ≅ tNil A' : tList A] by irrelevance.
  econstructor.
  (* + eapply redtmwf_refl. escape. now apply ty_nil. *)
  (* + eapply redtmwf_refl. escape. *)
  (*   eapply ty_conv. 2: symmetry ; eassumption. *)
  (*   now eapply ty_nil. *)
  (* + eapply convtm_nil. escape. eassumption. *)
  (* + constructor ; escape ; tea. *)
  (*   - apply LRTyEqRefl_. *)
  (*   - irrelevance. *)
Admitted.

Lemma nilValid {Γ A l}
  {VΓ : [||-v Γ]}
  {VA : [Γ ||-v<l> A | VΓ]}
  {VLA : [Γ ||-v<l> tList A | VΓ]} :
  [Γ ||-v<l> tNil A : tList A | VΓ | VLA].
Proof.
  split; intros.
  - instValid Vσ.
    now eapply nilRed.
  - instAllValid Vσ Vσ' Vσσ'.
    now eapply nilEqRed.
Qed.

Lemma consRed {Γ A hd tl l}
  (RA: [Γ ||-< l > A])
  (RLA: [Γ ||-< l > tList A]) :
  [RA | Γ ||- hd : A] ->
  [RLA | Γ ||- tl : tList A] ->
  [RLA | Γ ||- tCons A hd tl : tList A ].
Proof.
  intros.
  enough [ normList RLA | Γ ||- tCons A hd tl : _] by irrelevance.
  econstructor.
  + eapply redtmwf_refl. escape. now apply ty_cons.
  + eapply convtm_cons.
    * unshelve eapply escapeEq ; tea.
      apply LRTyEqRefl_.
    * eapply escapeEqTerm ; tea.
      now apply LREqTermRefl_.
    * eapply escapeEqTerm ; tea.
      now apply LREqTermRefl_.
  + constructor. 1: escape ; tea.
    * apply LRTyEqRefl_.
    * irrelevance.
    * change [ normList RLA | Γ ||- tl : tList A].
      irrelevance.
Qed.

Lemma consEqRed {Γ A A' hd hd' tl tl' l}
  (RA: [Γ ||-< l > A])
  (RA': [Γ ||-< l > A'])
  (RLA: [Γ ||-< l > tList A])
  (RLA': [Γ ||-< l > tList A']) :
  [RA | Γ ||- A ≅ A'] ->
  [RLA | Γ ||- tList A ≅ tList A'] ->
  [RA | Γ ||- hd : A] ->
  [RA' | Γ ||- hd' : A'] ->
  [RA | Γ ||- hd ≅ hd' : A] ->
  [RLA | Γ ||- tl ≅ tl' : tList A] ->
  [RLA | Γ ||- tl : tList A] ->
  [RLA' | Γ ||- tl' : tList A'] ->
  [RLA | Γ ||- tCons A hd tl ≅ tCons A' hd' tl' : tList A ].
Proof.
  intros.
  enough [ normList RLA | Γ ||- tCons A hd tl ≅ tCons A' hd' tl' : _] by irrelevance.
  econstructor.
  (* + eapply redtmwf_refl. escape. now apply ty_cons. *)
  (* + eapply redtmwf_refl. escape. *)
  (*   eapply ty_conv. 2: symmetry ; eassumption. *)
  (*   now apply ty_cons. *)
  (* + eapply convtm_cons; escape; eassumption. *)
  (* + constructor ; escape ; tea. *)
  (*   - apply LRTyEqRefl_. *)
  (*   - irrelevance. *)
  (*   - irrelevance. *)
  (*   - change [ normList RLA | Γ ||- tl ≅ tl' : tList A]. *)
  (*     irrelevance. *)
Admitted.

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
    now eapply consRed.
  - instAllValid Vσ Vσ' Vσσ'.
    now eapply consEqRed.
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
    apply redSubstTerm. 1: now apply nilRed.
    eapply redtm_map_nil ; tea.
    unshelve eapply escapeEq.
    3: eassumption.
  - admit.
  - admit.
Admitted.

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
  (Rf': [Γ ||-<l> f' : arr A' B' | RFAB']) :
  (forall x x' (Rxx': ListRedTmEq _ _ LA_ x x'),
        [Γ ||-<l> tMap A B f x ≅ tMap A' B' f' x' : tList B | RLB])
    ×
    (forall x x' (Rxx': ListPropEq _ _ LA_ x x'),
          [Γ ||-<l> tMap A B f x ≅ tMap A' B' f' x' : tList B | RLB]).
  apply ListRedEqInduction.
  - intros.
    eapply LREqTermHelper.
    4: eassumption.
    1: now unshelve eapply mapRedAux.
    2: eassumption.
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
    Unshelve. now tea.
  - intros.
    eapply LREqTermHelper.
    3: eassumption.
    + unshelve eapply mapRedAux ; tea.
      econstructor ; tea.
      irrelevance.
    + unshelve eapply mapRedAux ; tea.
      econstructor ; tea.
      eapply transEq ; tea.
      unshelve eapply LRTyEqSym. 3: eassumption.
    + cbn. now eapply nilEqRed.
  - intros.
    eapply LREqTermHelper.
    3: eassumption.
    all: admit.
  - admit. (* see Neutral.v *)
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
  {VLB : [Γ ||-v<i> tList B | VΓ]}
  {VLB' : [Γ ||-v<i> tList B' | VΓ]}
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
  all: admit.
  (* + now eapply invLRList. *)
  (* + now eapply invLRList. *)
  (* + admit. *)
  (* + admit. *)
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


Lemma mapRedIdAux {Γ A i}
  {RA : [Γ ||-<i> A]}
  {LA : [Γ ||-List<i> tList A]}
  (LA' := normList0 LA : [Γ ||-List<i> tList A])
  (RLA :=  LRList' LA' : [Γ ||-<i> tList A] )
  {RFAA : [Γ ||-<i> arr A A]}
  (Rid: [Γ ||-<i> (idterm A) : arr A A | RFAA]) :
  (forall l (Rx: ListRedTm _ _ LA' l),
        [Γ ||-<i> tMap A A (idterm A) l : tList A | RLA] ×
        [Γ ||-<i> tMap A A (idterm A) l ≅ l : tList A | RLA])
    ×
    (forall l (Rx: ListProp _ _ LA' l),
        [Γ ||-<i> tMap A A (idterm A) l : tList A | RLA] ×
          [Γ ||-<i> tMap A A (idterm A) l ≅ l : tList A | RLA]).
Proof.
  escape.
  intros.
  apply ListRedInduction.
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
  unshelve epose (snd (fst (mapRedIdAux _) _ _)).
  10: irrelevance.
  3: now apply invLRList.
  all: admit.
Admitted.

End List.
