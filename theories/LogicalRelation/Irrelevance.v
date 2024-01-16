(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst Context NormalForms Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity Escape.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.


(** We show a general version of irrelevance, saying that if A and A' are reducible (at levels logical relation levels lA, lA')
and A' is reducibly convertible to A, then the reducibility predicates they decode to are equivalent.
From this, both a simpler version of irrelevance and symmetry follow, by using reflexivity
in the right places. *)
(** Interestingly, we also show irrelevance with respect to universe levels, which is crucial
in later parts of the development, where this avoids creating spurious constraints on universe levels.*)


Section Irrelevances.
Context `{GenericTypingProperties}.


(** *** Equivalences of LRPack *)

Section EquivLRPack.
  Universe i i' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Definition equivLRPack {Γ Γ' s s' A A'} (P: LRPack@{i} Γ s A) (P': LRPack@{i'} Γ' s' A'):=
    and3@{v v v} 
      (forall B, [P | Γ ||- A ≅ B] <≈> [P' | Γ' ||- A' ≅ B])
      (forall t, [P | Γ ||- t : A] <≈> [P' | Γ' ||- t : A'])
      (forall t u, [P | Γ ||- t ≅ u : A] <≈> [P' | Γ' ||- t ≅ u : A']).
End EquivLRPack.

Lemma symLRPack@{i i' v} {Γ Γ' s s' A A'} {P: LRPack@{i} Γ s A} {P': LRPack@{i'} Γ' s' A'} :
    equivLRPack@{i i' v} P P' -> equivLRPack@{i' i v} P' P.
Proof.
  intros [eqT rTm eqTm]; constructor;split ;
    apply eqT + apply rTm + apply eqTm.
Qed.
  

Record equivPolyRed@{i j k l i' j' k' l' v}
  {Γ s_shp s_shp' s_pos s_pos' l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} Γ s_shp s_pos l shp pos}
  {PA' : PolyRed@{i' j' k' l'} Γ s_shp' s_pos' l' shp' pos'} :=
  {
    eqvShp : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ]),
          equivLRPack@{k k' v} (PolyRed.shpRed PA ρ wfΔ) (PolyRed.shpRed PA' ρ wfΔ) ;
    eqvPos : forall {Δ a} (ρ : Δ ≤ Γ) (wfΔ : [  |- Δ])
          (ha : [PolyRed.shpRed PA ρ wfΔ| Δ ||- a : _])
          (ha' : [PolyRed.shpRed PA' ρ wfΔ | Δ ||- a : _]),
          equivLRPack@{k k' v} 
            (PolyRed.posRed PA ρ wfΔ ha)
            (PolyRed.posRed PA' ρ wfΔ ha')
  }.

Arguments equivPolyRed : clear implicits.
Arguments equivPolyRed {_ _ _ _ _ _ _ _ _ _ _} _ _.

Lemma equivPolyRedSym@{i j k l i' j' k' l' v}
  {Γ s_shp s_shp' s_pos s_pos' l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} Γ s_shp s_pos l shp pos}
  {PA' : PolyRed@{i' j' k' l'} Γ s_shp' s_pos' l' shp' pos'} :
  equivPolyRed@{i j k l i' j' k' l' v} PA PA' ->
  equivPolyRed@{i' j' k' l' i j k l v} PA' PA.
Proof.
  intros eqv; unshelve econstructor; intros.
  - eapply symLRPack; eapply eqv.(eqvShp).
  - eapply symLRPack; eapply eqv.(eqvPos).
Qed.

(** *** Lemmas for product types *)

(** A difficulty is that we need to show the equivalence right away, rather than only an implication,
because of contravariance in the case of Π types. To save up work, we factor out some lemmas to
avoid having to basically duplicate their proofs. *)

Section ΠIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {Γ lA A lA' A'} 
  (ΠA : ParamRedTy@{i j k l} tProd Γ set set lA A) 
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd Γ set set lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom) @ set])
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy) @ set])
  (eqv : equivPolyRed ΠA ΠA').

Lemma ΠIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | |econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΠA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now apply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos).
    2: eauto.
    now eapply eqv.(eqvShp).
Qed.

Lemma ΠIrrelevanceTm t : [Γ ||-<lA> t : A | RA] -> [Γ ||-<lA'> t : A' | RA'].
Proof.
  intros []; cbn in *; econstructor; tea.
  - now eapply redtmwf_conv.
  - destruct isfun as [A₀ t₀|n Hn].
    + constructor.
      * intros; now eapply eqv.(eqvShp).
      * intros; unshelve eapply eqv.(eqvPos); [|eauto].
        now apply eqv.(eqvShp).
    + constructor; now eapply convneu_conv.
  - eapply (convtm_conv refl).
    apply eqPi.
  - intros; unshelve eapply eqv.(eqvPos).
    2: now auto.
    now apply eqv.(eqvShp).
  - intros; unshelve eapply eqv.(eqvPos), eq.
    all: now eapply eqv.(eqvShp).
Defined.

Lemma ΠIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΠIrrelevanceTm.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvPos).
    2: now auto.
    now apply eqv.(eqvShp).
Qed.

End ΠIrrelevanceLemmas.

Lemma ΠIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'} 
  (ΠA : ParamRedTy@{i j k l} tProd Γ set set lA A) 
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd Γ set set lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom) @ set])
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy) @ set])
  (eqv : equivPolyRed ΠA ΠA')
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (equivPolyRedSym eqv).
  constructor.
  - split; now apply ΠIrrelevanceTyEq.
  - split; now apply ΠIrrelevanceTm.
  - split; now apply ΠIrrelevanceTmEq.
Qed.


(** *** Lemmas for dependent sum types *)

Section ΣIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {Γ lA A lA' A'} 
  (ΣA : ParamRedTy@{i j k l} tSig Γ set set lA A) 
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig Γ set set lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom) @ set])
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy) @ set])
  (eqv : equivPolyRed ΣA ΣA').

Lemma ΣIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | |econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΣA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now apply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos).
    2: eauto.
    now eapply eqv.(eqvShp).
Qed.

Lemma ΣIrrelevanceTm t : [Γ ||-<lA> t : A | RA] -> [Γ ||-<lA'> t : A' | RA'].
Proof.
  intros []; cbn in *; unshelve econstructor; tea.
  - intros; unshelve eapply eqv.(eqvShp); now auto.
  - now eapply redtmwf_conv.
  - destruct ispair as [A₀ B₀ a b|n Hn].
    + unshelve econstructor.
      * intros; now unshelve eapply eqv.(eqvShp).
      * intros; now eapply eqv.(eqvShp).
      * intros; unshelve eapply eqv.(eqvPos); [|now eauto].
        now unshelve eapply eqv.(eqvShp).
      * intros; now eapply eqv.(eqvPos).
    + constructor; now eapply convneu_conv.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvPos); now auto.
Defined.

Lemma ΣIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΣIrrelevanceTm.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvShp); auto.
  - intros; unshelve eapply eqv.(eqvPos); auto.
Qed.

End ΣIrrelevanceLemmas.

Lemma ΣIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'} 
  (ΣA : ParamRedTy@{i j k l} tSig Γ set set lA A) 
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig Γ set set lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom) @ set])
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy) @ set])
  (eqv : equivPolyRed ΣA ΣA')
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (equivPolyRedSym eqv).
  constructor.
  - split; now apply ΣIrrelevanceTyEq.
  - split; now apply ΣIrrelevanceTm.
  - split; now apply ΣIrrelevanceTmEq.
Qed.

(** *** Lemmas for conversion of reducible neutral terms at arbitrary types *)

Lemma NeNfconv {Γ s k A A'} : [Γ |- A' @ s] -> [Γ |- A ≅ A' @ s] -> [Γ ||-NeNf k : A] -> [Γ ||-NeNf k : A'].
Proof.
  intros ?? []; econstructor; tea. all: gen_typing.
Qed.

Lemma NeNfEqconv {Γ s k k' A A'} : [Γ |- A' @ s] -> [Γ |- A ≅ A' @ s] -> [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k ≅ k' : A'].
Proof.
  intros ?? []; econstructor; tea. gen_typing.
Qed.

(** *** Irrelevance for Identity types *)

Section IdIrrelevance.
  Universe i j k l i' j' k' l' v.
  Context {Γ lA A lA' A'} 
    (IA : IdRedTy@{i j k l} Γ lA A) 
    (IA' : IdRedTy@{i' j' k' l'} Γ lA' A')
    (RA := LRId' IA)
    (RA' := LRId' IA')
    (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy) @ set])
    (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
    (* (eqty : [Γ |- IA.(IdRedTy.ty) ≅  IA'.(IdRedTy.ty)]) *)
    (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ])
    (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _]).

  Let APer := IA.(IdRedTy.tyPER).
  #[local]
  Existing Instance APer.

  Lemma IdIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
  Proof.
    intros  [????] ; cbn in *; econstructor; tea; try now apply eqv.
    - etransitivity; tea; now symmetry.
    - apply eqv; etransitivity; tea; now symmetry.
    - apply eqv; etransitivity; tea; now symmetry.
  Qed.
  
  Lemma IdIrrelevanceProp t : IdProp IA t -> IdProp IA' t. 
  Proof.
    intros []; constructor; tea; cycle -1.
    1: eapply NeNfconv; tea; unfold_id_outTy ; destruct IA'; escape; cbn in *; gen_typing.
    all: apply eqv; tea.
    all: etransitivity; [now symmetry|]; tea.
  Qed.

  Lemma IdIrrelevanceTm t : [Γ ||-<lA> t : A | RA] -> [Γ ||-<lA'> t : A' | RA'].
  Proof.
    intros []; cbn in *; unshelve econstructor; unfold_id_outTy; tea.
    - now eapply redtmwf_conv.
    - now eapply convtm_conv.
    - now eapply IdIrrelevanceProp.
  Qed.

  Lemma IdIrrelevancePropEq t u : IdPropEq IA t u -> IdPropEq IA' t u.
  Proof.
    intros []; constructor ; tea; cycle -1.
    1: eapply NeNfEqconv; tea; unfold_id_outTy ; destruct IA'; escape; cbn in *; gen_typing.
    all: apply eqv; tea.
    all: etransitivity; [now symmetry|]; tea.
  Qed.
  
  Lemma IdIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
  Proof.
    intros []; cbn in *; unshelve econstructor; unfold_id_outTy.
    3,4: now eapply redtmwf_conv.
    - now eapply convtm_conv.
    - now eapply IdIrrelevancePropEq.
  Qed.
  
End IdIrrelevance.

Lemma IdIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'} 
  (IA : IdRedTy@{i j k l} Γ lA A) 
  (IA' : IdRedTy@{i' j' k' l'} Γ lA' A')
  (RA := LRId' IA)
  (RA' := LRId' IA')
  (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy) @ set])
  (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
  (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ])
  (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (IA.(IdRedTy.tyPER)).
  pose proof (symLRPack eqv).
  assert (eqId' : [Γ |- IA'.(IdRedTy.outTy) ≅ IA.(IdRedTy.outTy) @ set]) by now symmetry.
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.lhs) ≅  IA.(IdRedTy.lhs) : _ ] by (apply eqv; now symmetry).
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.rhs) ≅  IA.(IdRedTy.rhs) : _ ] by (apply eqv; now symmetry).
  constructor.
  - split; now apply IdIrrelevanceTyEq.
  - split; now apply IdIrrelevanceTm.
  - split; now apply IdIrrelevanceTmEq.
Qed.

(** *** Irrelevance for neutral types *)

Lemma NeIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ s A A'} lA lA'
  (neA : [Γ ||-ne A @ s])
  (neA' : [Γ ||-ne A' @ s])
  (RA := LRne_@{i j k l} lA neA)
  (RA' := LRne_@{i' j' k' l'} lA' neA')
  (eqAA' : [Γ ||-ne A ≅ A' | neA ])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  destruct neA as [ty], neA' as [ty'], eqAA' as [ty0']; cbn in *.
  assert (ty0' = ty'); [|subst].
  { eapply redtywf_det; tea; constructor; eapply convneu_whne; first [eassumption|symmetry; eassumption]. }
  assert [Γ |- ty ≅ ty' @ s] as convty by gen_typing.
  split.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    all: etransitivity ; [| tea]; tea; now symmetry.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    1,3: now eapply (redtmwf_conv (s := s)).
    all: now eapply convneu_conv; first [eassumption|symmetry; eassumption|gen_typing].
  + intros ??; split; intros []; econstructor; cbn in *.
    1-2,4-5: now eapply (redtmwf_conv (s := s)).
    all: now eapply convneu_conv; first [eassumption|symmetry; eassumption|gen_typing].
Qed.



Section NatIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {Γ lA lA' A A'} (NA : [Γ ||-Nat A]) (NA' : [Γ ||-Nat A'])
    (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA').
  
  Lemma NatIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma NatIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA] -> [Γ ||-<lA'> t : A' | RA'])
    × (forall t, NatProp NA t -> NatProp NA' t).
  Proof.
    apply NatRedInduction; now econstructor.
  Qed.
   
  Lemma NatIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'])
    × (forall t u, NatPropEq NA t u -> NatPropEq NA' t u).
  Proof.
    apply NatRedEqInduction; now econstructor.
  Qed.
End NatIrrelevant.

Lemma NatIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA lA' A A'} (NA : [Γ ||-Nat A]) (NA' : [Γ ||-Nat A'])
  (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply NatIrrelevanceTyEq.
  - split; apply NatIrrelevanceTm.
  - split; apply NatIrrelevanceTmEq.
Qed.

Section EmptyIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {Γ lA lA' A A'} (NA : [Γ ||-Empty A]) (NA' : [Γ ||-Empty A'])
    (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA').
  
  Lemma EmptyIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma EmptyIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA] -> [Γ ||-<lA'> t : A' | RA']).
  Proof.
    intros t Ht. induction Ht; now econstructor.
  Qed.
   
  Lemma EmptyIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA']).
  Proof.
    intros t u Htu. induction Htu. now econstructor.
  Qed.
End EmptyIrrelevant.

Lemma EmptyIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA lA' A A'} (NA : [Γ ||-Empty A]) (NA' : [Γ ||-Empty A'])
  (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply EmptyIrrelevanceTyEq.
  - split; apply EmptyIrrelevanceTm.
  - split; apply EmptyIrrelevanceTmEq.
Qed.

(** The main proof *)

Section LRIrrelevant.
Universe u v.
(** u is a small universe level that may be instanciated to Set. v is a large universe level *)

Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

Section LRIrrelevantInductionStep.

Universe i j k l i' j' k' l'.

#[local]
Definition IHStatement lA lA' :=
  (forall l0 (ltA : l0 << lA) (ltA' : l0 << lA'),
      prod@{v v}
        (forall Γ s t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t @ s ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t @ s ])
        (forall Γ s t
           (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t @ s ])
           (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t @ s ])
           u,
            [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ] <≈>
            [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ])).

#[local]
Lemma UnivIrrelevanceLRPack
  {Γ lA lA' A A'}
  (IH : IHStatement lA lA')
  (hU : [Γ ||-U<lA> A]) (hU' : [Γ ||-U<lA'> A'])
  (RA := LRU_@{i j k l} hU) (RA' := LRU_@{i' j' k' l'} hU') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  revert IH; destruct hU as [_ []], hU' as [_ []]; intro IH; destruct (IH zero Oi Oi) as [IHty IHeq].
  constructor.
  + intros; cbn; split; intros []; now constructor.
  + intros ?; destruct (IHty Γ set t) as [tfwd tbwd]; split; intros [];
      unshelve econstructor.
    6: now apply tfwd.
    9: now apply tbwd.
    all : tea.
  + cbn ; intros ? ?;
    destruct (IHty Γ set t) as [tfwd tbwd];
    destruct (IHty Γ set u) as [ufwd ubwd].
    split; intros [[] []]; cbn in *; unshelve econstructor.
    3: now apply tfwd.
    5: now apply tbwd.
    6: now apply ufwd.
    8: now apply ubwd.
    (* all: apply todo. *)
    all: cbn.
    6: now refine (fst (IHeq _ _ _ _ _ _) _).
    7: now refine (snd (IHeq _ _ _ _ _ _) _).
    1-4: now econstructor.
    all: cbn; tea.
Qed.

(** ** The main theorem *)

#[local]
Lemma LRIrrelevantPreds {lA lA'}
  (IH : IHStatement lA lA')
  (Γ : context) (s : sort) (A A' : term)
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ s A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ s A' eqTyA' redTmA' eqTmA')
  (RA := Build_LRPack Γ s A eqTyA redTmA eqTmA)
  (RA' := Build_LRPack Γ s A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  equivLRPack@{k k' v} RA RA'.
Proof.
  intros he.
  set (shpv := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? h1 | ? ? neA | ? A ΠA HAad IHdom IHcod | ?? NA | ?? NA|? A ΠA HAad IHdom IHcod | ?? IAP IAad IHPar]
    in RA, A', RA', eqTyA', eqTmA', redTmA', lrA', he, shpv |- *.
  - destruct lrA' ; try solve [destruct shpv] ; clear shpv.
    now apply UnivIrrelevanceLRPack.
  - destruct lrA'  ; try solve [destruct shpv] ; clear shpv.
    now unshelve eapply NeIrrelevanceLRPack.
  - destruct lrA' as [| | ? A' ΠA' HAad'| | | |] ; try solve [destruct shpv] ; clear shpv.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codRed]], ΠA' as [dom1 cod1];
    assert (tProd dom0 cod0 = tProd dom1 cod1) as ePi
    by (eapply redtywf_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    eapply (ΠIrrelevanceLRPack PA PA'); [| |unshelve econstructor].
    + eassumption.
    + eassumption.
    + intros; unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed PA' _ _)).
      eapply domRed.
    + intros; unshelve eapply IHcod.
      2: eapply (LRAd.adequate (PolyRed.posRed PA' _ _ _)).
      eapply codRed.
  - destruct lrA' ; try solve [destruct shpv] ; clear shpv.
    now unshelve eapply NatIrrelevanceLRPack.
  - destruct lrA' ; try solve [destruct shpv] ; clear shpv.
    now unshelve eapply EmptyIrrelevanceLRPack.
  - destruct lrA' as [| | | | |? A' ΠA' HAad'|] ; try solve [destruct shpv] ; clear shpv.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codRed]], ΠA' as [dom1 cod1];
    assert (tSig dom0 cod0 = tSig dom1 cod1) as ePi
    by (eapply redtywf_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    eapply (ΣIrrelevanceLRPack PA PA'); [| |unshelve econstructor].
    + eassumption.
    + eassumption.
    + intros; unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed PA' _ _)).
      eapply domRed.
    + intros; unshelve eapply IHcod.
      2: eapply (LRAd.adequate (PolyRed.posRed PA' _ _ _)).
      eapply codRed.
  - destruct lrA' as [| | | | | | ? A' IAP' IAad'] ; try solve [destruct shpv] ; clear shpv.
    pose (IA := IdRedTy.from IAad); pose (IA' := IdRedTy.from IAad').
    assert (IA'.(IdRedTy.outTy) = he.(IdRedTyEq.outTy)) as eId.
    + eapply redtywf_det.
      * constructor.
      * constructor.
      * now eapply IA'.(IdRedTy.red).
      * now eapply he.(IdRedTyEq.red).
    + inversion eId; destruct he, IAP'; cbn in *. subst; clear eId.
      eapply (IdIrrelevanceLRPack IA IA'); tea.
      eapply IHPar; tea.
      apply IA'.(IdRedTy.tyRed).
    (* unshelve eapply escapeEq.  2: apply IdRedTy.tyRed.  now cbn. *)
Qed.


#[local]
Lemma LRIrrelevantCumPolyRed {lA}
  (IH : IHStatement lA lA)
  (Γ : context) (s_shp s_pos : sort) (shp pos : term)
  (PA : PolyRed@{i j k l} Γ s_shp s_pos lA shp pos)
  (IHshp : forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-< lA > shp⟨ρ⟩ @ s_shp⟨ρ⟩])
  (IHpos : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
          [PolyRed.shpRed PA ρ h | _ ||- a : _] ->
          [Δ ||-< lA > pos[a .: ρ >> tRel] @ s_pos[a .: ρ >> tRel]]) :
  PolyRed@{i' j' k' l'} Γ s_shp s_pos lA shp pos.
Proof.
  unshelve econstructor.
  + exact IHshp.
  + intros Δ a ρ tΔ ra. eapply IHpos.
    pose (shpRed := PA.(PolyRed.shpRed) ρ tΔ).
    destruct (LRIrrelevantPreds IH _ _ _ _
             (LRAd.adequate shpRed)
             (LRAd.adequate (IHshp Δ ρ tΔ))
             (reflLRTyEq shpRed)) as [_ irrTmRed _].
    now eapply (snd (irrTmRed a)).
  + now destruct PA.
  + now destruct PA.
  + cbn. intros Δ a b ρ tΔ ra rb rab.
    set (p := LRIrrelevantPreds _ _ _ _ _ _ _).
    destruct p as [_ irrTmRed irrTmEq].
    pose (ra' := snd (irrTmRed a) ra).
    pose (posRed := PA.(PolyRed.posRed) ρ tΔ ra').
    destruct (LRIrrelevantPreds IH _ _ _ _
                (LRAd.adequate posRed)
                (LRAd.adequate (IHpos Δ a ρ tΔ ra'))
                (reflLRTyEq posRed)) as [irrTyEq _ _].
    eapply (fst (irrTyEq (pos[b .: ρ >> tRel]))).
    eapply PolyRed.posExt.
    1: exact (snd (irrTmRed b) rb).
    exact (snd (irrTmEq a b) rab).
Qed.


Set Printing Universes.
#[local]
Lemma LRIrrelevantCumTy {lA}
  (IH : IHStatement lA lA)
  (Γ : context) (s : sort) (A : term)
  : [ LogRel@{i j k l} lA | Γ ||- A @ s ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A @ s ].
Proof.
  intros lrA; revert IH; pattern lA, Γ, s, A, lrA; eapply LR_rect_TyUr ; clear lA Γ s A lrA.
  all: intros lA Γ A.
  - intros [] ?; eapply LRU_; now econstructor.
  - intros; now eapply LRne_.
  - intros [] IHdom IHcod IH; cbn in *.
    eapply LRPi'; unshelve econstructor.
    3,4,5: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
  - intros; now eapply LRNat_.
  - intros; now eapply LREmpty_.
  - intros [] IHdom IHcod IH; cbn in *.
    eapply LRSig'; unshelve econstructor.
    3,4,5: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
  - intros [] IHPar IHKripke IH. 
    specialize (IHPar IH). pose (IHK Δ ρ wfΔ := IHKripke Δ ρ wfΔ IH).
    cbn in *; eapply LRId'.
    assert (eqv: equivLRPack tyRed IHPar).
    1: eapply LRIrrelevantPreds; tea; try eapply reflLRTyEq; now eapply LRAd.adequate.
    assert (eqvK : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]), equivLRPack (tyKripke Δ ρ wfΔ) (IHK Δ ρ wfΔ)).
    1: intros; eapply LRIrrelevantPreds; tea; try eapply reflLRTyEq; now eapply LRAd.adequate.
    unshelve econstructor.
    4-7: tea.
    1-4: now apply eqv.
    2-4: intros * ? ?%eqvK; apply eqvK; eauto.
    econstructor.
    + intros ?? ?%eqv; apply eqv; now symmetry.
    + intros ??? ?%eqv ?%eqv; apply eqv; now etransitivity.
Qed.


#[local]
Lemma IrrRec0 : IHStatement zero zero.
Proof.
  intros ? ltA; inversion ltA.
Qed.

(** Safety check: we did not add constraints we did not mean to *)
Fail Fail Constraint i < i'.
Fail Fail Constraint i' < i.
Fail Fail Constraint j < j'.
Fail Fail Constraint j' < j.
Fail Fail Constraint k < k'.
Fail Fail Constraint k' < k.
Fail Fail Constraint l < l'.
Fail Fail Constraint l' < l.

End LRIrrelevantInductionStep.

#[local]
Theorem IrrRec@{i j k l i' j' k' l'} {lA} {lA'} :
  IHStatement@{i j k l i' j' k' l'} lA lA'.
Proof.
  intros l0 ltA ltA'.
  destruct ltA. destruct ltA'. cbn in *.
  split.
  - intros Γ s t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros Γ s t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} Γ s t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (reflLRTyEq lr1)) as [tyEq _ _].
    exact (tyEq u).
Qed.

#[local]
Theorem LRIrrelevantCum@{i j k l i' j' k' l'}
  (Γ : context) (s : sort) (A A' : term) {lA lA'}
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ s A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ s A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  @and3@{v v v} (forall B, eqTyA B <≈> eqTyA' B)
    (forall t, redTmA t <≈> redTmA' t)
    (forall t u, eqTmA t u <≈> eqTmA' t u).
Proof.
  exact (LRIrrelevantPreds@{i j k l i' j' k' l'} IrrRec Γ s A A' lrA lrA').
Qed.

Theorem LRIrrelevantPack@{i j k l} 
  (Γ : context) (s : sort) (A A' : term) {lA lA'} 
  (RA : [ LogRel@{i j k l} lA | Γ ||- A @ s ])
  (RA' : [ LogRel@{i j k l} lA' | Γ ||- A' @ s ])
  (RAA' : [Γ ||-<lA> A ≅ A' | RA]) :
  equivLRPack@{v v v} RA RA'.
Proof.
  pose proof (LRIrrelevantCum@{i j k l i j k l} Γ s A A' (LRAd.adequate RA) (LRAd.adequate RA') RAA') as [].
  constructor; eauto.
Defined.

Theorem LRTransEq@{i j k l} 
  (Γ : context) (s : sort) (A B C : term) {lA lB} 
  (RA : [ LogRel@{i j k l} lA | Γ ||- A @ s])
  (RB : [ LogRel@{i j k l} lB | Γ ||- B @ s])
  (RAB : [Γ ||-<lA> A ≅ B | RA])
  (RBC : [Γ ||-<lB> B ≅ C | RB]) :
  [Γ ||-<lA> A ≅ C | RA].
Proof.
  pose proof (LRIrrelevantPack Γ s A B RA RB RAB) as [h _ _].
  now apply h.
Defined.


Theorem LRCumulative@{i j k l i' j' k' l'} {lA}
  {Γ : context} {s : sort} {A : term}
  : [ LogRel@{i j k l} lA | Γ ||- A @ s ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A @ s ].
Proof.
  exact (LRIrrelevantCumTy@{i j k l i' j' k' l'} IrrRec Γ s A).
Qed.

Corollary LRCumulative' @{i j k l i' j' k' l'} {lA}
  {Γ : context} {s : sort} {A A' : term}
  : A = A' -> [ LogRel@{i j k l} lA | Γ ||- A @ s ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A' @ s ].
Proof.
  intros ->; apply LRCumulative.
Qed.
End LRIrrelevant.


#[local]
Corollary TyEqIrrelevantCum Γ s A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ s A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ s A eqTyA' redTmA' eqTmA') :
  forall B, eqTyA B -> eqTyA' B.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ s A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A @ s]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A ≅ B | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ s A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A' @ s]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevant'@{i j k l} lA lA' Γ s A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A' @ s]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

#[local]
Corollary RedTmIrrelevantCum Γ s A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ s A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ s A eqTyA' redTmA' eqTmA') :
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmRedIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ s A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A @ s]) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ s A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A' @ s]) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevant'@{i j k l} lA lA' Γ s A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A' @ s]) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.


#[local]
Corollary TmEqIrrelevantCum Γ s A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ s A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ s A eqTyA' redTmA' eqTmA') :
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ s A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A @ s]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ s A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A' @ s]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevant'@{i j k l} lA lA' Γ s A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A @ s]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A' @ s]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.



Corollary TyEqSym Γ s A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ s A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ s A' eqTyA' redTmA' eqTmA') :
  eqTyA A' -> eqTyA' A.
Proof.
  intros.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  1: eauto.
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqSym lA lA' Γ s A A' (lrA : [Γ ||-< lA > A @ s]) (lrA' : [Γ ||-< lA'> A' @ s]) :
  [Γ ||-< lA > A ≅ A' | lrA] -> [Γ ||-< lA' > A' ≅ A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqSym.
Qed.

#[local]
Corollary RedTmConv Γ s A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ s A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ s A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
Qed.

Corollary LRTmRedConv lA lA' Γ s A A' (lrA : [Γ ||-< lA > A @ s]) (lrA' : [Γ ||-< lA'> A' @ s]) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmConv.
Qed.

Corollary PolyRedEqSym {Γ s_shp s_pos s_shp' s_pos' l l' shp shp' pos pos'}
  {PA : PolyRed Γ s_shp s_pos l shp pos}
  (PA' : PolyRed Γ s_shp' s_pos' l' shp' pos') :
  PolyRedEq PA shp' pos' -> PolyRedEq PA' shp pos.
Proof.
  intros []; unshelve econstructor.
  - intros; eapply LRTyEqSym. eapply shpRed.
  - intros. eapply LRTyEqSym. unshelve eapply posRed; tea.
    eapply LRTmRedConv; tea.
    now eapply LRTyEqSym.
  Unshelve. all: tea.
Qed.

#[local]
Corollary TmEqRedConv Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
Qed.

Corollary LRTmEqRedConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqRedConv.
Qed.

Corollary LRTmTmEqIrrelevant' lA lA' Γ A A' (e : A = A')
  (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  forall t u, 
  [Γ ||-<lA> t : A | lrA] × [Γ ||-< lA > t ≅ u : A | lrA] -> 
  [Γ ||-<lA'> t : A' | lrA'] × [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  intros ?? []; split; [eapply LRTmRedIrrelevant'| eapply LRTmEqIrrelevant']; tea.
Qed.

Set Printing Primitive Projection Parameters.

Lemma NeNfEqSym {Γ k k' A} : [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k' ≅ k : A].
Proof.
  intros []; constructor; tea; now symmetry.
Qed.

Lemma LRTmEqSym@{h i j k l} lA Γ A (lrA : [LogRel@{i j k l} lA | Γ ||- A]) : forall t u,
  [Γ ||-<lA> t ≅ u : A |lrA] -> [Γ ||-<lA> u ≅ t : A |lrA].
Proof.
  pattern lA, Γ, A, lrA. apply LR_rect_TyUr; clear lA Γ A lrA.
  - intros * []. unshelve econstructor; try eassumption.
    1: symmetry; eassumption.
    (* Need an additional universe level h < i *)
    eapply TyEqSym@{h i j k h i j k}. 3:exact relEq.
    all: eapply LogRelRec_unfold; eapply LRAd.adequate; eassumption.
  - intros * []. unshelve econstructor.
    3,4: eassumption.
    symmetry; eassumption.
  - intros * ihdom ihcod * []. unshelve econstructor.
    1,2: eassumption.
    1: symmetry; eassumption.
    intros. apply ihcod. eapply eqApp.
  - intros ??? NA.
    set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA u t)) by apply h.
    subst G; apply NatRedEqInduction.
    1-3: now econstructor.
    intros; constructor; now eapply NeNfEqSym.
  - intros ??? NA.
    intros t u [? ? ? ? ? ? ? prop]. destruct prop. econstructor; eauto.
    2: econstructor; now eapply NeNfEqSym.
    symmetry; eassumption.
  - intros * ihshp ihpos * []; unshelve econstructor; tea.
    1: now symmetry.
    + intros; now eapply ihshp.
    + intros; eapply ihpos.
      eapply LRTmEqRedConv.
      2: eapply eqSnd.
      now eapply PolyRed.posExt.
  - intros ??? [] ???? [????? hprop]; unshelve econstructor; unfold_id_outTy; cbn in *.
    3,4: tea.
    1: now symmetry.
    destruct hprop; econstructor; tea.
    now eapply NeNfEqSym.
Qed.

End Irrelevances.


(** ** Tactics for irrelevance, with and without universe cumulativity *)

Ltac irrelevanceCum0 :=
  lazymatch goal with
  | [|- [_ ||-<_> _]] => (now eapply LRCumulative) + eapply LRCumulative'
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ | _ ||- _ ≅ _ : _ ] ] => eapply LRTmEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevantCum'
  end.

Ltac irrelevanceCum := irrelevanceCum0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceCumRefl := irrelevanceCum0 ; [reflexivity|].

Ltac irrelevance0 :=
  lazymatch goal with
  | [|- [_ | _ ||- _ ≅ _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ | _ ] ] => eapply LRTyEqIrrelevant'
  | [|- [_ | _ ||- _ : _ ] ] => eapply LRTmRedIrrelevant'
  | [|- [_ ||-<_> _ : _ | _ ] ] => eapply LRTmRedIrrelevant'
  | [|- [_ | _ ||- _ ≅ _ : _ ] ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ] ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ : _ | _] × [_ ||-<_> _≅ _ : _ | _]] => eapply LRTmTmEqIrrelevant'
  end.

Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceRefl := irrelevance0 ; [reflexivity|].
