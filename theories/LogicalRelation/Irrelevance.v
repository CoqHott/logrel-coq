(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
Require Import PeanoNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Notations Utils BasicAst LContexts Context NormalForms Weakening GenericTyping LogicalRelation DeclarativeInstance.
From LogRel.LogicalRelation Require Import Induction ShapeView Reflexivity.

Set Universe Polymorphism.
Set Printing Universes.

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

  Definition equivLRPack {wl wl' Γ Γ' A A'} (P: LRPack@{i} wl Γ A) (P': LRPack@{i'} wl' Γ' A'):=
    and3@{v v v} 
      (forall B, [P | Γ ||- A ≅ B]< wl > <≈> [P' | Γ' ||- A' ≅ B]< wl' >)
      (forall t, [P | Γ ||- t : A]< wl > <≈> [P' | Γ' ||- t : A']< wl' >)
      (forall t u, [P | Γ ||- t ≅ u : A]< wl > <≈> [P' | Γ' ||- t ≅ u : A']< wl' >).
End EquivLRPack.

Lemma symLRPack@{i i' v} {wl wl' Γ Γ' A A'} {P: LRPack@{i} wl Γ A} {P': LRPack@{i'} wl' Γ' A'} :
    equivLRPack@{i i' v} P P' -> equivLRPack@{i' i v} P' P.
Proof.
  intros [eqT rTm eqTm]; constructor;split ;
    apply eqT + apply rTm + apply eqTm.
Qed.
  


(** *** Lemmas for product types *)

(** A difficulty is that we need to show the equivalence right away, rather than only an implication,
because of contravariance in the case of Π types. To save up work, we factor out some lemmas to
avoid having to basically duplicate their proofs. *)

Section ΠIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {wl Γ lA A lA' A'} 
  (ΠA : PiRedTyPack@{i j k l} wl Γ A lA) 
  (ΠA' : PiRedTyPack@{i' j' k' l'} wl Γ A' lA')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (domN := @PiRedTyPack.domN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA)
  (domN' := @PiRedTyPack.domN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA')
  (domRed := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (domRed' := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA'))
  (codomN := @PiRedTyPack.codomN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA)
  (codomN' := @PiRedTyPack.codomN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA')
  (codRed := (@PiRedTyPack.codRed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (codRed' := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA'))
  (eqPi : [Γ |- PiRedTyPack.prod ΠA ≅ PiRedTyPack.prod ΠA']< wl >).

Context
  (eqvDomN : nat)
  (eqvDom : forall {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                   (Ninfl : domN <= length wl')
                   (Ninfl' : domN' <= length wl')
                   (Ninfl'' : eqvDomN <= length wl')
                   (wfΔ : [  |- Δ]< wl' >),
      equivLRPack@{k k' v} (domRed Δ wl' ρ τ Ninfl wfΔ)
        (domRed' Δ wl' ρ τ Ninfl' wfΔ))
  (eqvCodN : forall {Δ a wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                   (Ninfl : domN <= length wl')
                   (Ninfl' : domN' <= length wl')
                   (Ninfl'' : eqvDomN <= length wl')
                   (wfΔ : [  |- Δ]< wl' >)
          (ha : [domRed Δ wl' ρ τ Ninfl wfΔ| Δ ||- a : _]< wl' >)
          (ha' : [domRed' Δ wl' ρ τ Ninfl' wfΔ | Δ ||- a : _]< wl' >),
      nat)
   (eqvCod : forall {Δ a wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                    (Ninfl : domN <= length wl')
                    (Ninfl' : domN' <= length wl')
                    (Ninfl'' : eqvDomN <= length wl')
                    (wfΔ : [  |- Δ]< wl' >)
                    (ha : [domRed Δ wl' ρ τ Ninfl wfΔ| Δ ||- a : _]< wl' >)
                    (ha' : [domRed' Δ wl' ρ τ Ninfl' wfΔ | Δ ||- a : _]< wl' >)
                    {wl''} (τ' : wl'' ≤ε wl')
                    (Minfl : codomN _ _ _ ρ τ Ninfl wfΔ ha <= length wl'')
                    (Minfl' : codomN' _ _ _ ρ τ Ninfl' wfΔ ha' <= length wl'')
                    (Minfl'' : eqvCodN ρ τ Ninfl Ninfl' Ninfl'' wfΔ ha ha' <= length wl''),
       equivLRPack@{k k' v} (codRed Δ a wl' ρ τ Ninfl wfΔ ha wl'' τ' Minfl)
              (codRed' Δ a wl' ρ τ Ninfl' wfΔ ha' wl'' τ' Minfl')).

Lemma ΠIrrelevanceTyEq B :
  [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
Proof.
  intros [] ; cbn in *.
  unshelve econstructor ; [exact dom | exact cod | ..].
  - exact (max (max domN0 domN) eqvDomN).
  - intros ; cbn in *.
    unshelve eapply (max (max _ _) _).
    + unshelve eapply (codomN Δ a l' ρ τ _ h).
      eapply Nat.max_lub_r.
      now eapply Nat.max_lub_l.
      unshelve eapply eqvDom ; try assumption.
      now eapply Nat.max_lub_r.
    + unshelve eapply (codomN0 Δ a l' ρ τ _ _) ; try assumption.
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
      * eapply Nat.max_lub_l.
        now eapply Nat.max_lub_l.
      * unshelve  eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
    + unshelve eapply (eqvCodN Δ a l' ρ τ _ _ _) ; try assumption.
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
      * now eapply Nat.max_lub_r.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
  - assumption.
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros.
    unshelve eapply eqvDom ; try eapply PeanoNat.Nat.max_lub_r ; try now eapply PeanoNat.Nat.max_lub_l.
    eassumption.
    unshelve eapply domRed0.
    eapply Nat.max_lub_l.
    now eapply Nat.max_lub_l.
  - intros; cbn in *.
    unshelve eapply eqvCod ; cbn in *.
    + eapply Nat.max_lub_r.
      now eapply Nat.max_lub_l.
    + now eapply Nat.max_lub_r.
    + cbn in *.
      unshelve eapply eqvDom ; try assumption.
      now eapply Nat.max_lub_r.
    + cbn in *.
      eapply Nat.max_lub_l.
      now eapply Nat.max_lub_l.
    + cbn in *.
      now eapply Nat.max_lub_r.
    + unshelve eapply codRed0.
      * eapply Nat.max_lub_l.
        now eapply Nat.max_lub_l.
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
Qed.

Lemma ΠIrrelevanceTm t : [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >.
Proof.
  intros []; cbn in *.
  unshelve econstructor; [ tea | ..] ; cbn in *.
  - refine (max (max redN domN) eqvDomN).
  - intros.
    unshelve refine (max (max _ _) _).
    + unshelve refine (appN Δ a l' ρ τ _ _ _ _) ; try assumption. 
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
      * eapply Nat.max_lub_l.
        now eapply Nat.max_lub_l.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
    + unshelve refine (codomN Δ a l' ρ τ _ _ _) ; try assumption. 
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
    + unshelve eapply (eqvCodN Δ a l' ρ τ _ _ _) ; try assumption.
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
      * now eapply Nat.max_lub_r.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
  - now eapply redtmwf_conv.
  - assumption.
  - apply (tm_nf_conv isnf).
    + destruct ΠA'; simpl in * ; apply eqPi.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqvCod.
    + eapply Nat.max_lub_r.
      now eapply Nat.max_lub_l.
    + now eapply Nat.max_lub_r.
    + cbn in *.
      unshelve eapply eqvDom ; try assumption.
      now eapply Nat.max_lub_r.
    + eapply Nat.max_lub_r.
      now eapply Nat.max_lub_l.
    + now eapply Nat.max_lub_r.
    + cbn in *.
      eapply app.
      eapply Nat.max_lub_l.
      now eapply Nat.max_lub_l.
  - intros; unshelve eapply eqvCod, eq.
    all: try eapply eqvDom ; try eassumption.
    all: try (eapply Nat.max_lub_r ;
              now eapply Nat.max_lub_l).
    all: try (eapply Nat.max_lub_l ;
              now eapply Nat.max_lub_l).
    all: try now eapply Nat.max_lub_r.
Defined.

Lemma ΠIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >.
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΠIrrelevanceTm.
  - exact (max (max eqN domN) eqvDomN).
  - intros.
    unshelve refine (max (max _ _) _).
    + unshelve refine (eqappN Δ a l' ρ τ _ _ _ _) ; try assumption.
      * eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
      * eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
    + unshelve refine (codomN Δ a l' ρ τ _ _ _) ; try assumption. 
      * eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
    + unshelve eapply (eqvCodN Δ a l' ρ τ _ _ _) ; try assumption.
      * eapply Nat.max_lub_r.
        now eapply Nat.max_lub_l.
      * now eapply Nat.max_lub_r.
      * unshelve eapply eqvDom ; try assumption.
        now eapply Nat.max_lub_r.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqvCod.
    + eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
    + now eapply Nat.max_lub_r.
    + cbn in *.
      unshelve eapply eqvDom ; try assumption.
      now eapply Nat.max_lub_r.
    + eapply Nat.max_lub_r ; now eapply Nat.max_lub_l.
    + now eapply Nat.max_lub_r.
    + cbn in *.
      eapply eqApp.
      eapply Nat.max_lub_l ; now eapply Nat.max_lub_l.
Qed.

End ΠIrrelevanceLemmas.

Lemma ΠIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA A lA' A'} 
  (ΠA : PiRedTyPack@{i j k l} wl Γ A lA) 
  (ΠA' : PiRedTyPack@{i' j' k' l'} wl Γ A' lA')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (domN := @PiRedTyPack.domN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA)
  (domN' := @PiRedTyPack.domN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA')
  (domRed := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (domRed' := (@PiRedTyPack.domRed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA'))
  (codomN := @PiRedTyPack.codomN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA)
  (codomN' := @PiRedTyPack.codomN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA')
  (codRed := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA))
  (codRed' := (@PiRedTyPack.codRed  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΠA'))
  (eqPi : [Γ |- PiRedTyPack.prod ΠA ≅ PiRedTyPack.prod ΠA']< wl >)
  (eqvDomN : nat)
  (eqvDom : forall {Δ wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                   (Ninfl : domN <= length wl')
                   (Ninfl' : domN' <= length wl')
                   (Ninfl'' : eqvDomN <= length wl')
                   (wfΔ : [  |- Δ]< wl' >),
      equivLRPack@{k k' v} (domRed Δ wl' ρ τ Ninfl wfΔ)
        (domRed' Δ wl' ρ τ Ninfl' wfΔ))
  (eqvCodN : forall {Δ a wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                   (Ninfl : domN <= length wl')
                   (Ninfl' : domN' <= length wl')
                   (Ninfl'' : eqvDomN <= length wl')
                   (wfΔ : [  |- Δ]< wl' >)
          (ha : [domRed Δ wl' ρ τ Ninfl wfΔ| Δ ||- a : _]< wl' >)
          (ha' : [domRed' Δ wl' ρ τ Ninfl' wfΔ | Δ ||- a : _]< wl' >),
      nat)
   (eqvCod : forall {Δ a wl'} (ρ : Δ ≤ Γ) (τ : wl' ≤ε wl)
                    (Ninfl : domN <= length wl')
                    (Ninfl' : domN' <= length wl')
                    (Ninfl'' : eqvDomN <= length wl')
                    (wfΔ : [  |- Δ]< wl' >)
                    (ha : [domRed Δ wl' ρ τ Ninfl wfΔ| Δ ||- a : _]< wl' >)
                    (ha' : [domRed' Δ wl' ρ τ Ninfl' wfΔ | Δ ||- a : _]< wl' >)
                    {wl''} (τ' : wl'' ≤ε wl')
                    (Minfl : codomN _ _ _ ρ τ Ninfl wfΔ ha <= length wl'')
                    (Minfl' : codomN' _ _ _ ρ τ Ninfl' wfΔ ha' <= length wl'')
                    (Minfl'' : eqvCodN ρ τ Ninfl Ninfl' Ninfl'' wfΔ ha ha' <= length wl''),
       equivLRPack@{k k' v} (codRed Δ a wl' ρ τ Ninfl wfΔ ha wl'' τ' Minfl)
         (codRed' Δ a wl' ρ τ Ninfl' wfΔ ha' wl'' τ' Minfl'))
   : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (eqvDom' := fun Δ wl' ρ τ Ninfl Ninfl' Ninfl'' wfΔ =>
                           symLRPack (@eqvDom Δ wl' ρ τ Ninfl Ninfl' Ninfl'' wfΔ)).
  pose (eqvCodN' := fun Δ a wl' ρ τ Ninfl Ninfl' Ninfl'' wfΔ ha ha' =>
                           @eqvCodN Δ a wl' ρ τ Ninfl' Ninfl Ninfl'' wfΔ ha' ha ).
  pose proof (eqvCod' := fun Δ a wl' ρ τ Ninfl Ninfl' Ninfl'' wfΔ ha ha' wl'' τ' Minfl Minfl' Minfl'' =>
                           symLRPack (@eqvCod Δ a wl' ρ τ Ninfl Ninfl' Ninfl'' wfΔ ha ha' wl'' τ' Minfl Minfl' Minfl'')).
  constructor.
  - split ; unshelve eapply ΠIrrelevanceTyEq ; easy.
  - split; unshelve eapply ΠIrrelevanceTm ; easy.
  - split; unshelve eapply ΠIrrelevanceTmEq ; easy.
Qed.

(** *** Irrelevance for neutral types *)

Lemma NeIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ A A'} lA lA'
  (neA : [Γ ||-ne A]< wl >)
  (neA' : [Γ ||-ne A']< wl >)
  (RA := LRne_@{i j k l} lA neA)
  (RA' := LRne_@{i' j' k' l'} lA' neA')
  (eqAA' : [Γ ||-ne A ≅ A' | neA ]< wl >)
  : equivLRPack@{k k' v} RA RA'.
Proof.
  destruct neA as [ty], neA' as [ty'], eqAA' as [ty0']; cbn in *.
  assert (ty0' = ty'); [|subst].
  { eapply redtywf_det; tea; constructor; now eapply ty_ne_whne. }
  assert [Γ |- ty ≅ ty']< wl > as convty by gen_typing.
  split.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    all: etransitivity ; [| tea]; tea; now symmetry.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    1,4: now eapply redtmwf_conv.
    all: try match goal with |- Ne[ _ |- _ : _]< _ > => destruct red, red1; now eapply tm_ne_conv; first [eassumption|symmetry; eassumption|gen_typing] end.
    all: now eapply convneu_conv.
  + intros ??; split; intros []; econstructor; cbn in *.
    1-2,6-7: now eapply redtmwf_conv.
    all: tea.
    all: try match goal with |- Ne[ _ |- _ : _]< _ > => destruct red, red1; now eapply tm_ne_conv; first [eassumption|symmetry; eassumption|gen_typing] end.
    all: now eapply convneu_conv.
Qed.

(** *** Lemmas for conversion of reducible neutral terms at arbitrary types *)

Lemma NeNfconv {wl Γ k A A'} : [Γ |- A']< wl > -> [Γ |- A ≅ A']< wl > -> [Γ ||-NeNf k : A]< wl > -> [Γ ||-NeNf k : A']< wl >.
Proof.
  intros ?? []; econstructor; tea. 2,3: gen_typing.
  now eapply tm_ne_conv.
Qed.

Lemma NeNfEqconv {wl Γ k k' A A'} : [Γ |- A']< wl > -> [Γ |- A ≅ A']< wl > -> [Γ ||-NeNf k ≅ k' : A]< wl > -> [Γ ||-NeNf k ≅ k' : A']< wl >.
Proof.
  intros ?? []; econstructor; tea. 3: gen_typing.
  all: now eapply tm_ne_conv.
Qed.


Section NatIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {wl Γ lA lA' A A'} (NA : [Γ ||-Nat A]< wl >) (NA' : [Γ ||-Nat A']< wl >)
    (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA').
  
  Lemma NatIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma NatIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >)
    × (forall t, NatProp NA t -> NatProp NA' t).
  Proof.
    apply NatRedInduction; now econstructor.
  Qed.
   
  Lemma NatIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >)
    × (forall t u, NatPropEq NA t u -> NatPropEq NA' t u).
  Proof.
    apply NatRedEqInduction; now econstructor.
  Qed.
End NatIrrelevant.

Lemma NatIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA lA' A A'} (NA : [Γ ||-Nat A]< wl >) (NA' : [Γ ||-Nat A']< wl >)
  (RA := LRNat_@{i j k l} lA NA) (RA' := LRNat_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply NatIrrelevanceTyEq.
  - split; apply NatIrrelevanceTm.
  - split; apply NatIrrelevanceTmEq.
Qed.

Section BoolIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {wl Γ lA lA' A A'} (NA : [Γ ||-Bool A]< wl >) (NA' : [Γ ||-Bool A']< wl >)
    (RA := LRBool_@{i j k l} lA NA) (RA' := LRBool_@{i' j' k' l'} lA' NA').
  
  Lemma BoolIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma BoolIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >).
  Proof.
    intros t Ht. induction Ht. econstructor. exact red. assumption.
    induction prop ; now econstructor.
  Qed.
   
  Lemma BoolIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >).
  Proof.
    intros t u Htu ; induction Htu.
    econstructor ; [ exact redL | exact redR | ..] ; try assumption.
    induction prop ; now econstructor.
  Qed.
End BoolIrrelevant.

Lemma BoolIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA lA' A A'} (NA : [Γ ||-Bool A]< wl >) (NA' : [Γ ||-Bool A']< wl >)
  (RA := LRBool_@{i j k l} lA NA) (RA' := LRBool_@{i' j' k' l'} lA' NA') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  constructor.
  - split; apply BoolIrrelevanceTyEq.
  - split; apply BoolIrrelevanceTm.
  - split; apply BoolIrrelevanceTmEq.
Qed.



Section EmptyIrrelevant.
  Universe i j k l i' j' k' l'.

  Context {wl Γ lA lA' A A'} (NA : [Γ ||-Empty A]< wl >) (NA' : [Γ ||-Empty A']< wl >)
    (RA := LREmpty_@{i j k l} lA NA) (RA' := LREmpty_@{i' j' k' l'} lA' NA').
  
  Lemma EmptyIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA]< wl > -> [Γ ||-<lA'> A' ≅ B | RA']< wl >.
  Proof.
    intros []; now econstructor.
  Qed.

  Lemma EmptyIrrelevanceTm :
    (forall t, [Γ ||-<lA> t : A | RA]< wl > -> [Γ ||-<lA'> t : A' | RA']< wl >).
  Proof.
    intros t Ht. induction Ht; now econstructor.
  Qed.
   
  Lemma EmptyIrrelevanceTmEq :
    (forall t u, [Γ ||-<lA> t ≅ u : A | RA]< wl > -> [Γ ||-<lA'> t ≅ u : A' | RA']< wl >).
  Proof.
    intros t u Htu. induction Htu. now econstructor.
  Qed.
End EmptyIrrelevant.

Lemma EmptyIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {wl Γ lA lA' A A'} (NA : [Γ ||-Empty A]< wl >) (NA' : [Γ ||-Empty A']< wl >)
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

Definition IHStatement lA lA' :=
  (forall l0 (ltA : l0 << lA) (ltA' : l0 << lA'),
      prod@{v v}
        (forall wl Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ]< wl > <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ]< wl >)
        (forall wl Γ t
           (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ]< wl >)
           (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ]< wl >)
           u,
            [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ≅ u | lr1 ]< wl > <≈>
            [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ≅ u | lr2 ]< wl >)).

Lemma UnivIrrelevanceLRPack
  {wl Γ lA lA' A A'}
  (IH : IHStatement lA lA')
  (hU : [Γ ||-U<lA> A]< wl >) (hU' : [Γ ||-U<lA'> A']< wl >)
  (RA := LRU_@{i j k l} hU) (RA' := LRU_@{i' j' k' l'} hU') :
  equivLRPack@{k k' v} RA RA'.
Proof.
  revert IH; destruct hU as [_ []], hU' as [_ []]; intro IH; destruct (IH zero Oi Oi) as [IHty IHeq].
  constructor.
  + intros; cbn; split; intros []; now constructor.
  + intros ?; destruct (IHty wl Γ t) as [tfwd tbwd]; split; intros [];
      unshelve econstructor.
    7: now apply tfwd.
    11: now apply tbwd.
    all : tea.
  + cbn ; intros ? ?;
    destruct (IHty wl Γ t) as [tfwd tbwd];
    destruct (IHty wl Γ u) as [ufwd ubwd].
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

Lemma LRIrrelevantPreds {lA lA'}
  (IH : IHStatement lA lA')
  (wl : wfLCon) (Γ : context) (A A' : term)
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' wl Γ A' eqTyA' redTmA' eqTmA')
  (RA := Build_LRPack wl Γ A eqTyA redTmA eqTmA)
  (RA' := Build_LRPack wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (fun wl Γ l0 ltA ltA' => fst (IH l0 ltA ltA') wl Γ) as IHty.
  pose proof (fun wl Γ l0 ltA ltA' => snd (IH l0 ltA ltA') wl Γ) as IHeq.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? h1 | ? ? ? neA | ? ? A ΠA HAad IHdom IHcod | ?? NA | ?? NA | ?? NA]
    in RA, A', RA', eqTyA', eqTmA', redTmA', lrA', he, s |- *.
  - destruct lrA' as [? ? h2 | | | | |]; try solve [destruct s] ; clear s.
    now apply UnivIrrelevanceLRPack.
  - destruct lrA' as [|? ? A' neA' | | | |] ; try solve [destruct s] ; clear s.
    exact (NeIrrelevanceLRPack lA lA' neA neA' he).
  - cbn in *.
    destruct lrA' as [| | ? ? A' ΠA' HAad' | | |] ; try solve [destruct s] ; clear s.
    pose (PA := PiRedTyPack.pack ΠA HAad).
    pose (PA' := PiRedTyPack.pack ΠA' HAad').
    destruct he as [dom0 cod0 ??? domRed ? codRed], ΠA' as [dom1 cod1].
    assert (tProd dom0 cod0 = tProd dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
    inversion ePi ; subst ; clear ePi.
    unshelve eapply (ΠIrrelevanceLRPack PA PA').
    + exact domN.
    + intros ; unshelve eapply codomN ; try assumption.
    + eassumption.
    + cbn in *.
      intros; unshelve eapply IHdom.
      1: now eapply (LRAd.adequate (PiRedTyPack.domRed PA' _ _ _ _)).
      now eapply domRed.
    + intros; unshelve eapply IHcod.
      1: eapply (LRAd.adequate (PiRedTyPack.codRed PA' _ _ _ _ _ _ _)).
      now eapply codRed. 
  - destruct lrA' as [| | ? A' ΠA' HAad'| | |] ; try solve [destruct s] ; clear s.
    apply (NatIrrelevanceLRPack (lA:=lA) (lA':=lA')).
  - destruct lrA' as [| | ? A' ΠA' HAad'| | |] ; try solve [destruct s] ; clear s.
    apply (BoolIrrelevanceLRPack (lA:=lA) (lA':=lA')).
  - destruct lrA' as [| | ? A' ΠA' HAad'| | |] ; try solve [destruct s] ; clear s.
    apply (EmptyIrrelevanceLRPack (lA:=lA) (lA':=lA')).
Qed.


Lemma LRIrrelevantCumTy {lA}
  (IH : IHStatement lA lA)
  (wl : wfLCon) (Γ : context) (A : term)
  : [ LogRel@{i j k l} lA | Γ ||- A ]< wl > -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ]< wl >.
Proof.
  intros [ [] lrA ] ; cbn in lrA.
  induction lrA as [? ? ? [l1 lt1] | ? | ? ? A [] [] IHdom IHcod|?? NEA|?? NEA |?? NEA].
  - eapply LRU_. econstructor ; tea.
  - eapply LRne_. exact neA.
  - cbn in *. eapply LRPi'. unshelve econstructor.
    7: eassumption.
    4,5,6: tea.
    + assumption.
    + exact IHdom.
    + intros Δ a wl' ρ τ Ninfl tΔ ra.
      eapply codomN.
      destruct (LRIrrelevantPreds IH wl' Δ (dom⟨ρ⟩) (dom⟨ρ⟩)
                  (domAd Δ wl' ρ τ Ninfl tΔ)
                  (IHdom Δ wl' ρ τ Ninfl tΔ : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHdom Δ wl' ρ τ Ninfl tΔ))
                  (LRTyEqRefl (domAd Δ wl' ρ τ Ninfl tΔ))) as [_ irrTmRed _].
      eapply (snd (irrTmRed a)). exact ra.
    + intros Δ a wl' ρ τ Ninfl tΔ ra.
      now eapply IHcod.
    + assumption.
    + cbn. intros Δ a b wl' ρ τ Ninfl tΔ ra rb rab wl'' τ' Minfl.
      destruct (LRIrrelevantPreds IH wl' Δ (dom⟨ρ⟩) (dom⟨ρ⟩)
                  (domAd  Δ wl' ρ τ Ninfl tΔ) (IHdom  Δ wl' ρ τ Ninfl tΔ : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHdom  Δ wl' ρ τ Ninfl tΔ))
                  (LRTyEqRefl (domAd  Δ wl' ρ τ Ninfl tΔ))) as [_ irrTmRed irrTmEq].
      destruct (LRIrrelevantPreds IH wl'' Δ (cod[a .: ρ >> tRel]) (cod[a .: ρ >> tRel])
                  (codAd Δ a wl' ρ τ Ninfl tΔ (snd (irrTmRed a) ra) wl'' τ' Minfl)
                  (IHcod Δ wl' a ρ τ Ninfl tΔ (snd (irrTmRed a) ra) wl'' τ' Minfl 
                    : LRPackAdequate (LogRel@{i' j' k' l'} lA) (IHcod Δ wl' a ρ τ Ninfl tΔ (snd (irrTmRed a) ra) wl'' τ' Minfl))
                  (LRTyEqRefl (codAd Δ a wl' ρ τ Ninfl tΔ (snd (irrTmRed a) ra) wl'' τ' Minfl)))
        as [irrTyEq _ _].
      eapply (fst (irrTyEq (cod[b .: ρ >> tRel]))).
      eapply codExt.
      exact (snd (irrTmRed b) rb).
      exact (snd (irrTmEq a b) rab).
  - now eapply LRNat_.
  - now eapply LRBool_.
  - now eapply LREmpty_.
Qed.


Lemma IrrRec0 : IHStatement zero zero.
Proof.
  intros ? ltA; inversion ltA.
Qed.

End LRIrrelevantInductionStep.

Theorem IrrRec@{i j k l i' j' k' l'} {lA} {lA'} :
  IHStatement@{i j k l i' j' k' l'} lA lA'.
Proof.
  intros l0 ltA ltA'.
  destruct ltA. destruct ltA'. cbn in *.
  split.
  - intros wl Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros wl Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} wl Γ t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (LRTyEqRefl_ lr1)) as [tyEq _ _].
    exact (tyEq u).
Qed.

Theorem LRIrrelevantCum@{i j k l i' j' k' l'}
  (wl : wfLCon) (Γ : context) (A A' : term) {lA lA'}
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA wl Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  @and3@{v v v} (forall B, eqTyA B <≈> eqTyA' B)
    (forall t, redTmA t <≈> redTmA' t)
    (forall t u, eqTmA t u <≈> eqTmA' t u).
Proof.
  exact (LRIrrelevantPreds@{i j k l i' j' k' l'} IrrRec wl Γ A A' lrA lrA').
Qed.

Theorem LRCumulative@{i j k l i' j' k' l'} {lA}
  {wl : wfLCon} {Γ : context} {A : term}
  : [ LogRel@{i j k l} lA | Γ ||- A ]< wl > -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ]< wl >.
Proof.
  exact (LRIrrelevantCumTy@{i j k l i' j' k' l'} IrrRec wl Γ A).
Qed.

Corollary LRCumulative' @{i j k l i' j' k' l'} {lA}
  {wl : wfLCon} {Γ : context} {A A' : term}
  : A = A' -> [ LogRel@{i j k l} lA | Γ ||- A ]< wl > -> [ LogRel@{i' j' k' l'} lA | Γ ||- A' ]< wl >.
Proof.
  intros ->; apply LRCumulative.
Qed.
End LRIrrelevant.


Corollary TyEqIrrelevantCum wl Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A eqTyA' redTmA' eqTmA') :
  forall B, eqTyA B -> eqTyA' B.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' wl Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > -> [Γ ||-< lA' > A ≅ B | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']< wl >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > -> [Γ ||-< lA' > A' ≅ B | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']< wl >) :
  forall B, [Γ ||-< lA > A ≅ B | lrA]< wl > -> [Γ ||-< lA' > A' ≅ B | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary RedTmIrrelevantCum wl Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A eqTyA' redTmA' eqTmA') :
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmRedIrrelevantCum@{i j k l i' j' k' l'} lA lA' wl Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevantCum'@{i j k l i' j' k' l'} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']< wl >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']< wl >) :
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.


Corollary TmEqIrrelevantCum wl Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A eqTyA' redTmA' eqTmA') :
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' wl Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]< wl >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']< wl >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevant'@{i j k l} lA lA' wl Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']< wl >) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.



Corollary TyEqSym wl Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' -> eqTyA' A.
Proof.
  intros.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
  1: eauto.
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqSym lA lA' wl Γ A A' (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A']< wl >) :
  [Γ ||-< lA > A ≅ A' | lrA]< wl > -> [Γ ||-< lA' > A' ≅ A | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqSym.
Qed.

Corollary RedTmConv wl Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
Qed.

Corollary LRTmRedConv lA lA' wl Γ A A' (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A' ]< wl >) :
  [Γ ||-< lA > A ≅ A' | lrA ]< wl > ->
  forall t, [Γ ||-< lA > t : A | lrA]< wl > -> [Γ ||-< lA' > t : A' | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmConv.
Qed.

Corollary TmEqRedConv wl Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA wl Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' wl Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ _ lrA lrA').
Qed.

Corollary LRTmEqRedConv lA lA' wl Γ A A' (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A']< wl >) :
  [Γ ||-< lA > A ≅ A' | lrA ]< wl > ->
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqRedConv.
Qed.

Corollary LRTmTmEqIrrelevant' lA lA' wl Γ A A' (e : A = A')
  (lrA : [Γ ||-< lA > A]< wl >) (lrA' : [Γ ||-< lA'> A']< wl >) :
  forall t u, 
  [Γ ||-<lA> t : A | lrA]< wl > × [Γ ||-< lA > t ≅ u : A | lrA]< wl > -> 
  [Γ ||-<lA'> t : A' | lrA']< wl > × [Γ ||-< lA' > t ≅ u : A' | lrA']< wl >.
Proof.
  intros ?? []; split; [eapply LRTmRedIrrelevant'| eapply LRTmEqIrrelevant']; tea.
Qed.

Set Printing Primitive Projection Parameters.

Lemma NeNfEqSym {wl Γ k k' A} : [Γ ||-NeNf k ≅ k' : A]< wl > -> [Γ ||-NeNf k' ≅ k : A]< wl >.
Proof.
  intros []; constructor; tea; now symmetry.
Qed.

Lemma LRTmEqSym@{h i j k l} lA wl Γ A (lrA : [LogRel@{i j k l} lA | Γ ||- A]< wl >) : forall t u,
  [Γ ||-<lA> t ≅ u : A |lrA]< wl > -> [Γ ||-<lA> u ≅ t : A |lrA]< wl >.
Proof.
  pattern lA, wl, Γ, A, lrA. apply LR_rect_TyUr; clear lA Γ A lrA.
  - intros * []. unshelve econstructor; try eassumption.
    1: symmetry; eassumption.
    (* Need an additional universe level h < i *)
    eapply TyEqSym@{h i j k h i j k}. 3:exact relEq.
    all: eapply LogRelRec_unfold; eapply LRAd.adequate; eassumption.
  - intros * []. unshelve econstructor.
    3,4: eassumption.
    1,2: eassumption.
    symmetry; eassumption.
  - intros * ihdom ihcod * []. unshelve econstructor.
    1,2: eassumption.
    assumption.
    assumption.
    1: symmetry; eassumption.
    intros. apply ihcod. now eapply eqApp.
  - intros ???? NA.
    set (G := _); enough (h : G × (forall t u, NatPropEq NA t u -> NatPropEq NA u t)) by apply h.
    subst G; apply NatRedEqInduction.
    1-3: now econstructor.
    intros. constructor; now eapply NeNfEqSym.
  - intros ???? NA.
    intros t u [? ? ? ? ? ? ? prop]. induction prop.
    + econstructor; eauto ; now econstructor.
    + econstructor; eauto ; now econstructor.
    + econstructor ; eauto.
      * easy.
      * constructor. now eapply NeNfEqSym.
  - intros ???? NA.
    intros t u [? ? ? ? ? ? ? prop]. induction prop.
    econstructor ; eauto.
    * easy.
    * constructor. now eapply NeNfEqSym.
Qed.

End Irrelevances.


(** ** Tactics for irrelevance, with and without universe cumulativity *)

Ltac irrelevanceCum0 :=
  lazymatch goal with
  | [|- [_ ||-<_> _]< _ >] => (now eapply LRCumulative) + eapply LRCumulative'
  | [|- [_ | _ ||- _ ≅ _ ]< _ > ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ | _ ]< _ > ] => eapply LRTyEqIrrelevantCum'
  | [|- [_ | _ ||- _ : _ ]< _ > ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ ||-<_> _ : _ | _ ]< _ > ] => eapply LRTmRedIrrelevantCum'
  | [|- [_ | _ ||- _ ≅ _ : _ ]< _ > ] => eapply LRTmEqIrrelevantCum'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ]< _ > ] => eapply LRTmEqIrrelevantCum'
  end.

Ltac irrelevanceCum := irrelevanceCum0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceCumRefl := irrelevanceCum0 ; [reflexivity|].

Ltac irrelevance0 :=
  lazymatch goal with
  | [|- [_ | _ ||- _ ≅ _ ]< _ > ] => eapply LRTyEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ | _ ]< _ > ] => eapply LRTyEqIrrelevant'
  | [|- [_ | _ ||- _ : _ ]< _ > ] => eapply LRTmRedIrrelevant'
  | [|- [_ ||-<_> _ : _ | _ ]< _ > ] => eapply LRTmRedIrrelevant'
  | [|- [_ | _ ||- _ ≅ _ : _ ]< _ > ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ ≅ _ : _ | _ ]< _ > ] => eapply LRTmEqIrrelevant'
  | [|- [_ ||-<_> _ : _ | _]< _ > × [_ ||-<_> _≅ _ : _ | _]< _ >] => eapply LRTmTmEqIrrelevant'
  end.

Ltac irrelevance := irrelevance0 ; [|eassumption] ; try first [reflexivity| now bsimpl].

Ltac irrelevanceRefl := irrelevance0 ; [reflexivity|].
