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

  Definition equivLRPack {Γ Γ' A A'} (P: LRPack@{i} Γ A) (P': LRPack@{i'} Γ' A'):=
    and3@{v v v} 
      (forall B, [P | Γ ||- A ≅ B] <≈> [P' | Γ' ||- A' ≅ B])
      (forall t, [P | Γ ||- t : A] <≈> [P' | Γ' ||- t : A'])
      (forall t u, [P | Γ ||- t ≅ u : A] <≈> [P' | Γ' ||- t ≅ u : A']).
End EquivLRPack.

Lemma symLRPack@{i i' v} {Γ Γ' A A'} {P: LRPack@{i} Γ A} {P': LRPack@{i'} Γ' A'} :
    equivLRPack@{i i' v} P P' -> equivLRPack@{i' i v} P' P.
Proof.
  intros [eqT rTm eqTm]; constructor;split ;
    apply eqT + apply rTm + apply eqTm.
Qed.
  

Record equivPolyRed@{i j k l i' j' k' l' v}
  {Γ l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} Γ l shp pos}
  {PA' : PolyRed@{i' j' k' l'} Γ l' shp' pos'} :=
  {
    eqvShp : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ wfΔ' : [  |- Δ]),
          equivLRPack@{k k' v} (PolyRed.shpRed PA ρ wfΔ) (PolyRed.shpRed PA' ρ wfΔ') ;
    eqvPos : forall {Δ a} (ρ : Δ ≤ Γ) (wfΔ wfΔ' : [  |- Δ])
          (ha : [PolyRed.shpRed PA ρ wfΔ| Δ ||- a : _])
          (ha' : [PolyRed.shpRed PA' ρ wfΔ' | Δ ||- a : _]),
          equivLRPack@{k k' v} 
            (PolyRed.posRed PA ρ wfΔ ha)
            (PolyRed.posRed PA' ρ wfΔ' ha')
  }.

Arguments equivPolyRed : clear implicits.
Arguments equivPolyRed {_ _ _ _ _ _ _} _ _.

Lemma equivPolyRedSym@{i j k l i' j' k' l' v}
  {Γ l l' shp shp' pos pos'}
  {PA : PolyRed@{i j k l} Γ l shp pos}
  {PA' : PolyRed@{i' j' k' l'} Γ l' shp' pos'} :
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
  (ΠA : ParamRedTy@{i j k l} tProd Γ lA A) 
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd Γ lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom)])
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy)])
  (eqv : equivPolyRed ΠA ΠA').

Lemma ΠIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | |econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΠA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now unshelve eapply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos); tea.
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
  - intros; unshelve eapply eqv.(eqvPos); tea.
    2: now auto.
    now unshelve eapply eqv.(eqvShp).
  - intros; unshelve eapply eqv.(eqvPos), eq; tea.
    all: now unshelve eapply eqv.(eqvShp).
Defined.

Lemma ΠIrrelevanceTmEq t u : [Γ ||-<lA> t ≅ u : A | RA] -> [Γ ||-<lA'> t ≅ u : A' | RA'].
Proof.
  intros [] ; cbn in *; unshelve econstructor.
  1,2: now eapply ΠIrrelevanceTm.
  - now eapply convtm_conv.
  - intros; unshelve eapply eqv.(eqvPos); tea.
    2: now auto.
    now unshelve eapply eqv.(eqvShp).
Qed.

End ΠIrrelevanceLemmas.

Lemma ΠIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'} 
  (ΠA : ParamRedTy@{i j k l} tProd Γ lA A) 
  (ΠA' : ParamRedTy@{i' j' k' l'} tProd Γ lA' A')
  (RA := LRPi' ΠA)
  (RA' := LRPi' ΠA')
  (eqDom : [Γ |- ΠA.(ParamRedTy.dom) ≅ ΠA'.(ParamRedTy.dom)])
  (eqPi : [Γ |- ΠA.(outTy) ≅ ΠA'.(outTy) ])
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
  (ΣA : ParamRedTy@{i j k l} tSig Γ lA A) 
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig Γ lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom)])
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy)])
  (eqv : equivPolyRed ΣA ΣA').

Lemma ΣIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [????? []] ; cbn in *; econstructor; [| | |econstructor].
  - now gen_typing.
  - transitivity (ParamRedTyPack.dom ΣA); [now symmetry|tea].
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now unshelve eapply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos); tea.
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
  (ΣA : ParamRedTy@{i j k l} tSig Γ lA A) 
  (ΣA' : ParamRedTy@{i' j' k' l'} tSig Γ lA' A')
  (RA := LRSig' ΣA)
  (RA' := LRSig' ΣA')
  (eqDom : [Γ |- ΣA.(ParamRedTy.dom) ≅ ΣA'.(ParamRedTy.dom)])
  (eqSig : [Γ |- ΣA.(outTy) ≅ ΣA'.(outTy) ])
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

Lemma NeNfconv {Γ k A A'} : [Γ |- A'] -> [Γ |- A ≅ A'] -> [Γ ||-NeNf k : A] -> [Γ ||-NeNf k : A'].
Proof.
  intros ?? []; econstructor; tea. all: gen_typing.
Qed.

Lemma NeNfEqconv {Γ k k' A A'} : [Γ |- A'] -> [Γ |- A ≅ A'] -> [Γ ||-NeNf k ≅ k' : A] -> [Γ ||-NeNf k ≅ k' : A'].
Proof.
  intros ?? []; econstructor; tea. gen_typing.
Qed.


(** *** Irrelevance for W types *)

Lemma subst_single_wk_id_left cod a {Γ Δ} (ρ : Δ ≤ Γ) : 
  cod[a.:ρ >>tRel] = cod[a.: (wk_id ∘wρ) >>tRel].
Proof. intros; now bsimpl. Qed.


Section WIrrelevanceLemmas.
Universe i j k l i' j' k' l' v.
Context {Γ lA A lA' A'} (wfΓ wfΓ' : [|-Γ])
  (WA : WRedTy@{i j k l} Γ lA A) 
  (WA' : WRedTy@{i' j' k' l'} Γ lA' A')
  (dom:=WA.(ParamRedTy.dom))
  (dom':=WA'.(ParamRedTy.dom))
  (cod:=WA.(ParamRedTy.cod))
  (cod':=WA'.(ParamRedTy.cod))
  (RA := WRedTy.LRW wfΓ WA)
  (RA' := WRedTy.LRW wfΓ' WA')
  (codRedConv : forall Δ a (ρ : Δ ≤ Γ) (h :[|- Δ]) (ha : [PolyRedPack.shpRed WA ρ h | Δ ||- a : _]),
         [PolyRedPack.posRed WA ρ h ha | Δ ||- cod[a .: ρ >> tRel] ≅ cod'[a .: ρ >> tRel]])
  (eqW : [Γ |- WA.(outTy) ≅ WA'.(outTy)])
  (eqv : equivPolyRed WA WA').
  (* (eqvcod0 : forall Δ (ρ : Δ ≤ Γ) (wfΔ wfΔ': [|-Δ]), 
    equivLRPack (WA.(WRedTy.codRed0) ρ wfΔ) (WA'.(WRedTy.codRed0) ρ wfΔ')). *)

(* TODO: factor this lemma with one for Π and Σ *)
Lemma WIrrelevanceTyEq B : [Γ ||-<lA> A ≅ B | RA] -> [Γ ||-<lA'> A' ≅ B | RA'].
Proof.
  intros  [???? []] ; cbn in *; econstructor; [| |econstructor].
  - now gen_typing.
  - cbn; etransitivity; [|tea]; now symmetry.
  - intros; now unshelve eapply eqv.(eqvShp).
  - intros; cbn; unshelve eapply eqv.(eqvPos); tea.
    2: eauto.
    now eapply eqv.(eqvShp).
Qed.

Lemma supContTy_conv {Δ a} (ρ : Δ ≤ Γ) (h :[|- Δ]) (Ra : [PolyRedPack.shpRed WA (wk_id ∘w ρ) h | Δ ||- a⟨@wk_id Δ⟩ : _])
    (coda := cod⟨wk_up dom ρ⟩[a..])
    (coda' := cod'⟨wk_up dom' ρ⟩[a..]) :
  [Δ |- tProd coda WA.(outTy)⟨wk_step coda ρ⟩ ≅ tProd coda' WA'.(outTy)⟨wk_step coda' ρ⟩].
Proof.
  rewrite <-2!wk_step_wk1,2!wk1_ren_on.
  apply convty_simple_arr; tea.
  3: now eapply convty_wk.
  + unfold coda; rewrite <-wk_up_ren_subst_id, subst_single_wk_id_left.
    eapply escape. unshelve eapply WA.(PolyRed.posRed); tea.
    now erewrite <- (wk_id_ren_on _ a).
  + unfold coda, coda'.
    rewrite <-2!wk_up_ren_subst_id, subst_single_wk_id_left, (subst_single_wk_id_left cod').
    eapply escapeEq.
    unshelve eapply codRedConv; tea.  
    now erewrite <- (wk_id_ren_on _ a). 
Qed.

#[local]
Lemma instWCodRed_irrelevance {Δ} {a} (ρ : Δ ≤ Γ) (wfΔ wfΔ' : [|- Δ])
  (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _])
  (Ra' : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA'.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _])
  Ξ (ρ' : Ξ ≤ Δ) (wfΞ wfΞ' : [|-Ξ]) :
  equivLRPack@{v v v} (WRedTm.instWCodRed ρ wfΔ Ra Ξ ρ' wfΞ) (WRedTm.instWCodRed ρ wfΔ' Ra' Ξ ρ' wfΞ').
Proof.
  unfold WRedTm.instWCodRed.
  set (e := eq_ind_r _ _ _); set (e' := eq_ind_r _ _ _); clearbody e e'. cbn in e, e'.
  set (P := @eq_rect _ _ _ _).
  set (P' := @eq_rect _ _ _ _).
  refine (match e as e in _ = A return equivLRPack (P A e) (P' _ e') with | eq_refl => _ end).
  refine (match e' as e' in _ = A' return equivLRPack (P _ eq_refl) (P' _ e') with | eq_refl => _ end).
  cbn. eapply eqv.
Qed.

Lemma funRedTm_irrelevance {Δ} {a k} (ρ : Δ ≤ Γ) (wfΔ wfΔ' : [|- Δ])
  (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _])
  (Ra' : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA'.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _]) 
  (Rk : WRedTm.funRedTm Δ ρ wfΔ k Ra (fun Δ => WRedTm WA (Δ:=Δ)) (fun Δ => WRedTmEq WA (Δ:=Δ)))
  (ihRed : forall (Ξ : context) (ρ' : Ξ ≤ Δ) (wfΞ : [ |-[ ta ] Ξ]) (b : term),
    [WRedTm.instWCodRed ρ wfΔ Ra Ξ ρ' wfΞ | _ ||- b : _] -> forall wfΔ' : [ |-[ ta ] Ξ], WRedTm WA' (ρ' ∘w ρ) wfΔ' (tApp (PiRedTm.nf Rk)⟨ρ'⟩ b))
  (ihRedEq : forall (Ξ : context) (ρ' : Ξ ≤ Δ) (wfΞ : [ |-[ ta ] Ξ]) (b b' : term),
     [WRedTm.instWCodRed ρ wfΔ Ra Ξ ρ' wfΞ | _ ||- b : _] ->
     [WRedTm.instWCodRed ρ wfΔ Ra Ξ ρ' wfΞ | _ ||- b' : _] ->
     [WRedTm.instWCodRed ρ wfΔ Ra Ξ ρ' wfΞ | _ ||- b ≅ b' : _] ->
     forall wfΔ' : [ |-[ ta ] Ξ], WRedTmEq WA' (ρ' ∘w ρ) wfΔ' (tApp (PiRedTm.nf Rk)⟨ρ'⟩ b) (tApp (PiRedTm.nf Rk)⟨ρ'⟩ b')) :
  WRedTm.funRedTm Δ ρ wfΔ' k Ra' (fun Δ => WRedTm WA' (Δ:=Δ)) (fun Δ => WRedTmEq WA' (Δ:=Δ)).
Proof.
  pose proof (supContTy_conv ρ wfΔ (Ra _ wk_id wfΔ)).
  destruct Rk; cbn in *; unshelve econstructor; cycle 2; tea.
  * now eapply convtm_conv.
  * intros; unshelve eapply ihRed; tea.
    now eapply instWCodRed_irrelevance.
  * intros; cbn in *. unshelve eapply ihRedEq; tea.
    all: now eapply instWCodRed_irrelevance.
  * now eapply redtmwf_conv.
Defined.

Lemma WIrrelevanceTm_mut :
  WRedInductionConcl WA
    (fun Δ ρ wfΔ t Rt => forall wfΔ', WRedTm WA' ρ wfΔ' t)
    (fun Δ ρ wfΔ t Pt => forall wfΔ', WProp WA' ρ wfΔ' t)
    (fun Δ ρ wfΔ t u Rtu => forall wfΔ', WRedTmEq WA' ρ wfΔ' t u)
    (fun Δ ρ wfΔ t u Ptu => forall wfΔ', WPropEq WA' ρ wfΔ' t u).
Proof.
  unfold outTy in *.
  apply WRedInduction.
  - intros; econstructor; tea.
    + eapply redtmwf_conv; tea; now eapply convty_wk.
    + eapply convtm_conv; tea; now eapply convty_wk.
    + eauto.
  - intros; unshelve econstructor; tea.
    + intros; unshelve eapply eqv; eauto.
    + now eapply eqv.
    + intros; unshelve eapply eqv; eauto.
    + now eapply funRedTm_irrelevance.
  - intros. constructor; eapply NeNfconv; tea.
    2: now eapply convty_wk.
    eapply wft_wk; tea; eapply wft_W; destruct WA' as [?????[]]; tea.
  - intros; econstructor; tea.
    4: eauto.
    1,2: eapply redtmwf_conv; tea; now eapply convty_wk.
    eapply convtm_conv; tea; now eapply convty_wk.
  - intros.
    pose proof (supContTy_conv ρ wfΔ (Ra _ wk_id wfΔ)).
    pose proof (supContTy_conv ρ wfΔ' (Ra' _ wk_id wfΔ')).
    unshelve econstructor; tea.
    + intros; unshelve eapply eqv; eauto.  
    + intros; unshelve eapply eqv.
      2: tea.  
    + now eapply eqv.
    (* + now eapply eqv. *)
    + intros; unshelve eapply eqv; eauto.
    + intros; unshelve eapply eqv; eauto.
    + intros; now unshelve eapply eqv.
    + intros; now unshelve eapply eqv.
    + intros; now unshelve eapply eqv.
    + intros; now unshelve eapply eqv.
    (* + now eapply funRedTm_irrelevance.
    + now eapply funRedTm_irrelevance. *)
    + destruct Rkk'; cbn in *; unshelve econstructor; cbn; tea.
      * eapply funRedTm_irrelevance; tea.
      * eapply funRedTm_irrelevance; tea.
      * cbn; eapply convtm_conv; tea.
      * intros. unshelve eapply X3; tea.
        unshelve eapply instWCodRed_irrelevance; tea.
  - intros; constructor; eapply NeNfEqconv; tea. 
    2: now eapply convty_wk.
    eapply wft_wk; tea; eapply wft_W; destruct WA' as [?????[]]; tea.
  Qed.
  
End WIrrelevanceLemmas.

Lemma WIrrelevance@{i j k l i' j' k' l' v}
  {Γ lA A lA' A'} (wfΓ wfΓ' : [|-Γ])
  (WA : WRedTy@{i j k l} Γ lA A) 
  (WA' : WRedTy@{i' j' k' l'} Γ lA' A')
  (dom:=WA.(ParamRedTy.dom))
  (dom':=WA'.(ParamRedTy.dom))
  (cod:=WA.(ParamRedTy.cod))
  (cod':=WA'.(ParamRedTy.cod))
  (RA := WRedTy.LRW wfΓ WA)
  (RA' := WRedTy.LRW wfΓ' WA')
  (codRedConv : forall Δ a (ρ : Δ ≤ Γ) (h :[|- Δ]) (ha : [PolyRedPack.shpRed WA ρ h | Δ ||- a : _]),
         [PolyRedPack.posRed WA ρ h ha | Δ ||- cod[a .: ρ >> tRel] ≅ cod'[a .: ρ >> tRel]])
  (eqW : [Γ |- WA.(outTy) ≅ WA'.(outTy)])
  (eqv : equivPolyRed WA WA') :
  (* (eqvcod0 : forall Δ (ρ : Δ ≤ Γ) (wfΔ wfΔ' : [|-Δ]), 
    equivLRPack@{v v v} (WA.(WRedTy.codRed0) ρ wfΔ) (WA'.(WRedTy.codRed0) ρ wfΔ')) : *)
  equivLRPack@{v v v } RA RA'.
Proof.
  assert (forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (ha : [PolyRedPack.shpRed WA' ρ h | _ ||- a : _]),
    [PolyRedPack.posRed WA' ρ h ha | _ ||- _ ≅ (ParamRedTy.cod WA)[a .: ρ >> tRel]]).
  1:{
    intros. unshelve eapply eqv; tea.
    1: now eapply eqv.
    eapply reflLRTyEq.
  }
  pose proof (equivPolyRedSym eqv).
  split.
  2,3: split; intros; eapply WIrrelevanceTm_mut; tea; now symmetry.
  split; now eapply WIrrelevanceTyEq.
Qed.

(** *** Irrelevance for Identity types *)

Section IdIrrelevance.
  Universe i j k l i' j' k' l' v.
  Context {Γ lA A lA' A'} 
    (IA : IdRedTy@{i j k l} Γ lA A) 
    (IA' : IdRedTy@{i' j' k' l'} Γ lA' A')
    (RA := LRId' IA)
    (RA' := LRId' IA')
    (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy)])
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
  (eqId : [Γ |- IA.(IdRedTy.outTy) ≅ IA'.(IdRedTy.outTy)])
  (eqv : equivLRPack@{k k' v} IA.(IdRedTy.tyRed) IA'.(IdRedTy.tyRed))
  (lhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.lhs) ≅  IA'.(IdRedTy.lhs) : _ ])
  (rhsconv : [IA.(IdRedTy.tyRed) | Γ ||- IA.(IdRedTy.rhs) ≅  IA'.(IdRedTy.rhs) : _])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  pose proof (IA.(IdRedTy.tyPER)).
  pose proof (symLRPack eqv).
  assert (eqId' : [Γ |- IA'.(IdRedTy.outTy) ≅ IA.(IdRedTy.outTy)]) by now symmetry.
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.lhs) ≅  IA.(IdRedTy.lhs) : _ ] by (apply eqv; now symmetry).
  assert [IA'.(IdRedTy.tyRed) | Γ ||- IA'.(IdRedTy.rhs) ≅  IA.(IdRedTy.rhs) : _ ] by (apply eqv; now symmetry).
  constructor.
  - split; now apply IdIrrelevanceTyEq.
  - split; now apply IdIrrelevanceTm.
  - split; now apply IdIrrelevanceTmEq.
Qed.

(** *** Irrelevance for neutral types *)

Lemma NeIrrelevanceLRPack@{i j k l i' j' k' l' v}
  {Γ A A'} lA lA'
  (neA : [Γ ||-ne A])
  (neA' : [Γ ||-ne A'])
  (RA := LRne_@{i j k l} lA neA)
  (RA' := LRne_@{i' j' k' l'} lA' neA')
  (eqAA' : [Γ ||-ne A ≅ A' | neA ])
  : equivLRPack@{k k' v} RA RA'.
Proof.
  destruct neA as [ty], neA' as [ty'], eqAA' as [ty0']; cbn in *.
  assert (ty0' = ty'); [|subst].
  { eapply redtywf_det; tea; constructor; eapply convneu_whne; first [eassumption|symmetry; eassumption]. }
  assert [Γ |- ty ≅ ty'] as convty by gen_typing.
  split.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    all: etransitivity ; [| tea]; tea; now symmetry.
  + intros ?; split; intros []; econstructor; cbn in *; tea.
    1,3: now eapply redtmwf_conv.
    all: now eapply convneu_conv; first [eassumption|symmetry; eassumption|gen_typing].
  + intros ??; split; intros []; econstructor; cbn in *.
    1-2,4-5: now eapply redtmwf_conv.
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
        (forall Γ t, [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ] <≈> [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
        (forall Γ t
           (lr1 : [ LogRelRec@{i j k} lA l0 ltA | Γ ||- t ])
           (lr2 : [ LogRelRec@{i' j' k'} lA' l0 ltA' | Γ ||- t ])
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
  + intros ?; destruct (IHty Γ t) as [tfwd tbwd]; split; intros [];
      unshelve econstructor.
    6: now apply tfwd.
    9: now apply tbwd.
    all : tea.
  + cbn ; intros ? ?;
    destruct (IHty Γ t) as [tfwd tbwd];
    destruct (IHty Γ u) as [ufwd ubwd].
    split; intros [[] []]; cbn in *; unshelve econstructor.
    3: now apply tfwd.
    5: now apply tbwd.
    6: now apply ufwd.
    8: now apply ubwd.
    (* all: apply todo. *)
    all: cbn.
    6: now refine (fst (IHeq _ _ _ _ _) _).
    7: now refine (snd (IHeq _ _ _ _ _) _).
    1-4: now econstructor.
    all: cbn; tea.
Qed.

(** ** The main theorem *)

#[local]
Lemma LRIrrelevantPreds {lA lA'}
  (IH : IHStatement lA lA')
  (Γ : context) (A A' : term)
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' redTmA' eqTmA')
  (RA := Build_LRPack Γ A eqTyA redTmA eqTmA)
  (RA' := Build_LRPack Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  equivLRPack@{k k' v} RA RA'.
Proof.
  intros he.
  set (s := ShapeViewConv lrA lrA' he).
  induction lrA as [? ? h1 | ? ? neA | ? A ΠA HAad IHdom IHcod | ?? NA | ?? NA|? A ΠA HAad IHdom IHcod | ?? IAP IAad IHPar | ?? wfΓ WAP WAad IHdom IHcod]
    in RA, A', RA', eqTyA', eqTmA', redTmA', lrA', he, s |- *.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now apply UnivIrrelevanceLRPack.
  - destruct lrA'  ; try solve [destruct s] ; clear s.
    now unshelve eapply NeIrrelevanceLRPack.
  - destruct lrA' as [| | ? A' ΠA' HAad'| | | | |] ; try solve [destruct s] ; clear s.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codRed]], ΠA' as [dom1 cod1];
    assert (tProd dom0 cod0 = tProd dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
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
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply NatIrrelevanceLRPack.
  - destruct lrA' ; try solve [destruct s] ; clear s.
    now unshelve eapply EmptyIrrelevanceLRPack.
  - destruct lrA' as [| | | | |? A' ΠA' HAad'| |] ; try solve [destruct s] ; clear s.
    pose (PA := ParamRedTy.from HAad).
    pose (PA' := ParamRedTy.from HAad').
    destruct he as [dom0 cod0 ??? [domRed codRed]], ΠA' as [dom1 cod1];
    assert (tSig dom0 cod0 = tSig dom1 cod1) as ePi
    by (eapply whredty_det ; gen_typing).
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
  - destruct lrA' as [| | | | | | ? A' IAP' IAad'| ] ; try solve [destruct s] ; clear s.
    pose (IA := IdRedTy.from IAad); pose (IA' := IdRedTy.from IAad').
    assert (IA'.(IdRedTy.outTy) = he.(IdRedTyEq.outTy)) as eId.
    1: eapply whredty_det; constructor; try constructor; [apply IA'.(IdRedTy.red)| apply he.(IdRedTyEq.red)].
    inversion eId; destruct he, IAP'; cbn in *. subst; clear eId.
    eapply (IdIrrelevanceLRPack IA IA'); tea.
    eapply IHPar; tea.
    apply IA'.(IdRedTy.tyRed).
    (* unshelve eapply escapeEq.  2: apply IdRedTy.tyRed.  now cbn. *)
  - destruct lrA' as [| | | | | | | ?? wfΓ' WAP' WAad']; try solve [destruct s]; clear s.
    pose (WA := WRedTy.from WAad).
    pose (WA' := WRedTy.from WAad').
    destruct he as [dom cod redeq ? [domRed codRed]].
    destruct WAP' as [[??? red']]; cbn in *.
    assert (eW : tW dom cod = WA'.(ParamRedTy.outTy)).
    1: unfold outTy; cbn; eapply whredty_det; gen_typing.
    inversion eW; subst; clear eW.
    eapply (WIrrelevance _ _ WA WA'); [ | |unshelve econstructor].
    + intros; eapply codRed.
    + unfold outTy; cbn. destruct WAP; cbn in *. gen_typing.
    + intros. unshelve eapply IHdom.
      2: eapply (LRAd.adequate (PolyRed.shpRed WA' _ _)).
      eapply domRed.
    + intros; unshelve eapply IHcod.
      2: eapply (LRAd.adequate (PolyRed.posRed WA' _ _ _)).
      eapply codRed.
Qed.


#[local]
Lemma LRIrrelevantCumPolyRed {lA}
  (IH : IHStatement lA lA)
  (Γ : context) (shp pos : term)
  (PA : PolyRed@{i j k l} Γ lA shp pos)
  (IHshp : forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-< lA > shp⟨ρ⟩])
  (IHpos : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
          [PolyRed.shpRed PA ρ h | _ ||- a : _] ->
          [Δ ||-< lA > pos[a .: ρ >> tRel]]) :
  PolyRed@{i' j' k' l'} Γ lA shp pos.
Proof.
  unshelve econstructor.
  + exact IHshp.
  + intros Δ a ρ tΔ ra. eapply IHpos.
    pose (shpRed := PA.(PolyRed.shpRed) ρ tΔ).
    destruct (LRIrrelevantPreds IH _ _ _
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
    destruct (LRIrrelevantPreds IH _ _ _
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
  (Γ : context) (A : term)
  : [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ].
Proof.
  intros lrA; revert IH; pattern lA, Γ, A, lrA; eapply LR_rect_TyUr ; clear lA Γ A lrA.
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
  - intros ? [] IHdom IHcod IH; cbn in *.
    eapply LRW'; unshelve econstructor.
    3,4: tea.
    unshelve eapply LRIrrelevantCumPolyRed; tea.
    + intros; now eapply IHdom.
    + intros; now eapply IHcod.
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
  - intros Γ t. split.
    + eapply (LRIrrelevantCumTy@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'}).
    + eapply (LRIrrelevantCumTy@{u i' j' k' u i j k} IrrRec0@{u i' j' k' u i j k}).
  - intros Γ t lr1 lr2 u.
    destruct (LRIrrelevantPreds@{u i j k u i' j' k'} IrrRec0@{u i j k u i' j' k'} Γ t t
                (lr1 : LRPackAdequate (LogRel@{u i j k} zero) lr1)
                (lr2 : LRPackAdequate (LogRel@{u i' j' k'} zero) lr2)
                (reflLRTyEq lr1)) as [tyEq _ _].
    exact (tyEq u).
Qed.

#[local]
Theorem LRIrrelevantCum@{i j k l i' j' k' l'}
  (Γ : context) (A A' : term) {lA lA'}
  {eqTyA redTmA : term -> Type@{k}}
  {eqTyA' redTmA' : term -> Type@{k'}}
  {eqTmA : term -> term -> Type@{k}}
  {eqTmA' : term -> term -> Type@{k'}}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA)
  (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  @and3@{v v v} (forall B, eqTyA B <≈> eqTyA' B)
    (forall t, redTmA t <≈> redTmA' t)
    (forall t u, eqTmA t u <≈> eqTmA' t u).
Proof.
  exact (LRIrrelevantPreds@{i j k l i' j' k' l'} IrrRec Γ A A' lrA lrA').
Qed.

Theorem LRIrrelevantPack@{i j k l} 
  (Γ : context) (A A' : term) {lA lA'} 
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ])
  (RA' : [ LogRel@{i j k l} lA' | Γ ||- A' ])
  (RAA' : [Γ ||-<lA> A ≅ A' | RA]) :
  equivLRPack@{v v v} RA RA'.
Proof.
  pose proof (LRIrrelevantCum@{i j k l i j k l} Γ A A' (LRAd.adequate RA) (LRAd.adequate RA') RAA') as [].
  constructor; eauto.
Defined.

Theorem LRTransEq@{i j k l} 
  (Γ : context) (A B C : term) {lA lB} 
  (RA : [ LogRel@{i j k l} lA | Γ ||- A ])
  (RB : [ LogRel@{i j k l} lB | Γ ||- B ])
  (RAB : [Γ ||-<lA> A ≅ B | RA])
  (RBC : [Γ ||-<lB> B ≅ C | RB]) :
  [Γ ||-<lA> A ≅ C | RA].
Proof.
  pose proof (LRIrrelevantPack Γ A B RA RB RAB) as [h _ _].
  now apply h.
Defined.


Theorem LRCumulative@{i j k l i' j' k' l'} {lA}
  {Γ : context} {A : term}
  : [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A ].
Proof.
  exact (LRIrrelevantCumTy@{i j k l i' j' k' l'} IrrRec Γ A).
Qed.

Corollary LRCumulative' @{i j k l i' j' k' l'} {lA}
  {Γ : context} {A A' : term}
  : A = A' -> [ LogRel@{i j k l} lA | Γ ||- A ] -> [ LogRel@{i' j' k' l'} lA | Γ ||- A' ].
Proof.
  intros ->; apply LRCumulative.
Qed.
End LRIrrelevant.


#[local]
Corollary TyEqIrrelevantCum Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A eqTyA' redTmA' eqTmA') :
  forall B, eqTyA B -> eqTyA' B.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A ≅ B | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

Corollary LRTyEqIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall B, [Γ ||-< lA > A ≅ B | lrA] -> [Γ ||-< lA' > A' ≅ B | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTyEqIrrelevantCum.
Qed.

#[local]
Corollary RedTmIrrelevantCum Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A eqTyA' redTmA' eqTmA') :
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmRedIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.

Corollary LRTmRedIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmRedIrrelevantCum.
Qed.


#[local]
Corollary TmEqIrrelevantCum Γ A {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A eqTyA' redTmA' eqTmA') :
  forall t u, eqTmA t u -> eqTmA' t u.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  now eapply LRTyEqRefl.
Qed.

Corollary LRTmEqIrrelevantCum@{i j k l i' j' k' l'} lA lA' Γ A
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A]) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevantCum'@{i j k l i' j' k' l'} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i' j' k' l'} lA' | Γ ||- A']) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.

Corollary LRTmEqIrrelevant'@{i j k l} lA lA' Γ A A' (e : A = A')
  (lrA : [LogRel@{i j k l} lA | Γ ||- A]) (lrA' : [LogRel@{i j k l} lA' | Γ ||- A']) :
  forall t u, [Γ ||-< lA > t ≅ u : A | lrA] -> [Γ ||-< lA' > t ≅ u : A' | lrA'].
Proof.
  revert lrA'; rewrite <- e; now apply LRTmEqIrrelevantCum.
Qed.



Corollary TyEqSym@{i j k l i' j' k' l'} Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel@{i j k l} lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel@{i' j' k' l'} lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' -> eqTyA' A.
Proof.
  intros.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
  1: eauto.
  now eapply LRTyEqRefl.
Qed.

Corollary LRTyEqSym lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A']) :
  [Γ ||-< lA > A ≅ A' | lrA] -> [Γ ||-< lA' > A' ≅ A | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply TyEqSym.
Qed.

#[local]
Corollary RedTmConv Γ A A' {lA eqTyA redTmA eqTmA lA' eqTyA' redTmA' eqTmA'}
  (lrA : LogRel lA Γ A eqTyA redTmA eqTmA) (lrA' : LogRel lA' Γ A' eqTyA' redTmA' eqTmA') :
  eqTyA A' ->
  forall t, redTmA t -> redTmA' t.
Proof.
  apply (LRIrrelevantCum _ _ _ lrA lrA').
Qed.

Corollary LRTmRedConv lA lA' Γ A A' (lrA : [Γ ||-< lA > A]) (lrA' : [Γ ||-< lA'> A' ]) :
  [Γ ||-< lA > A ≅ A' | lrA ] ->
  forall t, [Γ ||-< lA > t : A | lrA] -> [Γ ||-< lA' > t : A' | lrA'].
Proof.
  destruct lrA, lrA'.
  cbn in *.
  now eapply RedTmConv.
Qed.

Corollary PolyRedEqSym {Γ l l' shp shp' pos pos'}
  {PA : PolyRed Γ l shp pos}
  (PA' : PolyRed Γ l' shp' pos') :
  PolyRedEq PA shp' pos' -> PolyRedEq PA' shp pos.
Proof.
  intros []; unshelve econstructor.
  - intros; eapply LRTyEqSym; eauto.
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

Section WContIrrelevanceLemmas.
  Context {Γ l A} (WA: [Γ ||-W<l> A]) {Δ} {a a'} (ρ : Δ ≤ Γ) (wfΔ wfΔ' : [|- Δ])
  (Ra : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ : _])
  (Ra' : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a'⟨ρ'⟩ : _]) 
  (Raa' : forall Ξ (ρ' : Ξ ≤ Δ) (wfΞ : [|- Ξ]), [WA.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _])
  (w := outTy WA) (dom := (ParamRedTy.dom WA)⟨ρ⟩) (cod := (ParamRedTy.cod WA)⟨wk_up dom ρ⟩).

Lemma instWCodRed_conv_irrelevance  Ξ (ρ' : Ξ ≤ Δ) (wfΞ wfΞ' : [|-Ξ]):
  equivLRPack (WRedTm.instWCodRed ρ wfΔ Ra Ξ ρ' wfΞ) (WRedTm.instWCodRed ρ wfΔ' Ra' Ξ ρ' wfΞ').
Proof.
  unfold WRedTm.instWCodRed.
  set (e := eq_ind_r _ _ _); set (e' := eq_ind_r _ _ _); clearbody e e'. cbn in e, e'.
  set (P := @eq_rect _ _ _ _).
  set (P' := @eq_rect _ _ _ _).
  refine (match e as e in _ = A return equivLRPack (P A e) (P' _ e') with | eq_refl => _ end).
  refine (match e' as e' in _ = A' return equivLRPack (P _ eq_refl) (P' _ e') with | eq_refl => _ end).
  cbn.  eapply LRIrrelevantPack.
  eapply PolyRed.posExt; eauto.
Qed.

Lemma instWCod_conv : [Δ |- cod[a..] ≅ cod[a'..]].
Proof.
  unfold cod; rewrite <-2!wk_up_ren_subst_id, subst_single_wk_id_left, (subst_single_wk_id_left _ a').
  unshelve eapply escapeEq.
  3: unshelve eapply PolyRed.posExt.
  7: erewrite <-(wk_id_ren_on _ a), <-(wk_id_ren_on _ a'); eapply Raa'.
  + tea.
  + erewrite <-(wk_id_ren_on _ a); eapply Ra.
  + erewrite <-(wk_id_ren_on _ a'); eapply Ra'.
Qed.

Lemma supContTy_inst_conv : [Δ |- tProd cod[a..] w⟨wk_step cod[a..] ρ⟩ ≅ tProd cod[a'..] w⟨wk_step cod[a'..] ρ⟩].
Proof.
  rewrite <- 2!wk_step_wk1, 2!wk1_ren_on.
  eapply convty_simple_arr.
  2: now eapply instWCod_conv.
  2: eapply convty_wk; tea; now eapply (ParamRedTy.eq WA).
  unfold cod; rewrite <-wk_up_ren_subst_id, subst_single_wk_id_left.
  eapply escape; eapply PolyRed.posRed.
  erewrite <-(wk_id_ren_on _ a); eapply Ra.
  Unshelve. tea.
Qed.

Lemma funRedTm_conv_irrelevance {k}
 (Rk : WRedTm.funRedTm Δ ρ wfΔ k Ra (fun Δ => WRedTm WA (Δ:=Δ)) (fun Δ => WRedTmEq WA (Δ:=Δ))) :
  WRedTm.funRedTm Δ ρ wfΔ' k Ra' (fun Δ => WRedTm WA (Δ:=Δ)) (fun Δ => WRedTmEq WA (Δ:=Δ)).
Proof.
  pose proof supContTy_inst_conv.
  destruct Rk; econstructor; tea.
  + eapply redtmwf_conv; tea.
  + eapply convtm_conv; tea.
  + intros. eapply app.
    eapply instWCodRed_conv_irrelevance; tea.
  + intros. eapply eq; eapply instWCodRed_conv_irrelevance; tea.
Defined.

Lemma funRedTmEq_conv_irrelevance {k k'}
 (Rkk' : WRedTm.funRedTmEq Δ ρ wfΔ k k' Ra (fun Δ => WRedTm WA (Δ:=Δ)) (fun Δ => WRedTmEq WA (Δ:=Δ))) :
 WRedTm.funRedTmEq Δ ρ wfΔ k k' Ra' (fun Δ => WRedTm WA (Δ:=Δ)) (fun Δ => WRedTmEq WA (Δ:=Δ)).
Proof.
  pose proof supContTy_inst_conv.
  destruct Rkk'; unshelve econstructor.
  + now eapply funRedTm_conv_irrelevance.
  + now eapply funRedTm_conv_irrelevance.
  + now eapply convtm_conv.
  + intros. eapply eqApp.
    now eapply instWCodRed_conv_irrelevance.
Qed.
  
End WContIrrelevanceLemmas.



Lemma WRedTmEqSym {Γ l A} (WA: [Γ ||-W<l> A]) 
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (t u : term),
      [PolyRed.shpRed WA ρ h | Δ ||- t ≅ u : (ParamRedTy.dom WA)⟨ρ⟩] -> [PolyRed.shpRed WA ρ h | Δ ||- u ≅ t : (ParamRedTy.dom WA)⟨ρ⟩])
  (ihcod : forall (Δ : context) (a : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]) (ha : [PolyRed.shpRed WA ρ h | Δ ||- a : (ParamRedTy.dom WA)⟨ρ⟩]) (t u : term),
      [PolyRed.posRed WA ρ h ha | Δ ||- t ≅ u : (ParamRedTy.cod WA)[a .: ρ >> tRel]] ->
      [PolyRed.posRed WA ρ h ha | Δ ||- u ≅ t : (ParamRedTy.cod WA)[a .: ρ >> tRel]]) :
  WRedInductionConcl WA
      (fun Δ ρ wfΔ t _ => True) 
      (fun Δ ρ wfΔ t _ => True)
      (fun Δ ρ wfΔ t u _ => WRedTmEq WA ρ wfΔ u t)
      (fun Δ ρ wfΔ t u _ => WPropEq WA ρ wfΔ u t).
Proof.
  apply WRedInduction; try solve [intros; exact I].
  - intros; econstructor; tea; now symmetry.
  - intros; unshelve eapply WRedTm.supReq; tea; eauto.
    unshelve eapply funRedTmEq_conv_irrelevance.
    3-5: eauto.
    1: eauto.
    destruct Rkk'; unshelve econstructor; tea; eauto.
    now symmetry.
  - intros. constructor. now eapply NeNfEqSym.
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
  - intros. now eapply WRedTmEqSym.
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
