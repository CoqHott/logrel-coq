(** * LogRel.LogicalRelation.Definition.Poly : Definition of the logical relation for polynomial *)
From Coq Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of a polynomial A,, B  *)

Module PolyRedPack.

  (* A polynomial is a pair (shp, pos) of a type of shapes [Γ |- shp] and
    a dependent type of positions [Γ |- pos] *)
  (* This should be used as a common entry for Π, Σ, W and M types *)

  Record PolyRedPack@{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta}
    {Γ : context} {shp shp' pos pos' : term}
  : Type (* @ max(Set, i+1) *) := {
    shpRed {Δ} (ρ : Δ ≤ Γ) : [ |- Δ ] -> LRPack@{i} Δ shp⟨ρ⟩ shp'⟨ρ⟩ ;
    posRed {Δ} {a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) :
        [ (shpRed ρ h) |  Δ ||- a ≅ b : shp⟨ρ⟩ ≅ shp'⟨ρ⟩] ->
        LRPack@{i} Δ (pos[a .: (ρ >> tRel)]) (pos'[b .: (ρ >> tRel)]);
  }.

  Arguments PolyRedPack {_ _ _ _}.

  (** We separate the recursive "data", ie the fact that we have reducibility data (an LRPack)
  for the domain and codomain, and the fact that these are in the graph of the logical relation.
  This is crucial for Coq to accept the definition, because it makes the nesting simple enough
  to be accepted. We later on show an induction principle that does not have this separation to
  make reasoning easier. *)
  Record PolyRedPackAdequate@{i j} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta} {shp shp' pos pos' : term}
    {Γ : context} {R : RedRel@{i j}}  {PA : PolyRedPack@{i} Γ shp shp' pos pos'}
  : Type@{j} := {
    shpAd {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) : LRPackAdequate@{i j} R (PA.(shpRed) ρ h);
    posAd {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ PA.(shpRed) ρ h | Δ ||- a ≅ b : shp⟨ρ⟩ ])
      : LRPackAdequate@{i j} R (PA.(posRed) ρ h ha);
  }.

  Arguments PolyRedPackAdequate {_ _ _ _ _ _ _ _ _}.

End PolyRedPack.

Export PolyRedPack(PolyRedPack, Build_PolyRedPack, PolyRedPackAdequate, Build_PolyRedPackAdequate).

Import EqNotations.

Lemma wk1_subst_scons B A a {Γ Δ} (ρ : Δ ≤ Γ) :  B⟨ρ⟩ = B⟨@wk1 Γ A⟩[a .: ρ >> tRel].
Proof. now rewrite wk1_ren_on, shift_subst_scons. Qed.

Definition mkPolyRedPackWk1@{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta}
    {Γ : context} {shp shp' pos pos' : term}
  (shpRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ shp⟨ρ⟩ shp'⟨ρ⟩)
  (posRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ pos⟨ρ⟩ pos'⟨ρ⟩) :
  PolyRedPack@{i} Γ shp shp' pos⟨@wk1 Γ shp⟩ pos'⟨@wk1 Γ shp'⟩.
Proof.
  exists shpRed; intros.
  rewrite <-2! wk1_subst_scons; eauto.
Defined.

From Equations Require Import Equations.

Definition mkPolyRedPackAdequateWk1@{i j} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta}
    {Γ : context} {shp shp' pos pos' : term} {R : RedRel@{i j}}
  (shpRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ shp⟨ρ⟩ shp'⟨ρ⟩)
  (shpAd : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), LRPackAdequate@{i j} R (shpRed ρ h))
  (posRed : forall {Δ} (ρ : Δ ≤ Γ), [ |- Δ ] -> LRPack@{i} Δ pos⟨ρ⟩ pos'⟨ρ⟩)
  (posAd : forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]), LRPackAdequate@{i j} R (posRed ρ h)) :
  PolyRedPackAdequate@{i j} R (mkPolyRedPackWk1 (@shpRed) (@posRed)).
Proof.
  unfold mkPolyRedPackWk1; constructor.
  + intros; apply shpAd.
  + cbn; intros.
    set (e' := wk1_subst_scons _ _ _ _); clearbody e'.
    set (e := wk1_subst_scons _ _ _ _); clearbody e.
    set (y := pos⟨wk1 shp⟩[a .: ρ >> tRel]) in e |- *.
    clearbody y; depelim e.
    set (y' := pos'⟨wk1 shp'⟩[b .: ρ >> tRel]) in e' |- *.
    clearbody y'; depelim e'.
    eapply posAd.
Qed.

Lemma ren_scons_ren_comp {Γ Δ Ξ B a} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) :
  B[a .: ρ >> tRel]⟨ρ'⟩ = B[a⟨ρ'⟩ .: (ρ' ∘w ρ) >> tRel].
Proof. now rasimpl. Qed.

Definition instPos @{i} `{ta : tag}
    `{WfContext ta} `{WfType ta} `{ConvType ta}
    {Γ : context} {shp shp' pos pos' : term}
  (P : PolyRedPack@{i} Γ shp shp' pos pos')
  {Δ a a'} (ρ : Δ ≤ Γ)
  (Ra : forall {Ξ} (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
      [P.(PolyRedPack.shpRed) (ρ' ∘w ρ) wfΞ | _ ||- a⟨ρ'⟩ ≅ a'⟨ρ'⟩ : _ ≅ _]) :
  forall [Ξ] (ρ' : Ξ ≤ Δ) (wfΞ : [ |- Ξ ]),
    LRPack@{i} Ξ (pos[a .: (ρ >> tRel)])⟨ρ'⟩ (pos'[a' .: (ρ >> tRel)])⟨ρ'⟩.
Proof.
  intros; rewrite 2!ren_scons_ren_comp.
  unshelve eapply P.(PolyRedPack.posRed); eauto.
Defined.

Module ParamRedTyPack.

  Record ParamTy {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A dom cod : term} := {
      red : [Γ |- A :⤳*: T dom cod];
      domTy : [Γ |- dom] ;
      codTy : [Γ,, dom |- cod] ;
  }.

  Arguments ParamTy {_ _ _ _ _ _}.

  Definition whred {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A dom cod : term} :
    (forall a b, isType (T a b)) ->
    ParamTy (T:=T) Γ A dom cod -> [Γ |- A ↘ ].
  Proof. intros h []; econstructor; tea; apply h. Defined.

  Record ParamRedTyPack {T : term -> term -> term}
    `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Type := {
    domL : term ;
    domR : term ;
    codL : term ;
    codR : term ;
    redL : ParamTy (T:=T) Γ A domL codL ;
    redR : ParamTy (T:=T) Γ B domR codR ;
    eqdom : [Γ |- domL ≅ domR];
    eq : [Γ |- T domL codL ≅ T domR codR];

    polyRed : PolyRedPack Γ domL domR codL codR ;
  }.


  Arguments ParamRedTyPack {_ _ _ _ _ _}.

  Definition outTy {T : term -> term -> term}
    `{ta : tag} `{WfContext ta}
    `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} (PA : ParamRedTyPack (T:=T) Γ A B) :=
    T PA.(domL) PA.(codL).

  Arguments outTy {_ _ _ _ _ _ _ _ _} _ /.

  Definition whredL0 {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} :
    (forall a b, isType (T a b)) ->
    ParamRedTyPack (T:=T) Γ A B -> [Γ |- A ↘ ].
  Proof. intros h []; now eapply whred. Defined.

  Definition whredR0 {T : term -> term -> term}
    `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta} `{RedType ta}
    {Γ : context} {A B : term} :
    (forall a b, isType (T a b)) ->
    ParamRedTyPack (T:=T) Γ A B -> [Γ |- B ↘ ].
  Proof. intros h []; now eapply whred. Defined.

End ParamRedTyPack.

Export ParamRedTyPack(ParamRedTyPack, Build_ParamRedTyPack, outTy).
Coercion ParamRedTyPack.polyRed : ParamRedTyPack >-> PolyRedPack.
