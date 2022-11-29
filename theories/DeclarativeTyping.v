From MetaCoq.Template Require Import Universes.
From MetaCoq.PCUIC Require Import PCUICAst.
From LogRel Require Import Untyped Automation Notations.

Set Primitive Projections.

Inductive wfType  : context -> term -> Type :=
    | wfTypeU {Γ} : 
        [ |- Γ ] -> 
        [ Γ |- U ] 
    | wfTypeProd {Γ} {na : aname} {A B} : 
        [ Γ |- A ] -> 
        [Γ ,, (vass na A) |- B ] -> 
        [ Γ |- tProd na A B ]
    | wfTypeUniv {Γ} {A} :
        [ Γ |- A : U ] -> 
        [ Γ |- A ]

with wfContext : context -> Type :=
    | connil : [ |- [] ]
    | concons {Γ na A} : 
        [ |- Γ ] -> 
        [ Γ |- A ] -> 
        [ |-  Γ ,, vass na A]

with wfTerm : context -> term -> term -> Type :=
    | wfVar {Γ} {n decl} :
        [   |- Γ ] ->
        nth_error Γ n = Some decl ->
        [ Γ |- tRel n : lift0 (S n) decl.(decl_type) ]
    | wfTermProd {Γ} {na} {A B} :
        [ Γ |- A : U] -> 
        [Γ ,, (vass na A) |- B : U ] ->
        [ Γ |- tProd na A B : U ]
    | wfTermLam {Γ} {na} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, vass na A |- t : B ] -> 
        [ Γ |- tLambda na A t : tProd na A B]
    | wfTermApp {Γ} {na} {f a A B} :
        [ Γ |- f : tProd na A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- tApp f a : B{0 := a} ]
    | wfTermConv {Γ} {t A B} :
        [ Γ |- t : A ] -> 
        [ Γ |- A ≅ B ] -> 
        [ Γ |- t : B ]
    
with convType : context -> term -> term  -> Type :=  
    | TypePiCong {Γ} {na nb} {A B C D} :
        [ Γ |- A] ->
        [ Γ |- A ≅ B] ->
        [ Γ ,, vass na A |- C ≅ D] ->
        [ Γ |- tProd na A C ≅ tProd nb B D]
    | TypeRefl {Γ} {A} : 
        [ Γ |- A ] -> 
        [ Γ |- A ≅ A]       
    | TypeSym {Γ} {A B} :
        [ Γ |- A ≅ B ] -> 
        [ Γ |- B ≅ A ]
    | TypeTrans {Γ} {A B C} :
        [ Γ |- A ≅ B] ->
        [ Γ |- B ≅ C] ->
        [ Γ |- A ≅ C]
    | convUniv {Γ} {A B} :
        [ Γ |- A ≅ B : U ] -> 
        [ Γ |- A ≅ B ]    

with convTerm : context -> term -> term -> term -> Type :=
    | TermPiCong {Γ} {na nb } {A B C D} :
        [ Γ |- A ] ->
        [ Γ |- A ≅ B : U ] ->
        [ Γ ,, vass na A |- C ≅ D : U ] ->
        [ Γ |- tProd na A C ≅ tProd nb B D : U ]
    | TermAppCong {Γ} {na} {a b f g A B} :
        [ Γ |- f ≅ g : tProd na A B ] ->
        [ Γ |- a ≅ b : A ] ->
        [ Γ |- tApp f a ≅ tApp g b : B{0 := a} ]
    | TermBRed {Γ} {na} {a t A B} :
        [ Γ |- A ] ->
        [ Γ ,, vass na A |- t : B ] ->
        [ Γ |- a : A ] ->
        [ Γ |- tApp (tLambda na A t) a ≅ t{0 := a} : B{0 := a} ]
    | TermFunExt {Γ} {na nb} {f g A B} :
        [ Γ |- A ] ->
        [ Γ |- f : tProd na A B ] ->
        [ Γ |- g : tProd nb A B ] ->
        [ Γ ,, vass na A |- eta_expand f ≅ eta_expand g : B ] ->
        [ Γ |- f ≅ g : tProd na A B ]
    | TermRefl {Γ} {t A} :
        [ Γ |- t : A ] -> 
        [ Γ |- t ≅ t : A ]
    | TermSym {Γ} {t t' A} :
        [ Γ |- t ≅ t' : A ] ->
        [ Γ |- t' ≅ t : A ]
    | TermTrans {Γ} {t t' t'' A} :
        [ Γ |- t ≅ t' : A ] ->
        [ Γ |- t' ≅ t'' : A ] ->
        [ Γ |- t ≅ t'' : A ]
    | TermConv {Γ} {t t' A B} :
        [ Γ |- t ≅ t': A ] ->
        [ Γ |- A ≅ B ] ->
        [ Γ |- t ≅ t': B ]
    
where "[   |- Γ ]" := (wfContext Γ)
and   "[ Γ |- T ]" := (wfType Γ T)
and   "[ Γ |- t : T ]" := (wfTerm Γ t T)
and   "[ Γ |- A ≅ B ]" := (convType Γ A B)
and   "[ Γ |- t ≅ t' : T ]" := (convTerm Γ t t' T).

Section InductionPrinciples.


Scheme 
    Minimality for wfContext Sort Type with
    Minimality for wfType    Sort Type with
    Minimality for wfTerm    Sort Type with
    Minimality for convType  Sort Type with
    Minimality for convTerm  Sort Type.

Combined Scheme wfInduction from
    wfContext_rect_nodep,
    wfType_rect_nodep,
    wfTerm_rect_nodep,
    convType_rect_nodep,
    convTerm_rect_nodep.

Definition wfInductionType
  (PCon : context -> Type) (PTy : context -> term -> Type)
  (PTm PTyEq : context -> term -> term -> Type)
  (PTmEq : context -> term -> term -> term -> Type) :=
  (forall Γ : context, [  |- Γ ] -> PCon Γ)
  × (forall (Γ : context) (A : term), [Γ |- A] -> PTy Γ A)
  × (forall (Γ : context) (t A : term), [Γ |- t : A] -> PTm Γ t A)
	× (forall (Γ : context) (A B : term), [Γ |- A ≅ B] -> PTyEq Γ A B)
  × (forall (Γ : context) (t u A : term), [Γ |- t ≅ u : A] -> PTmEq Γ t u A).


End InductionPrinciples.

Lemma termMetaConv (Γ : context) (t A B : term) :
  [Γ |- t : A] ->
  A = B ->
  [Γ |- t : B].
Proof.
  now intros ? ->.
Qed.

Lemma eqTermMetaConv (Γ : context) (t u A B : term) :
  [Γ |- t ≅ u : A] ->
  A = B ->
  [Γ |- t ≅ u : B].
Proof.
  now intros ? ->.
Qed.

Inductive termRed (Γ : context) : term -> term -> term -> Type :=
    | appSubst {na A B t u a} :
        [ Γ |- t ⇒ u : tProd na A B] ->
        [ Γ |- a : A ] ->
        [ Γ |- tApp t a ⇒ tApp u a : B{0 := a} ]
    | BRed {na} {A B a t} :
        [ Γ |- A ] -> 
        [ Γ ,, vass na A |- t : B ] ->
        [ Γ |- a : A ] ->
        [ Γ |- tApp (tLambda na A t) a ⇒ t{0 := a} : B{0 := a} ]
    | termRedConv {A B t u} : 
        [ Γ |- t ⇒ u : A ] ->
        [ Γ |- A ≅ B ] ->
        [ Γ |- t ⇒ u : B ]

where "[ Γ |- t ⇒ u : A ]" := (termRed Γ t u A).

Inductive typeRed (Γ : context) : term -> term -> Type :=
    | typeRedUniv {A B} :
        [ Γ |- A ⇒ B : U ] ->
        [ Γ |- A ⇒ B ]

where "[ Γ |- A ⇒ B ]" := (typeRed Γ A B).

#[global] Hint Constructors wfType wfContext wfTerm convType convTerm : mltt.
#[global] Hint Constructors termRed typeRed termRedClosure typeRedClosure
  termRedWHNF typeRedWHNF termEqWF typeEqWF termRedWF typeRedWF : mltt.

(*Making the non syntax-directed hints more costly*)
#[global] Remove Hints wfTermConv TermConv termRedConv TypeTrans TermTrans
  termRedSucc typeRedSucc : mltt.
#[global] Hint Resolve wfTermConv TermConv termRedConv TypeTrans TermTrans
  termRedSucc typeRedSucc | 6 : mltt.

#[global] Hint Resolve termRedWHNFRed termRedWHNFWHNF typeRedWHNFRed typeRedWHNFWHNF 
  termEqWFLeft termEqWFRight termEqWFEq typeEqWFLeft typeEqWFRight typeEqWFEq
  termRedWFLeft termRedWFRight termRedWFRed typeRedWFLeft typeRedWFRight
  typeRedWFRed : mltt.


Section TypingWk.

Variable foo : context_decl.

Lemma nth_error_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
  nth_error Γ n = Some decl ->
  {decl' & nth_error Δ (ρ n) = Some decl' ×
    map_decl (rename (ρ ∘ rshiftk (S n))) decl = map_decl (rename (rshiftk (S (ρ n)))) decl'}.
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ] ; cbn.
  induction wfρ in n, Hdecl |- *.
  - exists decl.
    split.
    1: easy.
    reflexivity.
  - cbn.
    edestruct IHwfρ as [decl' [? IH]].
    1: eassumption.
    eexists ; split.
    1: eassumption.
    now rewrite <- rename_compose, <- compose_map_decl, IH, compose_map_decl, rename_compose.
  - destruct n as [ | n].
    + cbn in *.
      inversion Hdecl ; subst ; clear Hdecl.
      eexists ; split.
      1: reflexivity.
      unfold map_decl ; cbn.
      f_equal.
      rewrite <- rename_inst, rename_compose.
      apply rename_ext.
      intros ?.
      now rewrite Nat.sub_0_r.
    + cbn in *.
      edestruct IHwfρ as [decl' [? IH]].
      1: eassumption.
      eexists ; split.
      1: now rewrite Nat.sub_0_r.
      now rewrite <- rename_compose, <- compose_map_decl, IH, compose_map_decl, rename_compose, Nat.sub_0_r.
  Qed.

Let PCon (Γ : context) := True.
Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A.[ren ρ]].
Let PTm (Γ : context) (t A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- t.[ren ρ] : A.[ren ρ]].
Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- A.[ren ρ] ≅ B.[ren ρ]].
Let PTmEq (Γ : context) (t u A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
  [Δ |- t.[ren ρ] ≅ u.[ren ρ] : A.[ren ρ]].


Theorem typing_wk : wfInductionType PCon PTy PTm PTyEq PTmEq.
Proof.
  apply wfInduction.
  - red.
    trivial.
  - red. trivial.
  - intros ? ? IH.
    now econstructor.
  - intros Γ na A B HA IHA HB IHB Δ ρ HΔ.
    econstructor ; fold inst.
    1: easy.
    replace (B.[up 1 (ren ρ)]) with (B.[ren (wk_lift ρ)])
      by now rewrite ren_shiftn.
    unshelve eapply (IHB _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    all: now econstructor.
  - intros * _ IHA ? * ?.
    econstructor.
    now eapply IHA.
  - intros * _ IHΓ Hnth ? * ?.
    unshelve eapply nth_error_wk in Hnth as [decl' [? edecl]] ; tea.
    unfold ren at 1.
    cbn.
    eapply termMetaConv.
    1: econstructor ; eassumption.
    rewrite <- rename_inst, ! lift_rename, rename_compose, (map_decl_type _ decl'), (map_decl_type _ decl).
    f_equal.
    rewrite ! lift_renaming_0_rshift, <- edecl.
    eapply map_decl_ext ; intros ; eapply rename_ext ; intros ?.
    now rewrite lift_renaming_0_rshift.
  - intros * _ IHA _ IHB ? ρ ?.
    cbn.
    econstructor.
    1: now eapply IHA.
    replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
    unshelve eapply (IHB _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    1: now econstructor.
    econstructor ; tea.
    econstructor.
    now eapply IHA.
  - intros * _ IHA _ IHt ? ρ ?.
    cbn.
    econstructor.
    1: now eapply IHA.
    red in IHt.
    replace t.[_] with t.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
    replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
    unshelve eapply (IHt _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    1: now econstructor.
    econstructor ; tea.
    now eapply IHA.
  - intros * _ IHf _ IHu ? ρ ?.
    cbn.
    rewrite subst10_inst.
    replace B.[_] with B.[(up 1 (ren ρ))] by (now rewrite up_Up).
    econstructor.
    2: now eapply IHu.
    now eapply IHf.
  - intros * _ IHt _ IHAB ? ρ ?.
    econstructor.
    1: now eapply IHt.
    now eapply IHAB.
  - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
    cbn.
    econstructor.
    + now eapply IHA.
    + now eapply IHAA'.
    + replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      replace B'.[_] with B'.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      unshelve eapply (IHBB' _ {| wk := wk_lift ρ ; well_wk := _ |} _).
      1: now econstructor.
      econstructor ; tea.
      now eapply IHA.
  - intros * _ IHA ? ρ ?.
    eapply TypeRefl.
    now eapply IHA.
  - intros * _ IH ? ρ ?.
    econstructor.
    now eapply IH.
  - intros * _ IHA _ IHB ? ρ ?.
    eapply TypeTrans.
    + now eapply IHA.
    + now eapply IHB.
  - intros * _ IH ? ρ ?.
    eapply convUniv.
    now eapply IH.
  - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
    cbn.
    econstructor.
    + now eapply IHA.
    + now eapply IHAA'.
    + replace B.[_] with B.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      replace B'.[_] with B'.[ren (wk_lift ρ)] by now rewrite ren_shiftn.
      unshelve eapply (IHBB' _ {| wk := wk_lift ρ ; well_wk := _ |} _).
      all: now econstructor.
  - intros Γ ? u u' f f' A B _ IHf _ IHu ? ρ ?.
    cbn.
    rewrite subst10_inst.
    replace B.[_] with B.[(up 1 (ren ρ))] by (now rewrite up_Up).
    now econstructor.
  - intros Γ ? u t A B _ IHA _ IHt _ IHu ? ρ ?.
    cbn. 
    rewrite ! subst10_inst.
    replace t.[⇑ _] with t.[(up 1 (ren ρ))] by (now rewrite up_Up).
    replace t.[_] with t.[ren (wk_lift ρ)] by (now rewrite ren_shiftn).
    replace B.[_] with B.[ren (wk_lift ρ)] by (now rewrite <- up_Up, ren_shiftn).
    econstructor.
    1,3: easy.
    unshelve eapply (IHt _ {| wk := wk_lift ρ ; well_wk := _ |} _).
    all: now econstructor.
  - intros Γ ? ? f f' A B _ IHA _ IHf _ IHg _ IHe ? ρ ?.
    cbn.
    econstructor.
    1-3: easy.
    unshelve epose proof (IHe _ {| wk := wk_lift ρ ; well_wk := _ |} _) as IHe'.
    2: now econstructor.
    1: now econstructor.
    cbn in *.
    unfold ren in IHe' at 3 5.
    unfold eta_expand.
    cbn in *.
    rewrite ! lift0_inst, ! inst_assoc in IHe' |- *.
    replace B.[_] with B.[ren (shiftn 1 ρ)] by (now rewrite ren_shiftn).
    unshelve erewrite (inst_ext _ _ _ f), (inst_ext _ _ _ f').
    5: eassumption.
    all: rewrite <- Upn_ren.
    all: change 1 with (0 + 1).
    all: rewrite <- subst_shift_comm.
    all: cbn.
    all: now rewrite Upn_0.
  - intros * _ IHt ? ρ ?.
    now econstructor.
  - intros * _ IHt ? ρ ?.
    now econstructor.
  - intros * _ IHt _ IHt' ? ρ ?.
    now eapply TermTrans.
  - intros * _ IHt _ IHA ? ρ ?.
    now eapply TermConv.
Qed.

End TypingWk.