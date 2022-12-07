From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping.
Set Primitive Projections.

Section Definitions.

  (* We locally disable typing notations to be able to use the in the definition here before declaring the right
  instance *)
  Close Scope typing_scope.

  Inductive WfContextDecl : context -> Type :=
      | connil : [ |- ε ]
      | concons {Γ na A} : 
          [ |- Γ ] -> 
          [ Γ |- A ] -> 
          [ |-  Γ ,, vass na A]
  
  with WfTypeDecl  : context -> term -> Type :=
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

  with TypingDecl : context -> term -> term -> Type :=
      | wfVar {Γ} {n decl} :
          [   |- Γ ] ->
          in_ctx Γ n decl ->
          [ Γ |- tRel n : decl.(decl_type) ]
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
          [ Γ |- tApp f a : B[a..] ]
      | wfTermConv {Γ} {t A B} :
          [ Γ |- t : A ] -> 
          [ Γ |- A ≅ B ] -> 
          [ Γ |- t : B ]
      
  with ConvTypeDecl : context -> term -> term  -> Type :=  
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

  with ConvTermDecl : context -> term -> term -> term -> Type :=
      | TermBRed {Γ} {na} {a t A B} :
              [ Γ |- A ] ->
              [ Γ ,, vass na A |- t : B ] ->
              [ Γ |- a : A ] ->
              [ Γ |- tApp (tLambda na A t) a ≅ t[a..] : B[a..] ]
      | TermPiCong {Γ} {na nb } {A B C D} :
          [ Γ |- A ] ->
          [ Γ |- A ≅ B : U ] ->
          [ Γ ,, vass na A |- C ≅ D : U ] ->
          [ Γ |- tProd na A C ≅ tProd nb B D : U ]
      | TermAppCong {Γ} {na} {a b f g A B} :
          [ Γ |- f ≅ g : tProd na A B ] ->
          [ Γ |- a ≅ b : A ] ->
          [ Γ |- tApp f a ≅ tApp g b : B[a..] ]
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
      
  where "[   |- Γ ]" := (WfContextDecl Γ)
  and   "[ Γ |- T ]" := (WfTypeDecl Γ T)
  and   "[ Γ |- t : T ]" := (TypingDecl Γ T t)
  and   "[ Γ |- A ≅ B ]" := (ConvTypeDecl Γ A B)
  and   "[ Γ |- t ≅ t' : T ]" := (ConvTermDecl Γ T t t').

  Inductive OneRedTermDecl (Γ : context) : term -> term -> term -> Type :=
  | BRed {na} {A B a t} :
      [ Γ |- A ] -> 
      [ Γ ,, vass na A |- t : B ] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp (tLambda na A t) a ⇒ t[a..] : B[a..] ]
  | appSubst {na A B t u a} :
      [ Γ |- t ⇒ u : tProd na A B] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp t a ⇒ tApp u a : B[a..] ]
  | termRedConv {A B t u} : 
      [ Γ |- t ⇒ u : A ] ->
      [ Γ |- A ≅ B ] ->
      [ Γ |- t ⇒ u : B ]

  where "[ Γ |- t ⇒ u : A ]" := (OneRedTermDecl Γ A t u).

  Inductive OneRedTypeDecl (Γ : context) : term -> term -> Type :=
  | typeRedUniv {A B} :
      [ Γ |- A ⇒ B : U ] ->
      [ Γ |- A ⇒ B ]

  where "[ Γ |- A ⇒ B ]" := (OneRedTypeDecl Γ A B).

End Definitions.

Module DeclarativeTypingData.

  #[export] Instance WfContext_Decl : WfContext de := WfContextDecl.
  #[export] Instance WfType_Decl : WfType de := WfTypeDecl.
  #[export] Instance Typing_Decl : Typing de := TypingDecl.
  #[export] Instance ConvType_Decl : ConvType de := ConvTypeDecl.
  #[export] Instance ConvTerm_Decl : ConvTerm de := ConvTermDecl.
  #[export] Instance ConvNeu_Decl : ConvNeu de := ConvTermDecl.
  #[export] Instance OneRedType_Decl : OneRedType de := OneRedTypeDecl.
  #[export] Instance OneRedTerm_Decl : OneRedTerm de := OneRedTermDecl.

  Ltac fold_decl :=
    change WfContextDecl with wf_context in * ;
    change WfTypeDecl with wf_type in *;
    change TypingDecl with typing in * ;
    change ConvTypeDecl with conv_type in * ;
    change ConvTermDecl with conv_term in * ;
    change OneRedTypeDecl with one_red_ty in *;
    change OneRedTermDecl with one_red_tm in *.

End DeclarativeTypingData.

Section InductionPrinciples.
  Import DeclarativeTypingData.

Scheme 
    Minimality for WfContextDecl Sort Type with
    Minimality for WfTypeDecl   Sort Type with
    Minimality for TypingDecl    Sort Type with
    Minimality for ConvTypeDecl  Sort Type with
    Minimality for ConvTermDecl  Sort Type.

Combined Scheme _WfDeclInduction from
    WfContextDecl_rect_nodep,
    WfTypeDecl_rect_nodep,
    TypingDecl_rect_nodep,
    ConvTypeDecl_rect_nodep,
    ConvTermDecl_rect_nodep.

Definition WfDeclInductionConcl
  (PCon : context -> Type) (PTy : context -> term -> Type)
  (PTm PTyEq : context -> term -> term -> Type)
  (PTmEq : context -> term -> term -> term -> Type) :=
  (forall Γ : context, [  |- Γ ] -> PCon Γ)
  × (forall (Γ : context) (A : term), [Γ |- A] -> PTy Γ A)
  × (forall (Γ : context) (A t : term), [Γ |- t : A] -> PTm Γ A t)
	× (forall (Γ : context) (A B : term), [Γ |- A ≅ B] -> PTyEq Γ A B)
  × (forall (Γ : context) (A t u : term), [Γ |- t ≅ u : A] -> PTmEq Γ A t u).

Let WfDeclInductionType := ltac:
  (
  set (H := _WfDeclInduction) ;
  fold_decl ;
  let ty := type of H in exact ty).

Definition WfDeclInduction : WfDeclInductionType := _WfDeclInduction.

End InductionPrinciples.

Section TypingWk.
  Import DeclarativeTypingData.

  Lemma map_decl_lift (ρ : weakening) d :
    map_decl (ren_term (up_ren ρ)) (map_decl (ren_term shift) d) =
    map_decl (ren_term shift) (map_decl (ren_term ρ) d).
  Proof.
    rewrite ! compose_map_decl.
    eapply map_decl_ext.
    intros t.
    asimpl.
    reflexivity.
  Qed.

  Lemma nth_error_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
    in_ctx Γ n decl ->
    in_ctx Δ (ρ n) (map_decl (ren_term ρ) decl).
  Proof.
    intros Hdecl.
    destruct ρ as [ρ wfρ] ; cbn.
    induction wfρ in n, decl, Hdecl |- *.
    - cbn.
      rewrite map_decl_id.
      1: eassumption.
      now asimpl.
    - cbn.
      change ((ρ >> S) n) with (S (ρ n)).
      replace (map_decl _ _) with (map_decl (ren_term shift) (map_decl (ren_term ρ) decl))
        by (now rewrite compose_map_decl ; asimpl).
      now econstructor.
    - destruct n ; cbn.
      + cbn.
        inversion Hdecl ; subst ; clear Hdecl.
        unfold ren1, Ren_decl.
        rewrite map_decl_lift.
        now constructor.
      + inversion Hdecl ; subst ; cbn in *.
        rewrite map_decl_lift.
        now econstructor.
    Qed.
  
  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PTm (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].

  Theorem typing_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    apply WfDeclInduction.
    - red.
      trivial.
    - red. trivial.
    - intros ? ? IH.
      now econstructor.
    - intros Γ na A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      replace (ren_term _ B) with (B⟨wk_up ρ⟩)
        by (now unfold ren1, RenWk_term ; asimpl).
      unshelve eapply (IHB _ {| wk := wk_up ρ ; well_wk := _ |} _).
      1: now constructor.
      now constructor ; fold_decl.
    - intros * _ IHA ? * ?.
      econstructor.
      now eapply IHA.
    - intros * _ IHΓ Hnth ? * ?.
      eapply typing_meta_conv.
      1: econstructor ; tea.
      1: eapply nth_error_wk ; tea.
      reflexivity.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      replace (ren_term _ B) with (B⟨wk_up ρ⟩)
        by (now unfold ren1, RenWk_term ; asimpl).
      unshelve eapply (IHB _ {| wk := wk_up ρ ; well_wk := _ |} _).
      1: now econstructor.
      econstructor ; tea.
      econstructor.
      now eapply IHA.
    - intros * _ IHA _ IHt ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      red in IHt.
      replace (ren_term _ t) with (t⟨wk_up ρ⟩)
        by (now unfold ren1, RenWk_term ; asimpl).
      replace (ren_term _ B) with (B⟨wk_up ρ⟩)
        by (now unfold ren1, RenWk_term ; asimpl).
      unshelve eapply (IHt _ {| wk := wk_up ρ ; well_wk := _ |} _).
      1: now econstructor.
      econstructor ; tea.
      now eapply IHA.
    - intros * _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply typing_meta_conv.
      1: econstructor.
      1: now eapply IHf.
      1: now eapply IHu.
      now asimpl.
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + replace (ren_term _ B) with (B⟨wk_up ρ⟩)
          by (now unfold ren1, RenWk_term ; asimpl).
        replace (ren_term _ B') with (B'⟨wk_up ρ⟩)
          by (now unfold ren1, RenWk_term ; asimpl).
        unshelve eapply (IHBB' _ {| wk := wk_up ρ ; well_wk := _ |} _).
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
    - intros Γ ? u t A B _ IHA _ IHt _ IHu ? ρ ?.
      cbn.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHA.
      + unfold upRen_term_term.
        replace (ren_term _ t) with (t⟨wk_up ρ⟩)
          by (now asimpl).
        unshelve eapply (IHt _ {| wk := wk_up ρ ; well_wk := _ |} _).
        1: now econstructor.
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + unfold ren1 at 2, RenWlWk_term.   
        cbn.
        now asimpl.
      + now asimpl. 
    - intros Γ ? ? A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + replace (ren_term _ B) with (B⟨wk_up ρ⟩)
          by (now unfold ren1, RenWk_term ; asimpl).
        replace (ren_term _ B') with (B'⟨wk_up ρ⟩)
          by (now unfold ren1, RenWk_term ; asimpl).
        unshelve eapply (IHBB' _ {| wk := wk_up ρ ; well_wk := _ |} _).
        1: now econstructor.
        all: now econstructor ; fold_decl.
    - intros Γ ? u u' f f' A B _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + now asimpl.
      + now asimpl.
    - intros Γ ? ? f f' A B _ IHA _ IHf _ IHg _ IHe ? ρ ?.
      cbn.
      econstructor ; fold_decl.
      1-3: easy.
      unshelve epose proof (IHe _ {| wk := wk_up ρ ; well_wk := _ |} _) as IHe'.
      2: now econstructor.
      1: now econstructor ; fold_decl.
      unfold ren1, RenWlWk_term in IHe'.
      cbn in *.
      asimpl.
      replace (ren_term _ f) with (f⟨↑⟩⟨up_ren ρ⟩)
        by now asimpl.
      replace (ren_term _ f') with (f'⟨↑⟩⟨up_ren ρ⟩)
          by now asimpl.
      now apply IHe'.
    - intros * _ IHt ? ρ ?.
      now econstructor ; fold_decl.
    - intros * _ IHt ? ρ ?.
      now econstructor ; fold_decl.
    - intros * _ IHt _ IHt' ? ρ ?.
      now eapply TermTrans ; fold_decl.
    - intros * _ IHt _ IHA ? ρ ?.
      now eapply TermConv ; fold_decl.
  Qed.

End TypingWk.