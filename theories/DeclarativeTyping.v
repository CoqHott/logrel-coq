(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context LContexts NormalForms Weakening UntypedReduction.

Set Primitive Projections.

(** Definitions in this file should be understood as the _specification_ of conversion
or typing, done in a declarative fashion. For instance, we _demand_ that conversion
be transitive by adding a corresponding rule. *)

(** ** Definitions *)
Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition
  here before declaring the instance to which abstract notations are bound. *)
  Close Scope typing_scope.


  (** Typing and conversion are mutually defined inductive relations. To avoid having
  to bother with elimination of propositions, we put them in the Type sort. *)

  (** **** Context well-formation *)
  Inductive WfContextDecl l : context -> Type :=
  | connil : [ |- ε]< l >
  | concons {Γ A} : 
          [ |- Γ ]< l > -> 
          [ Γ |- A ]< l > -> 
          [ |- Γ ,, A ]< l >
(*  | ϝwfCon {Γ n} {ne : not_in_LCon (pi1 l) n} : 
        [ |- Γ ]< l ,,l (ne, true) > ->
        [ |- Γ ]< l ,,l (ne, false) > ->
        [ |- Γ ]< l >*)
  (** **** Type well-formation *)
  with WfTypeDecl l : context -> term -> Type :=
      | wfTypeU {Γ} : 
          [ |- Γ ]< l > -> 
          [ Γ |- U ]< l > 
      | wfTypeProd {Γ} {A B} : 
          [ Γ |- A ]< l > -> 
          [ Γ ,, (A) |- B ]< l > -> 
          [ Γ |- tProd A B ]< l >
      | wfTypeNat {Γ} : 
          [ |- Γ ]< l > ->
          [ Γ |- tNat ]< l >
      | wfTypeEmpty {Γ} : 
          [ |- Γ ]< l > ->
          [ Γ |- tEmpty ]< l >    
      | wfTypeBool {Γ} : 
          [ |- Γ ]< l > ->
          [ Γ |- tBool ]< l >
      | wfTypeUniv {Γ} {A} :
          [ Γ |- A : U ]< l > ->
          [ Γ |- A ]< l >
      | ϝwfType {Γ A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- A ]< l ,,l (ne, true) > ->
        [ Γ |- A ]< l ,,l (ne, false) > ->
        [ Γ |- A ]< l >
          
  (** **** Typing *)
  with TypingDecl  l : context -> term -> term -> Type :=
      | wfVar {Γ} {n decl} :
          [ |- Γ ]< l > ->
          in_ctx Γ n decl ->
          [ Γ |- tRel n : decl ]< l >
      | wfTermProd {Γ} {A B} :
          [ Γ |- A : U]< l > -> 
          [ Γ ,, (A) |- B : U ]< l > ->
          [ Γ |- tProd A B : U ]< l >
      | wfTermLam {Γ} {A B t} :
          [ Γ |- A ]< l > ->        
          [ Γ ,, A |- t : B ]< l > -> 
          [ Γ |- tLambda A t : tProd A B]< l >
      | wfTermApp {Γ} {f a A B} :
          [ Γ |- f : tProd A B ]< l > -> 
          [ Γ |- a : A ]< l > -> 
          [ Γ |- tApp f a : B[a..] ]< l >
      | wfTermNat {Γ} :
          [ |- Γ ]< l > ->
          [ Γ |- tNat : U]< l >
      | wfTermBool {Γ} :
          [ |- Γ ]< l > ->
          [ Γ |- tBool : U]< l >
      | wfTermZero {Γ} :
          [ |- Γ ]< l > ->
          [ Γ |- tZero : tNat]< l >
      | wfTermSucc {Γ n} :
          [ Γ |- n : tNat]< l > ->
          [ Γ |- tSucc n : tNat]< l >
      | wfTermNatElim {Γ P hz hs n} :
        [ Γ ,, tNat |- P ]< l > ->
        [ Γ |- hz : P[tZero..]]< l > ->
        [ Γ |- hs : elimSuccHypTy P]< l > ->
        [ Γ |- n : tNat]< l > ->
        [ Γ |- tNatElim P hz hs n : P[n..]]< l >
      | wfTermTrue {Γ} :
          [ |- Γ ]< l > ->
          [ Γ |- tTrue : tBool]< l >
      | wfTermFalse {Γ} :
          [ |- Γ ]< l > ->
          [ Γ |- tFalse : tBool]< l >
      | wfTermAlpha {Γ n} :
          [ Γ |- n : tNat]< l > ->
          [ Γ |- tAlpha n : tBool]< l >
      | wfTermBoolElim {Γ P ht hf b} :
        [ Γ ,, tBool |- P ]< l > ->
        [ Γ |- ht : P[tTrue..]]< l > ->
        [ Γ |- hf : P[tFalse..]]< l > ->
        [ Γ |- b : tBool]< l > ->
        [ Γ |- tBoolElim P ht hf b : P[b..]]< l >
      | wfTermEmpty {Γ} :
          [ |- Γ ]< l > ->
          [ Γ |- tEmpty : U]< l >
      | wfTermEmptyElim {Γ P e} :
        [ Γ ,, tEmpty |- P ]< l > ->
        [ Γ |- e : tEmpty]< l > ->
        [ Γ |- tEmptyElim P e : P[e..]]< l >
      | wfTermConv {Γ} {t A B} :
          [ Γ |- t : A ]< l > -> 
          [ Γ |- A ≅ B ]< l > -> 
          [ Γ |- t : B ]< l >
      | ϝwfTerm {Γ t A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- t : A ]< l ,,l (ne, true) > ->
        [ Γ |- t : A ]< l ,,l (ne, false) > ->
        [ Γ |- t : A ]< l >
  (** **** Conversion of types *)
  with ConvTypeDecl  l : context -> term -> term  -> Type :=  
      | TypePiCong {Γ} {A B C D} :
          [ Γ |- A ]< l > ->
          [ Γ |- A ≅ B]< l > ->
          [ Γ ,, A |- C ≅ D]< l > ->
          [ Γ |- tProd A C ≅ tProd B D]< l >
      | TypeRefl {Γ} {A} : 
          [ Γ |- A ]< l > ->
          [ Γ |- A ≅ A ]< l >
      | convUniv {Γ} {A B} :
        [ Γ |- A ≅ B : U ]< l > -> 
        [ Γ |- A ≅ B ]< l >
      | ϝTypeConv {Γ A B n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- A ≅ B ]< l ,,l (ne, true) > ->
        [ Γ |- A ≅ B ]< l ,,l (ne, false) > ->
        [ Γ |- A ≅ B ]< l >
      | TypeSym {Γ} {A B} :
          [ Γ |- A ≅ B ]< l > ->
          [ Γ |- B ≅ A ]< l >
      | TypeTrans {Γ} {A B C} :
          [ Γ |- A ≅ B]< l > ->
          [ Γ |- B ≅ C]< l > ->
          [ Γ |- A ≅ C]< l >
  (** **** Conversion of terms *)
  with ConvTermDecl  l : context -> term -> term -> term -> Type :=
      | TermBRed {Γ} {a t A B} :
              [ Γ |- A ]< l > ->
              [ Γ ,, A |- t : B ]< l > ->
              [ Γ |- a : A ]< l > ->
              [ Γ |- tApp (tLambda A t) a ≅ t[a..] : B[a..] ]< l >
      | TermPiCong {Γ} {A B C D} :
          [ Γ |- A : U]< l > ->
          [ Γ |- A ≅ B : U ]< l > ->
          [ Γ ,, A |- C ≅ D : U ]< l > ->
          [ Γ |- tProd A C ≅ tProd B D : U ]< l >
      | TermAppCong {Γ} {a b f g A B} :
          [ Γ |- f ≅ g : tProd A B ]< l > ->
          [ Γ |- a ≅ b : A ]< l > ->
          [ Γ |- tApp f a ≅ tApp g b : B[a..] ]< l >
      | TermFunExt {Γ} {f g A B} :
          [ Γ |- A ]< l > ->
          [ Γ |- f : tProd A B ]< l > ->
          [ Γ |- g : tProd A B ]< l > ->
          [ Γ ,, A |- eta_expand f ≅ eta_expand g : B ]< l > ->
          [ Γ |- f ≅ g : tProd A B ]< l >
      | TermSuccCong {Γ} {n n'} :
          [ Γ |- n ≅ n' : tNat]< l > ->
          [ Γ |- tSucc n ≅ tSucc n' : tNat]< l >
      | TermNatElimCong {Γ P P' hz hz' hs hs' n n'} :
          [ Γ ,, tNat |- P ≅ P']< l > ->
          [ Γ |- hz ≅ hz' : P[tZero..]]< l > ->
          [ Γ |- hs ≅ hs' : elimSuccHypTy P]< l > ->
          [ Γ |- n ≅ n' : tNat]< l > ->
          [ Γ |- tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : P[n..]]< l >        
      | TermNatElimZero {Γ P hz hs} :
          [ Γ ,, tNat |- P ]< l > ->
          [ Γ |- hz : P[tZero..]]< l > ->
          [ Γ |- hs : elimSuccHypTy P]< l > ->
          [ Γ |- tNatElim P hz hs tZero ≅ hz : P[tZero..]]< l >   
      | TermNatElimSucc {Γ P hz hs n} :
          [ Γ ,, tNat |- P ]< l > ->
          [ Γ |- hz : P[tZero..]]< l > ->
          [ Γ |- hs : elimSuccHypTy P]< l > ->
          [ Γ |- n : tNat]< l > ->
          [ Γ |- tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]]< l >    
      | TermBoolElimCong {Γ P P' ht ht' hf hf' b b'} :
          [ Γ ,, tBool |- P ≅ P']< l > ->
          [ Γ |- ht ≅ ht' : P[tTrue..]]< l > ->
          [ Γ |- hf ≅ hf' : P[tFalse..]]< l > ->
          [ Γ |- b ≅ b' : tBool]< l > ->
          [ Γ |- tBoolElim P ht hf b ≅ tBoolElim P' ht' hf' b' : P[b..]]< l > 
      | TermBoolElimTrue {Γ P ht hf} :
          [ Γ ,, tBool |- P ]< l > ->
          [ Γ |- ht : P[tTrue..]]< l > ->
          [ Γ |- hf : P[tFalse..]]< l > ->
          [ Γ |- tBoolElim P ht hf tTrue ≅ ht : P[tTrue..]]< l >  
      | TermBoolElimFalse {Γ P ht hf} :
          [ Γ ,, tBool |- P ]< l > ->
          [ Γ |- ht : P[tTrue..]]< l > ->
          [ Γ |- hf : P[tFalse..]]< l > ->
          [ Γ |- tBoolElim P ht hf tFalse ≅ ht : P[tFalse..]]< l >
      | TermAlphaCong {Γ} {n n'} :
          [ Γ |- n ≅ n' : tNat]< l > ->
          [ Γ |- tAlpha n ≅ tAlpha n' : tBool]< l >
      | TypeAlphaConv {Γ n b} :
        [ |- Γ ]< l > ->
        in_LCon (pi1 l) n b ->
        [ Γ |- tAlpha (nat_to_term n) ≅ bool_to_term b : tBool ]< l >
      | TermEmptyElimCong {Γ P P' e e'} :
          [ Γ ,, tEmpty |- P ≅ P']< l > ->
          [ Γ |- e ≅ e' : tEmpty]< l > ->
          [ Γ |- tEmptyElim P e ≅ tEmptyElim P' e' : P[e..]]< l >
      | ϝTermConv {Γ t t' A n} {ne : not_in_LCon (pi1 l) n} : 
        [ Γ |- t ≅ t' : A ]< l ,,l (ne, true) > ->
        [ Γ |- t ≅ t' : A ]< l ,,l (ne, false) > ->
        [ Γ |- t ≅ t' : A ]< l >
      | TermRefl {Γ} {t A} :
          [ Γ |- t : A ]< l > -> 
          [ Γ |- t ≅ t : A ]< l >
      | TermConv {Γ} {t t' A B} :
          [ Γ |- t ≅ t': A ]< l > ->
          [ Γ |- A ≅ B ]< l > ->
          [ Γ |- t ≅ t': B ]< l >
      | TermSym {Γ} {t t' A} :
          [ Γ |- t ≅ t' : A ]< l > ->
          [ Γ |- t' ≅ t : A ]< l >
      | TermTrans {Γ} {t t' t'' A} :
          [ Γ |- t ≅ t' : A ]< l > ->
          [ Γ |- t' ≅ t'' : A ]< l > ->
          [ Γ |- t ≅ t'' : A ]< l >
      
  where "[ |- Γ ]< l >" := (WfContextDecl l Γ)
  and   "[ Γ |- T ]< l >" := (WfTypeDecl l Γ T)
  and   "[ Γ |- t : T ]< l >" := (TypingDecl l Γ T t)
  and   "[ Γ |- A ≅ B ]< l >" := (ConvTypeDecl l Γ A B)
  and   "[ Γ |- t ≅ t' : T ]< l >" := (ConvTermDecl l Γ T t t').

Lemma ϝwfCon {l Γ n} {ne : not_in_LCon (pi1 l) n} : 
        [ |- Γ ]< l ,,l (ne, true) > ->
        [ |- Γ ]< l ,,l (ne, false) > ->
        [ |- Γ ]< l >.
Proof.
  revert l n ne.
  induction Γ ; intros.
  - econstructor.
  - inversion H ; subst.
    inversion H0 ; subst.
    econstructor.
    + eapply IHΓ; eassumption.
    + eapply ϝwfType ; eassumption.
Qed.
      
  (** (Typed) reduction is defined afterwards,
  rather than mutually with the other relations. *)

  Local Coercion isterm : term >-> class.

  Record RedClosureDecl (l : wfLCon) (Γ : context) (A : class) (t u : term) := {
    reddecl_typ : match A with istype => [Γ |- t]< l > | isterm A => [Γ |- t : A]< l > end;
    reddecl_red : RedClosureAlg (l := l) t u;
    reddecl_conv : match A with istype => [ Γ |- t ≅ u ]< l > | isterm A => [Γ |- t ≅ u : A]< l > end;
  }.

  Notation "[ Γ |- t ⇒* t' ∈ A ]< l >" := (RedClosureDecl l Γ A t t').

End Definitions.

Definition TermRedClosure l Γ A t u := RedClosureDecl l Γ (isterm A) t u.
Definition TypeRedClosure l Γ A B := RedClosureDecl l Γ istype A B.

Notation "[ Γ |- t ⇒* u ∈ A ]< l >" := (RedClosureDecl l Γ A t u).

(** ** Instances *)
(** Used for printing (see Notations) and as a support for the generic typing
properties used for the logical relation (see GenericTyping). *)
Module DeclarativeTypingData.

  #[export] Instance WfContext_Decl : WfContext de := WfContextDecl.
  #[export] Instance WfType_Decl : WfType de := WfTypeDecl.
  #[export] Instance Typing_Decl : Inferring de := TypingDecl.
  #[export] Instance Inferring_Decl : Typing de := TypingDecl.
  #[export] Instance InferringRed_Decl : InferringRed de := TypingDecl.
  #[export] Instance ConvType_Decl : ConvType de := ConvTypeDecl.
  #[export] Instance ConvTerm_Decl : ConvTerm de := ConvTermDecl.
  #[export] Instance ConvNeuConv_Decl : ConvNeuConv de := ConvTermDecl.
  #[export] Instance RedType_Decl : RedType de := TypeRedClosure.
(*   #[export] Instance OneStepRedTerm_Decl : OneStepRedTerm de := OneRedTermDecl. *)
  #[export] Instance RedTerm_Decl : RedTerm de := TermRedClosure.

  Ltac fold_decl :=
    change WfContextDecl with (wf_context (ta := de)) in * ;
    change WfTypeDecl with (wf_type (ta := de)) in *;
    change TypingDecl with (typing (ta := de)) in * ;
    change ConvTypeDecl with (conv_type (ta := de)) in * ;
    change ConvTermDecl with (conv_term (ta := de)) in * ;
    change TypeRedClosure with (red_ty (ta := de)) in *;
    change TermRedClosure with (red_tm (ta := de)) in *.

  Smpl Add fold_decl : refold.

End DeclarativeTypingData.

(** ** Induction principles *)

(** We use Scheme to generate mutual induction principle. Sadly, Scheme uses
the product of the standard library, which is not universe polymorphic, which
causes universe issues, typically in the fundamental lemma. So
we use some Ltac code to generate properly polymorphic versions of the inductive
principle. We also use Ltac to generate the conclusion of the mutual induction
proof, to alleviate the user from the need to write it down every time: they
only need write the predicates to be proven. *)
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

Let _WfDeclInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _WfDeclInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let WfDeclInductionType :=
  ltac: (let ind := eval cbv delta [_WfDeclInductionType] zeta
    in _WfDeclInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma WfDeclInduction : WfDeclInductionType.
Proof.
  intros PL PCon PTy PTm PTyEq PTmEq test **.
  pose proof (_WfDeclInduction PL PCon PTy PTm PTyEq PTmEq test) as H.
  destruct H with (l := l) as [?[?[? []]]].
  all: try (assumption ; fail).
  repeat (split;[assumption|]); assumption.
Qed.

Definition WfDeclInductionConcl :=
  ltac:(
    let t := eval cbv delta [WfDeclInductionType] beta in WfDeclInductionType in
    let t' := remove_steps t in
    exact t').
End InductionPrinciples.

Arguments WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq : rename.

(** Typed reduction implies untyped reduction *)
Section TypeErasure.
  Import DeclarativeTypingData.

Lemma redtmdecl_red l Γ t u A : 
  [Γ |- t ⇒* u : A]< l > ->
  [t ⇒* u]< l >.
Proof.
apply reddecl_red.
Qed.

Lemma redtydecl_red l Γ A B : 
  [Γ |- A ⇒* B]< l > ->
  [A ⇒* B]< l >.
Proof.
apply reddecl_red.
Qed.

End TypeErasure.


(** Typing rules behave like presheaves on LContexts **)

Section LConTranslation.
  Import DeclarativeTypingData.
  
  Lemma WfContextDecl_trans {l l'} Γ (f : l' ≤ε l) :
    [ |- Γ ]< l > -> [ |- Γ ]< l' >
  with WfTypeDecl_trans {l l'} Γ {A} (f : l' ≤ε l) :
    [ Γ |- A ]< l > -> [ Γ |- A ]< l' >
  with TypingDecl_trans {l l'} Γ {t A} (f : l' ≤ε l) :
    [ Γ |- t : A ]< l > -> [ Γ |- t : A ]< l' >
  with ConvTypeDecl_trans {l l'} Γ {A B} (f : l' ≤ε l) :
    [ Γ |- A ≅ B]< l > -> [ Γ |- A ≅ B]< l' >
  with ConvTermDecl_trans {l l'} Γ {t u A} (f : l' ≤ε l) :
    [ Γ |- t ≅ u : A ]< l > -> [ Γ |- t ≅ u : A ]< l' >.
  Proof.
    intro IHΓ ; revert l' f.
    - induction IHΓ ; try now econstructor.
      (*intros l' f.
      case (decidInLCon l'.(pi1) n) ; intro H.
      + induction H ; [eapply IHIHΓ1 | eapply IHIHΓ2 ] ; now eapply LCon_le_in_LCon.
      + unshelve econstructor ; try assumption.
        * eapply IHIHΓ1 ; eapply LCon_le_up ; assumption.
        * eapply IHIHΓ2 ; eapply LCon_le_up ; assumption.*)
    - intro IHA ; revert l' f.
      induction IHA ; try now econstructor.
      intros l' f.
      case (decidInLCon l'.(pi1) n) ; intro H.
      + induction H ; [eapply IHIHA1 | eapply IHIHA2 ] ; now eapply LCon_le_in_LCon.
      + unshelve eapply ϝwfType ; try assumption.
        * eapply IHIHA1 ; eapply LCon_le_up ; assumption.
        * eapply IHIHA2 ; eapply LCon_le_up ; assumption.
    - intro IHt ; revert l' f.
      induction IHt ; try now econstructor.
      intros l' f.
      case (decidInLCon l'.(pi1) n) ; intro H.
      + induction H ; [eapply IHIHt1 | eapply IHIHt2 ] ; now eapply LCon_le_in_LCon.
      + unshelve eapply ϝwfTerm ; try assumption.
        * eapply IHIHt1 ; eapply LCon_le_up ; assumption.
        * eapply IHIHt2 ; eapply LCon_le_up ; assumption.
    - intro IHAB ; revert l' f.
      induction IHAB ; try now econstructor.
      intros l' f.
      case (decidInLCon l'.(pi1) n) ; intro H.
      + induction H ; [eapply IHIHAB1 | eapply IHIHAB2 ] ; now eapply LCon_le_in_LCon.
      + unshelve eapply ϝTypeConv ; try assumption.
        * eapply IHIHAB1 ; eapply LCon_le_up ; assumption.
        * eapply IHIHAB2 ; eapply LCon_le_up ; assumption.
    - intro IHtu ; revert l' f.
      induction IHtu ; try now econstructor.
      intros l' f.
      case (decidInLCon l'.(pi1) n) ; intro H.
      + induction H ; [eapply IHIHtu1 | eapply IHIHtu2 ] ; now eapply LCon_le_in_LCon.
      + unshelve eapply ϝTermConv ; try assumption.
        * eapply IHIHtu1 ; eapply LCon_le_up ; assumption.
        * eapply IHIHtu2 ; eapply LCon_le_up ; assumption.
Qed.
      
      
    

  
End LConTranslation.
