(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICPosition.
From MetaCoq.PCUIC Require Export PCUICCumulativitySpec.
From MetaCoq.PCUIC Require Export PCUICCases PCUICNormal.


Import MCMonadNotation.

(* TODO: remove this export *)
From MetaCoq Require Export LibHypsNaming.

Require Import ssreflect.
Require Import Equations.Type.Relation.
From Equations Require Import Equations.
Set Equations With UIP.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Reserved Notation "[   |- Γ ]" (at level 0).
Reserved Notation "[ Γ |- T ]" (at level 0).
Reserved Notation "[ Γ |- t ::: T ]" (at level 0).
Reserved Notation "[ Γ |- T ≅ T' ]" (at level 0).
Reserved Notation "[ Γ |- t ≅ t' ::: T ]" (at level 0).
Reserved Notation "[ Γ |- t ⇒ u ::: A ]" (at level 0).
Reserved Notation "[ Γ |- A ⇒ B ]" (at level 0).
Reserved Notation "[ Γ |- t ⇒* t' ::: A ]" (at level 0).
Reserved Notation "[ Γ |- A ⇒* B ]" (at level 0).
Print tProd.

Definition U := tSort Universe.type0.

Inductive wfType  : context -> term -> Type :=
    | wfTypeU {Γ} : 
        [ |- Γ ] -> 
        [ Γ |- U ] 
    | wfTypeProd {Γ} {na : aname} {A B} : 
        [ Γ |- A ] -> 
        [Γ ,, (vass na A) |- B ] -> 
        [ Γ |- tProd na A B ]
    | wfTypeUniv {Γ} {A} :
        [ Γ |- A ::: U ] -> 
        [ Γ |- A ]

with wfContext : context -> Type :=
    | connil : wfContext []
    | concons {na} {Γ} {A} : [ Γ |- A ] -> [ |-  Γ ,, vass na A]

with wfTerm : context -> term -> term -> Type :=
    | wfVar {Γ} {n decl} :
        [   |- Γ ] ->
        nth_error Γ n = Some decl ->
        [ Γ |- tRel n ::: lift0 (S n) decl.(decl_type) ]
    | wfTermProd {Γ} {na} {A B} :
        [ Γ |- A ::: U] -> 
        [Γ ,, (vass na A) |- B ::: U ] ->
        [ Γ |- tProd na A B ::: U ]
    | wfTermLam {Γ} {na} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, vass na A |- t ::: B ] -> 
        [ Γ |- tLambda na A t ::: tProd na A B] 
    | wfTermConv {Γ} {t A B} :
        [ Γ |- t ::: A ] -> 
        [ Γ |- A ≅ B ] -> 
        [ Γ |- t ::: B ]
    | wfTermApp {Γ} {na} {f a A B} :
        [ Γ |- f ::: tProd na A B ] -> 
        [ Γ |- a ::: A ] -> 
        [ Γ |- tApp f a ::: B{0 := a} ]
    
with convType : context -> term -> term  -> Type :=
    | convUniv {Γ} {A B} :
        [ Γ |- A ≅ B ::: U ] -> 
        [ Γ |- A ≅ B ]
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
    | TypePiCong {Γ} {na nb} {A B C D} :
        [ Γ |- A] ->
        [ Γ |- A ≅ B] ->
        [ Γ ,, vass na A |- C ≅ D] ->
        [ Γ |- tProd na A C ≅ tProd nb B D]

with convTerm : context -> term -> term -> term -> Type :=
    | TermRefl {Γ} {t A} :
        [ Γ |- t ::: A ] -> 
        [ Γ |- t ≅ t ::: A ]
    | TermSym {Γ} {t t' A} :
        [ Γ |- t ≅ t' ::: A ] ->
        [ Γ |- t' ≅ t ::: A ]
    | TermTrans {Γ} {t t' t'' A} :
        [ Γ |- t ≅ t' ::: A ] ->
        [ Γ |- t' ≅ t'' ::: A ] ->
        [ Γ |- t ≅ t'' ::: A ]
    | TermConv {Γ} {t t' A B} :
        [ Γ |- t ≅ t'::: A ] ->
        [ Γ |- A ≅ B ] ->
        [ Γ |- t ≅ t'::: B ]
    | TermPiCong {Γ} {na nb } {A B C D} :
        [ Γ |- A ] ->
        [ Γ |- A ≅ B ::: U ] ->
        [ Γ ,, vass na A |- C ≅ D ::: U ] ->
        [ Γ |- tProd na A C ≅ tProd nb B D ::: U ]
    | TermAppCong {Γ} {na} {a b f g A B} :
        [ Γ |- f ≅ g ::: tProd na A B ] ->
        [ Γ |- a ≅ b ::: A ] ->
        [ Γ |- tApp f a ≅ tApp g b ::: B{0 := a} ]
    | TermBRed {Γ} {na} {a t A B} :
        [ Γ |- A ] ->
        [ Γ ,, vass na A |- t ::: B ] ->
        [ Γ |- a ::: A ] ->
        [ Γ |- tApp (tLambda na A t) a ≅ t{0 := a} ::: B{0 := a} ]
    | TermFunExt {Γ} {na nb} {f g A B} :
        [ Γ |- A ] ->
        [ Γ |- f ::: tProd na A B ] ->
        [ Γ |- g ::: tProd nb A B ] ->
        [ Γ ,, vass na f |- tApp (lift0 1 f) (tRel 0) ≅ tApp (lift0 1 g) (tRel 0) ::: B ] ->
        [ Γ |- f ≅ g ::: tProd na A B ]

    
where "[   |- Γ ]" := (wfContext Γ)
and   "[ Γ |- T ]" := (wfType Γ T)
and   "[ Γ |- t ::: T ]" := (wfTerm Γ t T)
and   "[ Γ |- A ≅ B ]" := (convType Γ A B)
and   "[ Γ |- t ≅ t' ::: T ]" := (convTerm Γ t t' T).

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

End InductionPrinciples.

Inductive termRed (Γ : context) : term -> term -> term -> Type :=
    | conv {A B t u} : 
        [ Γ |- t ⇒ u ::: A ] ->
        [ Γ |- A ≅ B ] ->
        [ Γ |- t ⇒ u ::: B ]
    | appSubst {na A B t u a} :
        [ Γ |- t ⇒ u ::: tProd na A B] ->
        [ Γ |- a ::: A ] ->
        [ Γ |- tApp t a ⇒ tApp u a ::: B{0 := a} ]
    | BRed {na} {A B a t} :
        [ Γ |- A ] -> 
        [ Γ ,, vass na A |- t ::: B ] ->
        [ Γ |- a ::: A ] ->
        [ Γ |- tApp (tLambda na A t) a ⇒ t ::: B{0 := a} ]

where "[ Γ |- t ⇒ u ::: A ]" := (termRed Γ t u A).
    
Inductive typeRed (Γ : context) : term -> term -> Type :=
    | typeRedUniv {A B} :
        [ Γ |- A ⇒ B ::: U ] ->
        [ Γ |- A ⇒ B ]
where "[ Γ |- A ⇒ B ]" := (typeRed Γ A B).

Inductive termRedClosure (Γ : context) : term -> term -> term -> Type :=
    | termRedId {t A} :
        [ Γ |- t ::: A ] ->
        [ Γ |- t ⇒* t ::: A ]
    | termRedSucc {A t t' u} :
        [ Γ |- t ⇒ t' ::: A ] ->
        [ Γ |- t' ⇒* u ::: A ] ->
        [ Γ |- t ⇒* u ::: A ]
where "[ Γ |- t ⇒* t' ::: A ]" := (termRedClosure Γ t t' A).

Inductive typeRedClosure (Γ : context) : term -> term -> Type :=
| typeRedId {A} :
    [ Γ |- A  ] ->
    [ Γ |- A ⇒* A]
| typeRedSucc {A A' B} :
    [ Γ |- A ⇒ A' ] ->
    [ Γ |- A' ⇒* B ] ->
    [ Γ |- A ⇒* B ]
where "[ Γ |- A ⇒* B ]" := (typeRedClosure Γ A B). 


Definition termRedStrict (Γ : context) (t u A : term) {t'} : Type :=
    [ Γ |- t ⇒ t' ::: A ] × [Γ |- t' ⇒* u ::: A].


Definition typeRedStrict (Γ : context) (A B : term) {A'} : Type :=
    [ Γ |- A ⇒ A'] × [Γ |- A' ⇒* B].


Definition termRedWHNF (Γ : context) (t u A : term) : Type :=
        [ Γ |- t ⇒* u ::: A ] × (whnf RedFlags.default empty_global_env Γ u).


(*Type reduction to whnf*)
Definition typeRedWHNF (Γ : context) (A B : term) : Type :=
    [ Γ |- A ⇒* B ] × (whnf RedFlags.default empty_global_env Γ B).

Definition termEqWF (Γ : context) (t u A : term) : Type :=
    [Γ |- t ::: A] × [Γ |- u ::: A] × [Γ |- t ≅ u ::: A].


Definition typeEqWF (Γ : context) (A B : term) : Type :=
    [Γ |- A] × [Γ |- B] × [Γ |- A ≅ B].
 

Notation "[ Γ |- t ⇒⁺ u ::: A ]" := (termRedStrict Γ t u A) (at level 0).   
Notation "[ Γ |- A ⇒⁺ B ]" := (typeRedStrict Γ A B) (at level 0).   
Notation "[ Γ |- t ↘ u ::: A ]" := (termRedWHNF Γ t u A) (at level 0).
Notation "[ Γ |- A ↘ B ]" := (typeRedWHNF Γ A B) (at level 0).
Notation "[ Γ |- t :≡: u ::: A ]" := (termEqWF Γ t u A) (at level 0).
Notation "[ Γ |- A :≡: B ]" := (typeEqWF Γ A B) (at level 0).

Record TermRedWF (Γ : context) (t u A : term) : Type := mkTermRedWF {
    wft : [Γ |- t ::: A];
    wfu : [Γ |- u ::: A];
    C   : [Γ |- t ⇒* u ::: A]
}.


Record TypeRedWF (Γ : context) (A B : term) : Type := mkTypeRedWF {
    wfA : [Γ |- A];
    wfB : [Γ |- B];
    D   : [Γ |- A ⇒* B]
}.

Notation "[ Γ |- t :⇒*: u ::: A ]" := (TermRedWF Γ t u A) (at level 0).   
Notation "[ Γ |- A :⇒*: B ]" := (TypeRedWF Γ A B) (at level 0).   
