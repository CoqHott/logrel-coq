From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation.

Set Primitive Projections.
Set Universe Polymorphism.

Create HintDb substitution.
#[global] Hint Constants Opaque : substitution.
#[global] Hint Variables Transparent : substitution.
Ltac substitution := eauto with substitution.


(* The type of our inductively defined validity relation:
  for some R : VRel, R Γ validTy validSubst eqSubst says
  that according to R, Γ is valid and the associated type validity
  (resp. substitution validity, valid substitution equality) is validTy (resp. validSubst eqSubst).
  One should think of VRel as a functional relation taking one argument Γ and returning
  three outputs (validTy, validSubst and eqSubst) *)

  #[universes(polymorphic)]Definition VRel@{i j | i < j +} `{ta : tag} `{!WfContext ta} :=
  context ->
  (* (TypeLevel -> term -> Type@{i}) -> *)
  forall (validSubst : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]), Type@{i}),
  (forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ ]), validSubst Δ σ wfΔ -> Type@{i}) ->
  Type@{j}.

(* An VPack contains the data corresponding to the codomain of RedRel seen as a functional relation *)

Module VPack.

  #[universes(polymorphic)] Record VPack@{i} `{ta : tag} `{!WfContext ta} {Γ : context} :=
  {
    (* validTy : TypeLevel -> term -> Type@{i}; *)
    validSubst : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]), Type@{i} ;
    eqSubst : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ ]), validSubst Δ σ wfΔ -> Type@{i} ;
  }.

  Arguments VPack : clear implicits.
  Arguments VPack {_ _}.
End VPack.

Export VPack(VPack,Build_VPack).

(* Notation "[ P | Γ ||-v< l > A ]" := (@VPack.validTy Γ l A P). *)
Notation "[ P | Δ ||-v σ : Γ | wfΔ ]" := (@VPack.validSubst Γ Δ σ wfΔ) (at level 0, P, Δ, σ, Γ, wfΔ at level 50).
Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ]" := (@VPack.eqSubst Γ Δ σ σ' wfΔ vσ P) (at level 0, P, Δ, σ, σ', Γ, wfΔ, vσ at level 50).

(* An VPack it adequate wrt. a VRel when its three unpacked components are *)
#[universes(polymorphic)] Definition VPackAdequate@{i j} `{ta : tag} `{!WfContext ta} {Γ : context}
  (R : VRel@{i j}) (P : VPack@{i} Γ) : Type@{j} :=
  R Γ (*P.(VPack.validTy)*) P.(VPack.validSubst) P.(VPack.eqSubst).

Arguments VPackAdequate _ _ /.

Module VAd.

  #[universes(polymorphic)] Record > VAdequate `{ta : tag} `{!WfContext ta} {Γ : context} {R : VRel} :=
  {
    pack :> VPack Γ ;
    adequate :> VPackAdequate R pack
  }.

  Arguments VAdequate : clear implicits.
  Arguments VAdequate {_ _}.
  Arguments Build_VAdequate {_ _ _ _}.

End VAd.

Export VAd(VAdequate,Build_VAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion VAd.pack : VAdequate >-> VPack.
Coercion VAd.adequate : VAdequate >-> VPackAdequate.


Notation "[ R | ||-v Γ ]"                            := (VAdequate Γ R) (at level 0, R, Γ at level 50).
Notation "[ R | Δ ||-v σ : Γ | RΓ | wfΔ ]"           := (RΓ.(VPack.validSubst) Δ σ wfΔ) (at level 0, R, Δ, σ, Γ, RΓ, wfΔ at level 50).
Notation "[ R | Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ | vσ ]" := (RΓ.(VPack.eqSubst) Δ σ σ' wfΔ vσ) (at level 0, R, Δ, σ, σ', Γ, RΓ, wfΔ, vσ at level 50).

Record typeValidityPack `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeu ta} `{!RedType ta} `{!RedTerm ta}
  {Γ : context} {R : VRel} {RΓ : [ R | ||-v Γ ]}
  {l : TypeLevel} {A : term}
  {Δ : context} {σ : nat -> term} {wfΔ : [|- Δ ]} {vσ : [ R | Δ ||-v σ : Γ | RΓ | wfΔ]} :=
  {
    validTy : [ Δ ||-< l > A [ σ ] ] ;
    validTyExt : forall (σ' : nat -> term)
      (vσ' : [R| Δ ||-v σ' : Γ | RΓ | wfΔ])
      (vσσ' : [R| Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ | vσ]),
      [ Δ ||-< l > A [ σ ] ≅ A [ σ' ] | validTy ]
  }.

Arguments typeValidityPack : clear implicits.
Arguments typeValidityPack {_ _ _ _ _ _ _ _ _}.


Definition typeValidity `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeu ta} `{!RedType ta} `{!RedTerm ta}
  (Γ : context) (R : VRel) (RΓ : [ R | ||-v Γ ]) :
  TypeLevel -> term -> Type :=
  fun l A =>
    forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ ]) (vσ : [ R | Δ ||-v σ : Γ | RΓ | wfΔ]),
    typeValidityPack Γ R RΓ l A Δ σ wfΔ vσ.
    
Notation "[ R | Γ ||-v< l > A | RΓ ]" := (typeValidity Γ R RΓ l A) (at level 0, R, Γ, l, A, RΓ at level 50).


Definition emptyValidSubst `{ta : tag} `{!WfContext ta} : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]), Type := fun _ _ _ => unit.
Definition emptyEqSubst `{ta : tag} `{!WfContext ta} : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ]), emptyValidSubst Δ σ wfΔ -> Type := fun _ _ _ _ _ => unit.


Section snocValid.
  Context `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeu ta} `{!RedType ta} `{!RedTerm ta}
  {Γ : context} {R : VRel} {RΓ : [ R | ||-v Γ ]} {A : term} {l : TypeLevel}
  {vA : [R | Γ ||-v< l > A | RΓ ]}.

  Record snocValidSubst {Δ : context} {σ : nat -> term} {wfΔ : [|- Δ]} : Type := 
    {
      validTail : [ R | Δ ||-v ↑ >> σ : Γ | RΓ | wfΔ ] ;
      validHead : [ Δ ||-< l > σ var_zero : A[↑ >> σ] | validTy (vA Δ (↑ >> σ) wfΔ validTail) ]
    }.

  Arguments snocValidSubst : clear implicits.

  Record snocEqSubst {Δ : context} {σ σ' : nat -> term} {wfΔ : [|- Δ]} {vσ : snocValidSubst Δ σ wfΔ} : Type :=
    {
      eqTail : [ R | Δ ||-v ↑ >> σ ≅ ↑ >> σ' : Γ | RΓ | wfΔ | validTail vσ ] ;
      eqHead : [ Δ ||-< l > σ var_zero ≅ σ' var_zero : A[↑ >> σ] | validTy (vA Δ (↑ >> σ) wfΔ (validTail vσ)) ]
    }.
  
End snocValid.

Arguments snocValidSubst : clear implicits.
Arguments snocValidSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocEqSubst : clear implicits.
Arguments snocEqSubst {_ _ _ _ _ _ _ _ _}.


Inductive VR `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta}
  `{RedType ta} `{RedTerm ta} : VRel :=
  | VREmpty : VR ε emptyValidSubst emptyEqSubst
  | VRSnoc : forall {Γ A l}
    (RΓ : [ VR | ||-v Γ])
    (vA : [ VR | Γ ||-v< l > A | RΓ ]),
    VR (Γ ,, vass (Build_aname String.EmptyString) A) (snocValidSubst Γ VR RΓ A l vA) (snocEqSubst Γ VR RΓ A l vA).




