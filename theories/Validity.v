From LogRel.AutoSubst Require Import core unscoped Ast.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation.

Set Primitive Projections.
Set Universe Polymorphism.

Create HintDb substitution.
#[global] Hint Constants Opaque : substitution.
#[global] Hint Variables Transparent : substitution.
Ltac substitution := eauto with substitution.


(* The type of our inductively defined validity relation:
  for some R : VRel, R Γ eqSubst says
  that according to R, Γ is valid and the associated substitution validity and equality
  are validSubst and eqSubst.
  One should think of VRel as a functional relation taking one argument Γ and returning
  2 outputs validSubst and eqSubst *)

  #[universes(polymorphic)]Definition VRel@{i j | i < j +} `{ta : tag} `{!WfContext ta} :=
  forall 
    (Γ : context)
    (validSubst : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]), Type@{i})
    (eqSubst : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ ]), validSubst Δ σ wfΔ -> Type@{i}) 
    , Type@{j}.

(* An VPack contains the data corresponding to the codomain of VRel seen as a functional relation *)

Module VPack.

  #[universes(polymorphic)] Record VPack@{i} `{ta : tag} `{!WfContext ta} {Γ : context} :=
  {
    validSubst : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]), Type@{i} ;
    eqSubst : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ ]), validSubst Δ σ wfΔ -> Type@{i} ;
  }.

  Arguments VPack : clear implicits.
  Arguments VPack {_ _}.
  Arguments Build_VPack {_ _}.
End VPack.

Export VPack(VPack,Build_VPack).

Notation "[ P | Δ ||-v σ : Γ | wfΔ ]" := (@VPack.validSubst _ _ Γ P Δ σ wfΔ) (at level 0, P, Δ, σ, Γ, wfΔ at level 50).
Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ]" := (@VPack.eqSubst _ _ Γ P Δ σ σ' wfΔ vσ) (at level 0, P, Δ, σ, σ', Γ, wfΔ, vσ at level 50).

(* An VPack it adequate wrt. a VRel when its three unpacked components are *)
#[universes(polymorphic)] Definition VPackAdequate@{i j} `{ta : tag} `{!WfContext ta} {Γ : context}
  (R : VRel@{i j}) (P : VPack@{i} Γ) : Type@{j} :=
  R Γ P.(VPack.validSubst) P.(VPack.eqSubst).

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

Record typeValidity `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeu ta} `{!RedType ta} `{!RedTerm ta}
  {Γ : context} {VΓ : VPack Γ}
  {l : TypeLevel} {A : term} :=
  {
    validTy : forall {Δ : context} {σ : nat -> term}
      (wfΔ : [|- Δ ]) 
      (vσ : [ VΓ | Δ ||-v σ : Γ | wfΔ ])
      , [ Δ ||-< l > A [ σ ] ] ;
    validTyExt : forall {Δ : context} {σ σ' : nat -> term}
      (wfΔ : [|- Δ ])
      (vσ  : [ VΓ | Δ ||-v σ  : Γ | wfΔ ])
      (vσ' : [ VΓ | Δ ||-v σ' : Γ | wfΔ ])
      (vσσ' : [ VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ | vσ ])
      , [ Δ ||-< l > A [ σ ] ≅ A [ σ' ] | validTy wfΔ vσ ]
  }.

Arguments typeValidity : clear implicits.
Arguments typeValidity {_ _ _ _ _ _ _ _ _}.
    
Notation "[ P | Γ ||-v< l > A ]" := (typeValidity Γ P l A) (at level 0, P, Γ, l, A at level 50).

Definition emptyValidSubst `{ta : tag} `{!WfContext ta} : forall (Δ : context) (σ : nat -> term) (wfΔ : [|- Δ]), Type := fun _ _ _ => unit.
Definition emptyEqSubst `{ta : tag} `{!WfContext ta} : forall (Δ : context) (σ σ' : nat -> term) (wfΔ : [|- Δ]), emptyValidSubst Δ σ wfΔ -> Type := fun _ _ _ _ _ => unit.
Definition emptyVPack `{ta : tag} `{!WfContext ta} : VPack ε := 
  Build_VPack _ emptyValidSubst emptyEqSubst.

Section snocValid.
  Context `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeu ta} `{!RedType ta} `{!RedTerm ta}
  {Γ : context} {VΓ : VPack Γ} {A : term} {l : TypeLevel}
  {vA : [ VΓ | Γ ||-v< l > A ]}.

  Record snocValidSubst {Δ : context} {σ : nat -> term} {wfΔ : [|- Δ]} : Type := 
    {
      validTail : [ VΓ | Δ ||-v ↑ >> σ : Γ | wfΔ ] ;
      validHead : [ Δ ||-< l > σ var_zero : A[↑ >> σ] | validTy vA wfΔ validTail ]
    }.

  Arguments snocValidSubst : clear implicits.

  Record snocEqSubst {Δ : context} {σ σ' : nat -> term} {wfΔ : [|- Δ]} {vσ : snocValidSubst Δ σ wfΔ} : Type :=
    {
      eqTail : [ VΓ | Δ ||-v ↑ >> σ ≅ ↑ >> σ' : Γ | wfΔ | validTail vσ ] ;
      eqHead : [ Δ ||-< l > σ var_zero ≅ σ' var_zero : A[↑ >> σ] | validTy vA wfΔ (validTail vσ) ]
    }.
  
  Definition snocVPack na := Build_VPack (Γ ,, vass na A) snocValidSubst (@snocEqSubst).
End snocValid.

Arguments snocValidSubst : clear implicits.
Arguments snocValidSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocEqSubst : clear implicits.
Arguments snocEqSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocVPack : clear implicits.
Arguments snocVPack {_ _ _ _ _ _ _ _ _}.

Unset Elimination Schemes.

Inductive VR `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta}
  `{RedType ta} `{RedTerm ta} : VRel :=
  | VREmpty : VR ε emptyValidSubst emptyEqSubst
  | VRSnoc : forall {Γ na A l}
    (VΓ : VPack Γ)
    (VΓad : VPackAdequate VR VΓ)
    (VA : [ VΓ | Γ ||-v< l > A ]),
    VR (Γ ,, vass na A) (snocValidSubst Γ VΓ A l VA) (snocEqSubst Γ VΓ A l VA).


Set Elimination Schemes.

Notation "[||-v Γ ]"                             := [ VR | ||-v Γ ] (at level 0, Γ at level 50).
Notation "[ Δ ||-v σ : Γ | VΓ | wfΔ ]"           := [ VR | Δ ||-v σ : Γ | VΓ | wfΔ ]  (at level 0, Δ, σ, Γ, VΓ, wfΔ at level 50).
Notation "[ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ ]" := [ VR | Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | vσ ] (at level 0, Δ, σ, σ', Γ, VΓ, wfΔ, vσ at level 50).
Notation "[ Γ ||-v< l > A | VΓ ]"                := [ VΓ | Γ ||-v< l > A ] (at level 0, Γ, l , A, VΓ at level 50).


Section MoreDefs.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeu ta} `{RedType ta} `{RedTerm ta}.

  Definition validEmpty : [||-v ε ] := Build_VAdequate emptyVPack VREmpty.

  Definition validSnoc {Γ na A l} (VΓ : [||-v Γ]) (VA : [Γ ||-v< l > A | VΓ]) 
    : [||-v Γ ,, vass na A ] :=
    Build_VAdequate (snocVPack Γ VΓ A l VA na) (VRSnoc VΓ VΓ VA).

  Record termValidity {Γ l} {t A : term} {VΓ : [||-v Γ]} {VA : [Γ ||-v<l> A |VΓ]} : Type :=
    {
      validTm : forall {Δ σ} 
        (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
        [Δ ||-<l> t[σ] : A[σ] | validTy VA wfΔ Vσ ] ;
      validTmExt : forall {Δ : context} {σ σ' : nat -> term}
        (wfΔ : [|- Δ ])
        (Vσ  : [Δ ||-v σ  : Γ | VΓ | wfΔ ])
        (Vσ' : [ Δ ||-v σ' : Γ | VΓ | wfΔ ])
        (Vσσ' : [ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ | Vσ ]),
        [Δ ||-<l> t[σ] ≅ t[σ'] : A[σ] | validTy VA wfΔ Vσ ]
    }.
    
  Record typeEqValidity {Γ l} {A B : term} {VΓ : [||-v Γ]} {VA : [Γ ||-v<l> A |VΓ]} : Type :=
    {
      validTyEq : forall {Δ σ}
        (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
        [Δ ||-<l> A[σ] ≅ B[σ] | validTy VA wfΔ Vσ]
    }.
  
  Record termEqValidity {Γ l} {t u A : term} {VΓ : [||-v Γ]} {VA : [Γ ||-v<l> A |VΓ]} : Type :=
    {
      validTmEq : forall {Δ σ}
        (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ | wfΔ]),
        [Δ ||-<l> t[σ] ≅ u[σ] : A[σ] | validTy VA wfΔ Vσ]
    }.

  Record tmEqValidity {Γ l} {t u A : term} {VΓ : [||-v Γ]} : Type :=
    {
      Vty  : [Γ ||-v< l > A | VΓ] ;
      Vlhs : @termValidity Γ l t A VΓ Vty ; 
      Vrhs : @termValidity Γ l u A VΓ Vty ; 
      Veq  : @termEqValidity Γ l t u A VΓ Vty
    }.

End MoreDefs.

Arguments termValidity : clear implicits.
Arguments termValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_termValidity {_ _ _ _ _ _ _ _ _}.

Arguments typeEqValidity : clear implicits.
Arguments typeEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_typeEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments termEqValidity : clear implicits.
Arguments termEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_termEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments tmEqValidity : clear implicits.
Arguments tmEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_tmEqValidity {_ _ _ _ _ _ _ _ _}.

Notation "[ Γ ||-v< l > t : A | VΓ | VA ]"     := (termValidity Γ l t A VΓ VA) (at level 0, Γ, l, t, A, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > A ≅ B | VΓ | VA ]"     := (typeEqValidity Γ l A B VΓ VA) (at level 0, Γ, l, A, B, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > t ≅ u : A | VΓ | VA ]" := (termEqValidity Γ l t u A VΓ VA) (at level 0, Γ, l, t, u, A, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > t ≅ u : A | VΓ ]"      := (tmEqValidity Γ l t u A VΓ) (at level 0, Γ, l, t, u, A, VΓ at level 50).