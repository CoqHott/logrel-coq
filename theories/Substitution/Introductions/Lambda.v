From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Pi.

Set Universe Polymorphism.

Section LambdaValid.
Context `{GenericTypingProperties}.

Context {Γ nF F G l} {VΓ : [||-v Γ]} (VF : [Γ ||-v<l> F | VΓ]) 
  (VΓF := validSnoc nF VΓ VF)
  (VG : [Γ ,, vass nF F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma lamValid {t} (Vt : [Γ ,, vass nF F ||-v<l> t : G | VΓF | VG])
   :
    [Γ ||-v<l> tLambda nF F t : tProd nF F G | VΓ | VΠFG ].
Proof.
  admit.
Admitted.

Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ nF F)
  (Vfg : [Γ ,, vass nF F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTy VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd nF F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd nF F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd nF F G)[σ] | RΠFG ].
Proof.
  admit.
Admitted.


Lemma etaeqValid {f g} (ρ := @wk1 Γ nF F)
  (Vf : [Γ ||-v<l> f : tProd nF F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd nF F G | VΓ | VΠFG ]) 
  (Vfg : [Γ ,, vass nF F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd nF F G | VΓ | VΠFG].
Proof.
  admit.
Admitted.

End LambdaValid.