From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral Transitivity.
From LogRel.Substitution Require Import Irrelevance Properties Conversion.

Set Universe Polymorphism.

Section SingleSubst.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma substS {Γ F G t l} (VΓ : [||-v Γ]) nF
  (VF : [Γ ||-v<l> F | VΓ])
  (VG : [Γ,, vass nF F ||-v<l> G | validSnoc nF VΓ VF])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] | VΓ].
Proof.
  assert (eq : forall σ, G[t..][σ] = G[t[σ] .: σ]) by (intros; now asimpl).
  assert (h : forall (Δ : context) (σ : nat -> term) (wfΔ : [ |-[ ta ] Δ]),
    [VΓ | Δ ||-v σ : _ | wfΔ] -> [Δ ||-< l > G[t..][σ]]).
  { 
    intros; rewrite eq.
    unshelve eapply validTy. 3,4:  tea.
    now eapply consSubstSvalid.
  }
  exists h; intros; rewrite eq.
  irrelevance0. 1: symmetry; apply eq.
  eapply validTyExt.
  1: eapply consSubstS; now  eapply validTm.
  now eapply consSubstSEqvalid.
  Unshelve. all: eassumption.
Qed.

Lemma substSEq {Γ F F' G G' t t' l} (VΓ : [||-v Γ]) nF 
  (VF : [Γ ||-v<l> F | VΓ])
  (VF' : [Γ ||-v<l> F' | VΓ])
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VΓF := validSnoc nF VΓ VF)
  (VΓF' := validSnoc nF VΓ VF')
  (VG : [Γ,, vass nF F ||-v<l> G | VΓF])
  (VG' : [Γ,, vass nF F' ||-v<l> G' | VΓF'])
  (VGG' : [Γ ,, vass nF F ||-v<l> G ≅ G' | VΓF | VG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF'])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ | substS VΓ nF VF VG Vt].
Proof.
  assert (eq : forall G t σ, G[t..][σ] = G[t[σ] .: σ]) by (intros; now asimpl).
  constructor; intros.
  assert (VtF' : [Γ ||-v<l> t : F' | VΓ | VF']) by now eapply conv.
  pose proof (consSubstSvalid (nA:=nF) _ _ Vσ _ Vt').
  pose proof (consSubstSvalid (nA:=nF) _ _ Vσ _ VtF').
  rewrite eq; irrelevance0.
  1: symmetry; apply eq.
  eapply transEq.
  - unshelve now eapply validTyEq.
    2: now eapply consSubstSvalid.
  - eapply validTyExt; tea.
    unshelve econstructor.
    1: eapply reflSubst.
    eapply validTmEq.
    now eapply convEq.
    Unshelve. all: tea.
    now eapply validTy.
Qed.


Lemma substSTm {Γ F G t f l} (VΓ : [||-v Γ]) nF
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc nF VΓ VF)
  (VG : [Γ,, vass nF F ||-v<l> G | VΓF])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) 
  (Vf : [Γ ,, vass nF F ||-v<l> f : G | VΓF | VG]):
  [Γ ||-v<l> f[t..] : G[t..] | VΓ | substS VΓ nF VF VG Vt].
Proof.
  assert (eq : forall G t σ, G[t..][σ] = G[t[σ] .: σ]) by (intros; now asimpl).
  constructor; intros; rewrite !eq; irrelevance0. 
  1,3: symmetry; apply eq.
  - now eapply validTm.
  - eapply validTmExt; tea.
    1: now apply consSubstSvalid.
    now apply consSubstSEqvalid.
    Unshelve. 1,3: eassumption.
    now apply consSubstSvalid.
Qed.

Lemma substSTmEq {Γ F F' G G' t t' f f' l} (VΓ : [||-v Γ]) nF 
  (VF : [Γ ||-v<l> F | VΓ])
  (VF' : [Γ ||-v<l> F' | VΓ])
  (VFF' : [Γ ||-v<l> F ≅ F' | VΓ | VF])
  (VΓF := validSnoc nF VΓ VF)
  (VΓF' := validSnoc nF VΓ VF')
  (VG : [Γ,, vass nF F ||-v<l> G | VΓF])
  (VG' : [Γ,, vass nF F' ||-v<l> G' | VΓF'])
  (VGG' : [Γ ,, vass nF F ||-v<l> G ≅ G' | VΓF | VG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Vt' : [Γ ||-v<l> t' : F' | VΓ | VF'])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) 
  (Vf : [Γ ,, vass nF F ||-v<l> f : G | VΓF | VG])
  (Vf' : [Γ ,, vass nF F' ||-v<l> f' : G' | VΓF' | VG'])
  (Vff' : [Γ ,, vass nF F ||-v<l> f ≅ f' : G | VΓF | VG]) :
  [Γ ||-v<l> f[t..] ≅ f'[t..] : G[t..] | VΓ | substS VΓ nF VF VG Vt].
Proof.
  assert (eq : forall G t σ, G[t..][σ] = G[t[σ] .: σ]) by (intros; now asimpl).
  constructor; intros; rewrite !eq; irrelevance0. 
  1: symmetry; apply eq.
  unshelve now eapply validTmEq.
  2: now eapply consSubstSvalid.
Qed.

(* Skipping a series of lemmas on single substitution of a weakened term *)

(* Lemma substLiftS {Γ F G t l} (VΓ : [||-v Γ]) nF
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc nF VΓ VF)
  (VG : [Γ,, vass nF F ||-v<l> G | VΓF])
  (VF' := wk1ValidTy VΓ nF VF VF)
  (Vt : [Γ,, vass nF F ||-v<l> t : F⟨@wk1 Γ nF F⟩ | VΓF | VF']) :
  [Γ ,, vass nF F ||-v<l> G[t .: (S >> tRel)] | VΓF].
Proof. *)

End SingleSubst.