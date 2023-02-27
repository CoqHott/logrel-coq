From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Untyped Weakening GenericTyping LogicalRelation Reduction Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Neutral Transitivity.
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


Lemma singleSubstΠ1 {Γ nF F G t l lF}
  (ΠFG : [Γ ||-<l> tProd nF F G])
  (RF : [Γ ||-<lF> F])
  (Rt : [Γ ||-<lF> t : F | RF]) :
  [Γ ||-<l> G[t..]].
Proof.
  apply invLRΠ in ΠFG; destruct ΠFG as [??? red ??? domRed codRed].
  unshelve eassert (h :=redtywf_whnf red _).
  1: constructor.
  symmetry in h; injection h; clear h; intros ;  subst.
  replace G[t..] with G[t .: wk_id (Γ:=Γ) >> tRel] by now bsimpl.
  unshelve eapply codRed.
  1: gen_typing.
  irrelevance0; tea.
  now bsimpl.
Qed.

Lemma singleSubstΠ2 {Γ nF nF' F F' G G' t t' l lF lF'}
  (ΠFG : [Γ ||-<l> tProd nF F G])
  (ΠFGeq : [Γ ||-<l> tProd nF F G ≅ tProd nF' F' G' | ΠFG])
  (RF : [Γ ||-<lF> F])
  (RF' : [Γ ||-<lF'> F'])
  (Rt : [Γ ||-<lF> t : F | RF]) 
  (Rt' : [Γ ||-<lF'> t' : F' | RF']) 
  (Rteq : [Γ ||-<lF> t ≅ t' : F | RF])
  (RGt : [Γ ||-<lF> G[t..]])
  (RGt' : [Γ ||-<lF'> G'[t'..]]) :
  [Γ ||-<lF> G[t..] ≅ G'[t'..] | RGt ].
Proof.
  pose (hΠ := invLRΠ ΠFG).
  assert (heq : [Γ ||-<l> tProd nF F G ≅ tProd nF' F' G' | LRPi' _ hΠ]) by irrelevance.
  destruct hΠ as [??? red ??? domRed codRed codExt]; clear ΠFG ΠFGeq.
  assert (wfΓ : [|-Γ]) by gen_typing.
  destruct heq as [??? red' ? domRedEq codRedEq]; cbn in *.
  unshelve eassert (h :=redtywf_whnf red _).  1: constructor.
  unshelve eassert (h' :=redtywf_whnf red' _).  1: constructor.
  symmetry in h; symmetry in h' ; injection h; injection h'; clear h h'; intros ;  subst.
  assert [Γ ||-<l> t' : F⟨wk_id (Γ:=Γ)⟩ | domRed Γ wk_id wfΓ].
  {
    eapply LRTmRedConv; tea.
    eapply LRTyEqSym. 
    replace F' with F'⟨wk_id (Γ := Γ)⟩ by now bsimpl.
    eapply domRedEq.
  }
  eapply transEq.
  2: (replace G'[t'..] with G'[t' .: wk_id (Γ:=Γ) >> tRel] by now bsimpl); eapply codRedEq.
  irrelevance0.
  2: eapply codExt.
  3: irrelevance0; tea; now bsimpl.
  1: now bsimpl.
  eassumption.
  Unshelve. all: tea.
  irrelevance0; tea; now bsimpl.
Qed.

Lemma substSΠaux {Γ nF F G t l} 
  (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΠFG : [Γ ||-v<l> tProd nF F G | VΓ])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF])
  (Δ : context) (σ : nat -> term) 
  (wfΔ : [ |-[ ta ] Δ]) (vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) :
  [Δ ||-< l > G[up_term_term σ][t[σ]..]].
Proof.
  eapply singleSubstΠ1.
  eapply (validTy VΠFG); tea.
  now eapply validTm.
  Unshelve. all: eassumption.
Qed.

Lemma substSΠ {Γ nF F G t l} 
  (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VΠFG : [Γ ||-v<l> tProd nF F G | VΓ])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] | VΓ].
Proof.
  (* assert (h : forall (Δ : context) (σ : nat -> term) (wfΔ : [ |-[ ta ] Δ]),
    [VΓ | Δ ||-v σ : Γ | wfΔ] -> [Δ ||-< l > G[up_term_term σ][t[σ]..]]).
  {
    intros;   }  *)
  refine ((fun h' => {| validTy := h' ; validTyExt := _ |}) _); cycle 1; intros.
  - replace G[t..][σ] with G[up_term_term σ][t[σ]..] by now bsimpl.
    now eapply substSΠaux.
  - replace G[_][_] with G[up_term_term σ'][t[σ']..] by now bsimpl.
    irrelevance0.
    2: eapply singleSubstΠ2.
    2: eapply (validTyExt VΠFG).
    2,3: tea.
    2, 3: now eapply validTm.
    2: now eapply validTmExt.
    1: fold subst_term; now bsimpl.
    now eapply substSΠaux.
    Unshelve. all: tea.
    now eapply substSΠaux.
Qed.

Lemma substSΠeq {Γ nF nF' F F' G G' t u l} 
  (VΓ : [||-v Γ])
  (VF : [Γ ||-v<l> F | VΓ])
  (VF' : [Γ ||-v<l> F' | VΓ])
  (VΠFG : [Γ ||-v<l> tProd nF F G | VΓ])
  (VΠFG' : [Γ ||-v<l> tProd nF' F' G' | VΓ])
  (VΠFGeq : [Γ ||-v<l> tProd nF F G ≅ tProd nF' F' G' | VΓ | VΠFG])
  (Vt : [Γ ||-v<l> t : F | VΓ | VF]) 
  (Vu : [Γ ||-v<l> u : F' | VΓ | VF']) 
  (Vtu : [Γ ||-v<l> t ≅ u : F | VΓ | VF]) 
  (VGt := substSΠ VΓ VF VΠFG Vt) :
  [Γ ||-v<l> G[t..] ≅ G'[u..] | VΓ | VGt].
Proof.
  constructor; intros.
  replace G'[_][_] with G'[up_term_term σ][u[σ]..] by now bsimpl.
  irrelevance0.
  2: eapply singleSubstΠ2.
  2: now eapply (validTyEq VΠFGeq).
  4: now eapply validTmEq.
  2,3: now eapply validTm.
  1: fold subst_term; now bsimpl.
  now eapply substSΠaux.
  Unshelve. all: tea.
  now eapply substSΠaux.
Qed.


End SingleSubst.