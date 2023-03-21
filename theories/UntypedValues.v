From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction GenericTyping.

Unset Elimination Schemes.

Inductive snf (r : term) : Type :=
  | snf_tSort {s} : [ r ⇒* tSort s ] -> snf r
  | snf_tProd {na A B} : [ r ⇒* tProd na A B ] -> snf A -> snf B -> snf r
  | snf_tLambda {na A t} : [ r ⇒* tLambda na A t ] -> snf A -> snf t -> snf r
  | snf_sne {n} : [ r ⇒* n ] -> sne n -> snf r
with sne (r : term) : Type :=
  | sne_tRel {v} : r = tRel v -> sne r
  | sne_tApp {n t} : r = tApp n t -> sne n -> snf t -> sne r.

Set Elimination Schemes.

Section rect.

Variable 
  (P : forall r, snf r -> Type)
  (Q : forall n, sne n -> Type)
  (ptSort : forall r s (e : [ r ⇒* tSort s ]), P _ (snf_tSort r e))
  (ptProd : forall r na A B (e : [ r ⇒* tProd na A B ])
    (s1 : snf A), P A s1 -> forall (s2 : snf B), P B s2 ->  P _ (snf_tProd _ e s1 s2))
  (ptLambda : forall r na A t (e : [ r ⇒* tLambda na A t ])
    (s1 : snf A), P _ s1 -> forall (s2 : snf t), P _ s2 -> P _ (snf_tLambda _ e s1 s2))
  (ptne : forall r n (e : [ r ⇒* n ]) (s : sne n), Q _ s -> P _ (snf_sne _ e s))
  (ptRel : forall r v (e : r = tRel v), Q _ (sne_tRel _ e))
  (ptApp : forall r n t (e : r = tApp n t),
    forall (s1 : sne n), Q _ s1 -> forall (s2 : snf t), P _ s2 ->  Q _ (sne_tApp _ e s1 s2))
.

Fixpoint snf_rect (r : term) (s : snf r) : P r s :=
match s with
 | snf_tSort _ e => ptSort _ _ e
 | snf_tProd _ e s1 s2 => ptProd _ _ _ _ e s1 (snf_rect _ s1) s2 (snf_rect _ s2)
 | snf_tLambda _ e s1 s2 => ptLambda _ _ _ _ e s1 (snf_rect _ s1) s2 (snf_rect _ s2)
 | snf_sne _ e s => ptne _ _ e s (sne_rect _ s)
end

with sne_rect (n : term) (s : sne n) : Q n s :=
match s with
 | sne_tRel _ e => ptRel _ _ e
 | sne_tApp _ e s1 s2 => ptApp _ _ _ e s1 (sne_rect _ s1) s2 (snf_rect _ s2)
end.

End rect.

Definition snf_rec
  (P : forall r : term, snf r -> Set)
  (Q : forall r : term, sne r -> Set) := snf_rect P Q.

Definition snf_ind
  (P : forall r : term, snf r -> Prop)
  (Q : forall r : term, sne r -> Prop) := snf_rect P Q.

Definition sne_rec
  (P : forall r : term, snf r -> Set)
  (Q : forall r : term, sne r -> Set) := sne_rect P Q.

Definition sne_ind
  (P : forall r : term, snf r -> Prop)
  (Q : forall r : term, sne r -> Prop) := sne_rect P Q.

Definition snf_sne_rect P Q p1 p2 p3 p4 p5 p6 :=
  pair (snf_rect P Q p1 p2 p3 p4 p5 p6) (sne_rect P Q p1 p2 p3 p4 p5 p6).

Lemma sne_whne : forall (t : term), sne t -> whne t.
Proof.
apply sne_rect with (P := fun _ _ => True); intros; subst; constructor; assumption.
Qed.

Lemma snf_red : forall t u, [ t ⇒* u ] -> snf u -> snf t.
Proof.
intros t u Hr Hu; destruct Hu.
+ eapply snf_tSort.
  transitivity u; eassumption.
+ eapply snf_tProd.
  - transitivity u; eassumption.
  - assumption.
  - assumption.
+ eapply snf_tLambda.
  - transitivity u; eassumption.
  - assumption.
  - assumption.
+ eapply snf_sne.
  - transitivity u; eassumption.
  - eassumption.
Qed.

Inductive isSNType : term -> Type :=
  | UnivType {s} : isSNType (tSort s)
  | ProdType {na A B} : snf A -> snf B -> isSNType (tProd na A B)
  | NeType {A}  : sne A -> isSNType A.

Inductive isSNFun : term -> Type :=
  | LamFun {na A t} : snf A -> snf t -> isSNFun (tLambda na A t)
  | NeFun  {f} : sne f -> isSNFun f.

Lemma isSNType_snf t : isSNType t -> snf t.
Proof.
destruct 1.
+ eapply snf_tSort; reflexivity.
+ eapply snf_tProd; first[reflexivity|assumption].
+ eapply snf_sne; first[reflexivity|assumption].
Qed.

Lemma isSNType_whnf t : isSNType t -> whnf t.
Proof.
destruct 1; constructor.
apply sne_whne; assumption.
Qed.

Lemma isSNFun_snf t : isSNFun t -> snf t.
Proof.
destruct 1.
+ eapply snf_tLambda; first[reflexivity|assumption].
+ eapply snf_sne; first[reflexivity|assumption].
Qed.

Lemma isSNFun_whnf t : isSNFun t -> whnf t.
Proof.
destruct 1; constructor.
apply sne_whne; assumption.
Qed.

Lemma isSNType_isType t : isSNType t -> isType t.
Proof.
destruct 1; constructor; now apply sne_whne.
Qed.

Lemma isSNFun_isFun t : isSNFun t -> isFun t.
Proof.
destruct 1; constructor; now apply sne_whne.
Qed.

Section RenSnf.

  Notation credalg_wk := (credalg_wk nil nil).

  Lemma snf_sne_ren :
    prod (forall t, snf t -> forall ρ, snf (t⟨ρ⟩)) (forall t, sne t -> forall ρ, sne (t⟨ρ⟩)).
  Proof.
  apply snf_sne_rect.
  + intros r s Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSort; eassumption.
  + intros r na A B Hr HA IHA HB IHB ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tProd; eauto.
  + intros r na A t Hr HA IHA Ht IHt ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tLambda; eauto.
  + intros r n Hr Hn IHn ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_sne; eauto.
  + intros r v -> ρ; econstructor; reflexivity.
  + intros r n t -> Hn IHn Ht IHt ρ.
    cbn; eapply sne_tApp; eauto.
  Qed.

  Lemma sne_ren ρ t : sne t -> sne (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

  Lemma snf_ren ρ t : snf t -> snf (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

End RenSnf.

Lemma isSNType_ren ρ t : isSNType t -> isSNType (t⟨ρ⟩).
Proof.
destruct 1; cbn; constructor; first [apply sne_ren|apply snf_ren]; assumption.
Qed.

Lemma isSNFun_ren ρ t : isSNFun t -> isSNFun (t⟨ρ⟩).
Proof.
destruct 1; cbn; constructor; first [apply sne_ren|apply snf_ren]; assumption.
Qed.

Module WeakValuesData.

#[export] Instance TypeWhne {ta} : Notations.TypeNe ta := fun Γ A => whne A.
#[export] Instance TypeWhnf {ta} : Notations.TypeNf ta := fun Γ A => ∑ B, [ A ⇒* B ] × whnf B.
#[export] Instance TermWhne {ta} : Notations.TermNe ta := fun Γ A t => whne t.
#[export] Instance TermWhnf {ta} : Notations.TermNf ta := fun Γ A t => ∑ u, [ t ⇒* u ] × whnf u.

End WeakValuesData.

Module WeakValuesProperties.

Export WeakValuesData.

Section Properties.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!OneStepRedTerm ta} `{!RedTerm ta} `{!RedTypeProperties} `{!RedTermProperties}.

  #[export] Instance TypeWhneProperties : TypeNeProperties.
  Proof.
  split.
  + intros; now apply Weakening.whne_ren.
  + intros Γ A HA; exists A; split; [reflexivity|now apply whnf_whne].
  + intros; assumption.
  + intros; assumption.
  Qed.

  #[export] Instance TypeWhnfProperties : TypeNfProperties.
  Proof.
  split.
  + intros Γ Δ A ρ _ [B [? ?]].
    exists (B⟨ρ⟩); split.
    - now apply (credalg_wk Γ Δ).
    - now apply Weakening.whnf_ren.
  + intros Γ A B ? [C [? ?]].
    exists C; split.
    - transitivity B; [eapply redty_red| ]; eassumption.
    - assumption.
  + exists (tSort set); split; [reflexivity|constructor].
  + intros; eexists; split; [reflexivity|constructor].
  Qed.

  #[export] Instance TermWhneProperties : TermNeProperties.
  Proof.
  split.
  + intros; now apply Weakening.whne_ren.
  + intros; eexists; split; [reflexivity|now constructor].
  + intros; assumption.
  + intros; assumption.
  + constructor.
  + constructor; assumption.
  Qed.

  #[export] Instance TermWhnfProperties : TermNfProperties.
  Proof.
  split.
  + intros Γ Δ t A ρ _ [B [? ?]].
    exists (B⟨ρ⟩); split.
    - now apply (credalg_wk Γ Δ).
    - now apply Weakening.whnf_ren.
  + intros; assumption.
  + intros Γ t u A ? [r [? ?]].
    exists r; split.
    - transitivity u; [eapply redtm_red| ]; eassumption.
    - assumption.
  + intros; eexists; split; [reflexivity|constructor].
  + intros; eexists; split; [reflexivity|constructor].
  Qed.

End Properties.

End WeakValuesProperties.

