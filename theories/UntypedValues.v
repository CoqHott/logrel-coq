Require Import Coq.Arith.EqNat.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms UntypedReduction Weakening GenericTyping.
(*
Unset Elimination Schemes.

Inductive snf l (r : term) : Type :=
  | snf_tSort {s} : [ r ⇒* tSort s ]< l > -> snf l r
  | snf_tProd {A B} : [ r ⇒* tProd A B ]< l > -> snf l A -> snf l B -> snf l r
  | snf_tLambda {A t} : [ r ⇒* tLambda A t ]< l > -> snf l A -> snf l t -> snf l r
  | snf_tNat : [ r ⇒* tNat ]< l > -> snf l r
  | snf_tZero : [ r ⇒* tZero ]< l > -> snf l r
  | snf_tSucc {n} : [ r ⇒* tSucc n ]< l > -> snf l n -> snf l r
  | snf_tEmpty : [ r ⇒* tEmpty ]< l > -> snf l r
  | snf_tBool : [ r ⇒* tBool ]< l > -> snf l r
  | snf_tTrue : [ r ⇒* tTrue ]< l > -> snf l r
  | snf_tFalse : [ r ⇒* tFalse ]< l > -> snf l r
  | snf_sne {n} : [ r ⇒* n ]< l > -> sne l n -> snf l r
with sne l (r : term) : Type :=
  | sne_tRel {v} : r = tRel v -> sne l r
  | sne_tApp {n t} : r = tApp n t -> sne l n -> snf l t -> sne l r
  | sne_tNatElim {P hz hs n} : r = tNatElim P hz hs n -> snf l P -> snf l hz -> snf l hs -> sne l n -> sne l r
  | sne_tBoolElim {P ht hf b} : r = tNatElim P ht hf b -> snf l P -> snf l ht -> snf l hf -> sne l b -> sne l r
  | sne_tEmptyElim {P e} : r = tEmptyElim P e -> snf l P -> sne l e -> sne l r
  | sne_tAlpha {n} : r = tAlpha n -> sne l n -> sne l r
.

Set Elimination Schemes.

Scheme
  Induction for snf Sort Type with
  Induction for sne Sort Type.

Definition snf_rec l
  (P : forall r : term, snf l r -> Set)
  (Q : forall r : term, sne l r -> Set) := snf_rect l P Q.

Definition snf_ind l
  (P : forall r : term, snf l r -> Prop)
  (Q : forall r : term, sne l r -> Prop) := snf_rect l P Q.

Definition sne_rec l
  (P : forall r : term, snf l r -> Set)
  (Q : forall r : term, sne l r -> Set) := sne_rect l P Q.

Definition sne_ind l
  (P : forall r : term, snf l r -> Prop)
  (Q : forall r : term, sne l r -> Prop) := sne_rect l P Q.

(* A&Y: add as many ps as you added new constructors for snf and sne in total *)
Definition snf_sne_rect l P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 :=
  pair (snf_rect l P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) (sne_rect l P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12).

Lemma sne_whne l : forall (t : term), sne l t -> whne (l := l) t.
Proof.
apply sne_rect with (P := fun _ _ => True); intros; subst; constructor; assumption.
Qed.

Lemma snf_red l : forall t u, [ t ⇒* u ]< l > -> snf l u -> snf l t.
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
+ eapply snf_tNat; transitivity u; eassumption.
+ eapply snf_tZero.
  transitivity u; eassumption.
+ eapply snf_tSucc.
  - transitivity u; eassumption.
  - assumption.
+ eapply snf_tEmpty; transitivity u; eassumption.
+ eapply snf_sne.
  - transitivity u; eassumption.
  - eassumption.
Qed.

Inductive isSNType l : term -> Type :=
  | UnivType {s} : isSNType l (tSort s)
  | ProdType {A B} : snf l A -> snf l B -> isSNType l (tProd A B)
  | NeType {A}  : sne l A -> isSNType l A.

Inductive isSNFun l : term -> Type :=
  | LamFun {A t} : snf l A -> snf l t -> isSNFun l (tLambda A t)
  | NeFun  {f} : sne l f -> isSNFun l f.

Lemma isSNType_snf l t : isSNType l t -> snf l t.
Proof.
destruct 1.
+ eapply snf_tSort; reflexivity.
+ eapply snf_tProd; first[reflexivity|assumption].
+ eapply snf_sne; first[reflexivity|assumption].
Qed.

Lemma isSNType_whnf l t : isSNType l t -> whnf (l := l) t.
Proof.
destruct 1; constructor.
apply sne_whne; assumption.
Qed.

Lemma isSNFun_snf l t : isSNFun l t -> snf l t.
Proof.
destruct 1.
+ eapply snf_tLambda; first[reflexivity|assumption].
+ eapply snf_sne; first[reflexivity|assumption].
Qed.

Lemma isSNFun_whnf l t : isSNFun l t -> whnf (l := l) t.
Proof.
destruct 1; constructor.
apply sne_whne; assumption.
Qed.

Lemma isSNType_isType l t : isSNType l t -> isType (l := l) t.
Proof.
destruct 1; constructor; now apply sne_whne.
Qed.

Lemma isSNFun_isFun l t : isSNFun l t -> isFun (l := l) t.
Proof.
destruct 1; constructor; now apply sne_whne.
Qed.

Section RenSnf.

  Lemma snf_sne_ren l :
    prod (forall t, snf l t -> forall ρ, snf l (t⟨ρ⟩)) (forall t, sne l t -> forall ρ, sne l (t⟨ρ⟩)).
  Proof.
  apply snf_sne_rect.
  + intros r s Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSort; eassumption.
  + intros r A B Hr HA IHA HB IHB ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tProd; eauto.
  + intros r A t Hr HA IHA Ht IHt ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tLambda; eauto.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tNat; eassumption.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tZero; eauto.
  + intros r t Hr Ht IHt ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSucc; eauto.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tEmpty; eassumption.
  + intros r n Hr Hn IHn ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_sne; eauto.
  + intros r v -> ρ; econstructor; reflexivity.
  + intros r n t -> Hn IHn Ht IHt ρ.
    cbn; eapply sne_tApp; eauto.
  + intros r P hz hs n -> HP IHP Hhz IHhz Hhs IHhs Hn IHn ρ; cbn.
    eapply sne_tNatElim; eauto.
  + intros. subst. cbn.
    eapply sne_tEmptyElim; eauto.
  Qed.

  Lemma sne_ren l ρ t : sne l t -> sne l (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

  Lemma snf_ren l ρ t : snf l t -> snf l (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

End RenSnf.

Lemma isSNType_ren l ρ t : isSNType l t -> isSNType l (t⟨ρ⟩).
Proof.
destruct 1; cbn; constructor; first [apply sne_ren|apply snf_ren]; assumption.
Qed.

Lemma isSNFun_ren l ρ t : isSNFun l t -> isSNFun l (t⟨ρ⟩).
Proof.
destruct 1; cbn; constructor; first [apply sne_ren|apply snf_ren]; assumption.
Qed.
 *)

Inductive DTypeWhnf (l : wfLCon) (A : term) : Type :=
| Typesnf (B : term) (red : [ A ⇒* B ]< l >) (typeB : isType B) :
  DTypeWhnf l A
| digammaTypeNf {n} {ne : not_in_LCon (pi1 l) n}
    (leftHyp : DTypeWhnf (l ,,l (ne, true)) A)
    (rightHyp : DTypeWhnf (l ,,l (ne, false)) A) :
  DTypeWhnf l A.

Inductive DTermWhnf (l : wfLCon) (t : term) : Type :=
| Termsnf (u : term) (red : [ t ⇒* u ]< l >) (whnfu : whnf u) :
  DTermWhnf l t
| digammaTermNf {n} {ne : not_in_LCon (pi1 l) n}
    (leftHyp : DTermWhnf (l ,,l (ne, true)) t)
    (rightHyp : DTermWhnf (l ,,l (ne, false)) t) :
  DTermWhnf l t.

Lemma DTermWhnf_Ltrans {l l' t} (f : l' ≤ε l) : DTermWhnf l t -> DTermWhnf l' t.
Proof.
  intro Hyp.
  revert l' f.
  induction Hyp ; intros.
  - eapply Termsnf ; try eassumption.
    now eapply redalg_Ltrans.
  - case (decidInLCon l' n) as [ [inl' | inl'] | notinl'].
    + eapply IHHyp1.
      now eapply LCon_le_in_LCon.
    + eapply IHHyp2.
      now eapply LCon_le_in_LCon.
    + eapply (@digammaTermNf _ _ _ notinl' ).
      * eapply IHHyp1.
        now apply LCon_le_up.
      * eapply IHHyp2.
        now apply LCon_le_up.
Qed.

(*Lemma DTermWhnf_BackLtrans {l n b} {ne :  not_in_LCon (pi1 l) n} {t u} :
  [ t ⇒* u ]< l > -> DTermWhnf (l ,,l (ne , b)) t -> DTermWhnf l t.
Proof.
  intros red WH.
  revert red.
  remember (l ,,l (ne,b)).
  induction WH ; subst.
  - *)

  
Module WeakValuesData.

#[export] Instance TypeWhne {ta} : Notations.TypeNe ta := fun l Γ A => whne A.
#[export] Instance TypeWhnf {ta} : Notations.TypeNf ta := 
  fun l Γ A => DTypeWhnf l A. (*∑ B, [ A ⇒* B ]< l > × isType l B.*)
#[export] Instance TermWhne {ta} : Notations.TermNe ta := fun l Γ A t => whne t.
#[export] Instance TermWhnf {ta} : Notations.TermNf ta :=
  fun l Γ A t => DTermWhnf l t. (* ∑ u, [ t ⇒* u ]< l > × whnf l u.*)

End WeakValuesData.

Module WeakValuesProperties.

Export WeakValuesData.

Section Properties.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta} `{!RedTypeProperties} `{!RedTermProperties}.

  #[export] Instance TypeWhneProperties : TypeNeProperties.
  Proof.
  split.
  + intros; now apply Weakening.whne_ren.
  + intros l Γ A HA.
    unshelve eapply Typesnf.
    * exact A.
    * econstructor.
    * now apply NormalForms.NeType.
  + intros; assumption.
  + intros; assumption.
  + intros * f Hyp.
    induction  Hyp ; try now econstructor.
  Qed.

  #[export] Instance TypeWhnfProperties : TypeNfProperties.
  Proof.
  split.
  - intros l Γ Δ A ρ _ BHyp.
    induction BHyp.
    + unshelve eapply Typesnf. 
      * exact (B⟨ρ⟩).
      * now apply credalg_wk.
      * now apply Weakening.isType_ren.
    + now eapply digammaTypeNf.
  - intros l Γ A B ? CHyp.
    induction CHyp as [ ? B C | ? ? n ne ].
    + unshelve eapply Typesnf.
      * exact C.
      * transitivity B ; [eapply redty_red| ]; eassumption.
      * assumption.
    + eapply digammaTypeNf.
      * eapply IHCHyp1.
        eapply redty_Ltrans ; try eassumption.
        -- apply LCon_le_step.
           now apply wfLCon_le_id.
      * eapply IHCHyp2.
        eapply redty_Ltrans ; try eassumption.
        -- apply LCon_le_step.
           now apply wfLCon_le_id.
  - intros. unshelve eapply Typesnf.
    + exact (tSort set).
    + reflexivity.
    + constructor.
  - intros; eapply Typesnf ; [reflexivity|constructor].
  - intros; eapply Typesnf; [reflexivity|constructor].
  - intros; eapply Typesnf; [reflexivity|constructor].
  - intros; eapply Typesnf; [reflexivity|constructor].
  - intros * f Hyp ; revert l' f.
    induction Hyp ; intros.
    + eapply Typesnf.
      * now eapply redalg_Ltrans.
      * inversion typeB ; subst ; try now econstructor.
    + case (decidInLCon l' n).
      * intros [ inl' | inl'].
        -- eapply IHHyp1.
           now eapply LCon_le_in_LCon.
        -- eapply IHHyp2.
           now eapply LCon_le_in_LCon.
      * intro notinl'.
        unshelve eapply digammaTypeNf ; [ exact n | exact notinl' | ..].
        -- eapply IHHyp1.
           now eapply LCon_le_up.
        -- eapply IHHyp2.
           now eapply LCon_le_up.
  Qed.

  #[export] Instance TermWhneProperties : TermNeProperties.
  Proof.
  split.
  + intros; apply Weakening.whne_ren.
    destruct ρ ; clear H1.
    now induction well_wk. 
  + intros; eapply Termsnf; [reflexivity|now constructor].
  + intros; assumption.
  + intros; assumption.
  + constructor.
  + constructor; assumption.
  + intros; constructor; assumption.
  + intros; constructor; assumption.
  + intros; constructor; assumption.
  + intros; constructor; assumption.
  + intros * f Hyp.
    induction Hyp ; try now econstructor.
  + intros. clear H2.
    induction H1 ; try now econstructor.
  Qed.

  #[export] Instance TermWhnfProperties : TermNfProperties.
  Proof.
  split.
  - intros l Γ Δ t A ρ _ Hyp.
    induction Hyp.
    + eapply Termsnf.
      * now apply credalg_wk.
      * now apply whnf_ren.
    + now eapply digammaTermNf.
  - intros; assumption.
  - intros l Γ t u A ? Hyp.
    induction Hyp as [ ? u v | ? ? n ne ].
    + eapply Termsnf ; try eassumption.
      transitivity u ; [eapply redtm_red| ]; eassumption.
    + eapply digammaTermNf.
      * apply IHHyp1.
        eapply redtm_Ltrans ; try eassumption.
        eapply LCon_le_step ; now apply wfLCon_le_id.
      * apply IHHyp2.
        eapply redtm_Ltrans ; try eassumption.
        eapply LCon_le_step ; now apply wfLCon_le_id.
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros; eapply Termsnf ; [reflexivity|constructor].
(*  + intros; eexists; split; [reflexivity| ].
    apply whnf_tAlpha.
    now constructor.*)
    - intros; eapply Termsnf ; [reflexivity|constructor].
    - intros* f Hyp.
      now eapply DTermWhnf_Ltrans.
    - intros * HL HR.
      now eapply digammaTermNf.
  Qed.

End Properties.

End WeakValuesProperties.

(* Module StrongValuesProperties.

Export StrongValuesData.

Section Properties.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta} `{!RedTypeProperties} `{!RedTermProperties}.

  #[export] Instance TypeSneProperties : TypeNeProperties.
  Proof.
  split.
  + intros; now apply sne_ren.
  + intros; eapply snf_sne; [reflexivity|assumption].
  + intros; now apply sne_whne.
  + intros; assumption.
  Qed.

  #[export] Instance TypeSnfProperties : TypeNfProperties.
  Proof.
  split.
  all: try (now econstructor; first [reflexivity|eassumption]).
  + intros; now apply snf_ren.
  + intros; eapply snf_red; [eapply redty_red|]; eassumption.
  Qed.

  #[export] Instance TermSneProperties : TermNeProperties.
  Proof.
  split.
  all: try (intros; now econstructor).
  + intros; now apply sne_ren.
  + intros; eapply snf_sne; [reflexivity|assumption].
  + intros; now apply sne_whne.
  + intros; assumption.
  Qed.

  #[export] Instance TermSnfProperties : TermNfProperties.
  Proof.
  split.
  all: try (now econstructor; first [reflexivity|eassumption]).
  + intros; now apply snf_ren.
  + intros; assumption.
  + intros; eapply snf_red; [eapply redtm_red|]; eassumption.
  Qed.

End Properties.

End StrongValuesProperties.*)
