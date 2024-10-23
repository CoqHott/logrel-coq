From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms UntypedReduction.

Unset Elimination Schemes.

Inductive snf {l : wfLCon} (r : term) : Type :=
  | snf_tSort {s} : [ r ⤳* tSort s ]< l > -> snf r
  | snf_tProd {A B} : [ r ⤳* tProd A B ]< l > -> snf A -> snf B -> snf r
  | snf_tLambda {A t} : [ r ⤳* tLambda A t ]< l > -> snf A -> snf t -> snf r
  | snf_tNat : [ r ⤳* tNat ]< l > -> snf r
  | snf_tZero : [ r ⤳* tZero ]< l > -> snf r
  | snf_tSucc {n} : [ r ⤳* tSucc n ]< l > -> snf n -> snf r
  | snf_tEmpty : [ r ⤳* tEmpty ]< l > -> snf r
  | snf_tBool : [ r ⤳* tBool ]< l > -> snf r
  | snf_tTrue : [ r ⤳* tTrue ]< l > -> snf r
  | snf_tFalse : [ r ⤳* tFalse ]< l > -> snf r
  | snf_tSig {A B} : [r ⤳* tSig A B]< l > -> snf A -> snf B -> snf r
  | snf_tPair {A B a b} : [r ⤳* tPair A B a b]< l > -> snf A -> snf B -> snf a -> snf b -> snf r
  | snf_sne {n} : [ r ⤳* n ]< l > -> sne n -> snf r
with sne {l : wfLCon} (r : term) : Type :=
  | sne_tRel {v} : r = tRel v -> sne r
  | sne_tApp {n t} : r = tApp n t -> sne n -> snf t -> sne r
  | sne_tNatElim {P hz hs n} : r = tNatElim P hz hs n -> snf P -> snf hz -> snf hs -> sne n -> sne r
  | sne_tBoolElim {P ht hf b} : r = tBoolElim P ht hf b -> snf P -> snf ht -> snf hf -> sne b -> sne r
  | sne_tEmptyElim {P e} : r = tEmptyElim P e -> snf P -> sne e -> sne r
  | sne_tFst {p} : r = tFst p -> sne p -> sne r
  | sne_tSnd {p} : r = tSnd p -> sne p -> sne r
  | sne_tAlpha {n} : r = tAlpha n -> sne n -> sne r
.

Set Elimination Schemes.

Scheme
  Induction for snf Sort Type with
  Induction for sne Sort Type.

Definition snf_rec l
  (P : forall r : term, snf r -> Set)
  (Q : forall r : term, sne r -> Set) := snf_rect l P Q.

Definition snf_ind l
  (P : forall r : term, snf r -> Prop)
  (Q : forall r : term, sne r -> Prop) := snf_rect l P Q.

Definition sne_rec l
  (P : forall r : term, snf r -> Set)
  (Q : forall r : term, sne r -> Set) := sne_rect l P Q.

Definition sne_ind l
  (P : forall r : term, snf r -> Prop)
  (Q : forall r : term, sne r -> Prop) := sne_rect l P Q.

(* A&Y: add as many ps as you added new constructors for snf and sne in total *)
Definition snf_sne_rect l P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 :=
  pair 
    (snf_rect l P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21)
    (sne_rect l P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21).

Lemma sne_whne {l} : forall (t : term), sne (l := l) t -> whne t.
Proof.
  apply sne_rect with (P := fun _ _ => True); intros; subst; try now constructor; assumption.
  change n with (nSucc 0 n).
  now constructor.
Qed.

Lemma snf_red {l} : forall t u, [ t ⤳* u ]< l > -> snf (l:= l) u -> snf (l := l) t.
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
+ eapply snf_tBool; transitivity u; eassumption.
+ eapply snf_tTrue; transitivity u; eassumption.
+ eapply snf_tFalse; transitivity u; eassumption.
+ eapply snf_tSig.
  1: transitivity u; eassumption.
  all: tea.
+ eapply snf_tPair.
  1: transitivity u; eassumption.
  all: tea.
+ eapply snf_sne.
  - transitivity u; eassumption.
  - eassumption.
Qed.

Section RenSnf.

  Lemma snf_sne_ren {l} :
    prod (forall t, snf (l := l) t -> forall ρ, @snf l (t⟨ρ⟩)) (forall t, @sne l t -> forall ρ, @sne l (t⟨ρ⟩)).
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
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tBool; eassumption.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tTrue; eassumption.
  + intros r Hr ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tFalse; eassumption.
  + intros r A B Hr ???? ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tSig; eauto.
  + intros r ???? Hr ???????? ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_tPair; eauto.
  + intros r n Hr Hn IHn ρ.
    apply credalg_wk with (ρ := ρ) in Hr.
    eapply snf_sne; eauto.
  + intros r v -> ρ; econstructor; reflexivity.
  + intros r n t -> Hn IHn Ht IHt ρ.
    cbn; eapply sne_tApp; eauto.
  + intros r P hz hs n -> HP IHP Hhz IHhz Hhs IHhs Hn IHn ρ; cbn.
    eapply sne_tNatElim; eauto.
  + intros r P hz hs n -> HP IHP Hhz IHhz Hhs IHhs Hn IHn ρ; cbn.
    eapply sne_tBoolElim; eauto.
  + intros. subst. cbn.
    eapply sne_tEmptyElim; eauto.
  + intros r ? -> ???; cbn; eapply sne_tFst; eauto.
  + intros r ? -> ???; cbn; eapply sne_tSnd; eauto.
  + intros r t Hr Ht IHt ρ.
    eapply sne_tAlpha with (t⟨ρ⟩) ; eauto.
    now subst.
  Qed.

  Lemma sne_ren {l} ρ t : @sne l t -> @sne l (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

  Lemma snf_ren {l} ρ t : @snf l t -> @snf l (t⟨ρ⟩).
  Proof.
  intros; apply snf_sne_ren; assumption.
  Qed.

End RenSnf.
