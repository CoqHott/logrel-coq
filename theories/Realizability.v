From Coq Require Import ssreflect.
From Equations Require Import Equations.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import BasicAst Notations Utils Context Weakening NormalForms.

From Ltac2 Require Import Ltac2 Printf.
(* From Ltac2 Require Control Constr List Ltac1 Std Notations. *)

Unset Automatic Proposition Inductives.

Ltac2 depelim (i : ident) : unit := ltac1:(i |- depelim i) (Ltac1.of_ident i).
Ltac2 Notation "depelim" i(ident) := depelim i.

Ltac2 noconf (i : ident) : unit := ltac1:(i |- noconf i) (Ltac1.of_ident i).
Ltac2 Notation "noconf" i(ident) := noconf i.

Ltac2 eassumption0 := fun () => ltac1:(eassumption).
Ltac2 Notation "eassumption" := eassumption0 ().

Ltac2 Notation "solve" c(thunk(self)) := c (); Control.enter (fun () => fail).
Ltac2 Notation c1(thunk(self)) "+" c2(thunk(tactic)) := Control.plus c1 (fun _ => c2 ()).
Ltac2 Notation c1(thunk(self)) "||" c2(thunk(tactic)) := Notations.orelse c1 (fun _ => c2 ()).
Ltac2 Notation "[>" tacs(list0(thunk(self),"|")) "]" := Control.dispatch tacs.

Ltac2 Notation "only" startgoal(tactic) endgoal(opt(seq("-", tactic))) ":" tac(thunk(tactic)) :=
  Control.focus startgoal (Option.default startgoal endgoal) tac.

Ltac2 Notation "exfalso" := ltac1:(exfalso).

Set Equations With UIP.

Derive NoConfusion EqDec for sort term.
Derive NoConfusion for prod.

Require Import Relations RelationClasses.

Class HProp A := hProp : forall (a b : A), a = b.

Instance HProp_EqDec A (isHProp : HProp A) : EqDec A.
Proof.
  intros a b.
  left.
  apply isHProp.
Defined.

Instance option_EqDec {A} : EqDec A -> EqDec (option A).
Proof.
  intros eqdecA.
  intros a b.
  depelim a.
  - depelim b.
    + assert (_) by (eapply (eqdecA a a0)).
      depelim X.
      * left. now f_equal.
      * right. intros u. noconf u. apply n. reflexivity.
    + right. intros u. noconf u.
  - depelim b.
    + right. intros u. noconf u.
    + left. reflexivity.
Defined.

Fixpoint reduce (t : term) : option term :=
match t with
| tApp s a => match s with
  | tLambda _ b => Some (b [a..])
  | _ => match reduce s with
    | Some f => Some (tApp f a)
    | None => None
    end
  end
| tNatElim P hz hs s => match s with
  | tZero => Some hz
  | tSucc n => Some (tApp (tApp hs n) (tNatElim P hz hs n))
  | _ => match reduce s with
    | Some n => Some (tNatElim P hz hs n)
    | None => None
    end
  end
| _ => None
end.

Notation "[ t ~> t' ]" := (reduce t = Some t').
Notation "[ t ~x ]" := (reduce t = None).

(* Keep in sync with OneRedTermDecl! *)

Lemma red_nored {t u} : [ t ~> u ] -> [ t ~x ] -> False.
Proof.
  intros H1 H2.
  rewrite H2 in H1.
  discriminate H1.
Qed.

Reserved Notation "[ t ~* u ]".

Inductive reduce_n {t} : term -> Prop :=
  | terminates_later {u v} : [ t ~> u ] -> [ u ~* v ] -> [ t ~* v ]
  | terminates_now : [ t ~x ] -> [ t ~* t ]
  where "[ t ~* u ]" := (@reduce_n t u).

Inductive WhnfFuel {t} : Prop := {
  afterReduce : forall {u}, [ t ~> u ] -> @WhnfFuel u
}.

Arguments WhnfFuel : clear implicits.

Scheme WhnfFuel_ind_dep := Induction for WhnfFuel Sort Prop.

Lemma terminates_to_fuel {t u} (H : [ t ~* u ]) : WhnfFuel t.
Proof.
  induction H; constructor.
  - intros y red.
    rewrite H in red.
    now injection red as ->.
  - intros y red.
    exfalso.
    now eapply red_nored.
Defined.

Definition inspect {A} (a : A) : ∑ b, a = b := (a ; eq_refl).

Fixpoint whnf t (fuel : WhnfFuel t) {struct fuel} : term :=
  match inspect (reduce t) with
  | (Some t ; eq) => whnf t (fuel.(afterReduce) eq)
  | (None ; _) => t
  end.

Lemma whnf_irr {t fuel1 fuel2} : whnf t fuel1 = whnf t fuel2.
Proof.
  induction fuel1 using WhnfFuel_ind_dep.
  destruct fuel2.
  cbn. remember eq_refl. remember (reduce t).
  destruct o.
  - eapply H.
  - reflexivity.
Defined.

Lemma whnf_step {t u fuel1 fuel2} : [ t ~> u ] -> whnf t fuel1 = whnf u fuel2.
Proof.
  intros H.
  destruct fuel1.
  cbn. remember eq_refl. remember (reduce t) as o.
  destruct o.
  - injection H as <-.
    apply whnf_irr.
  - discriminate H.
Defined.

Lemma whnf_stop {t fuel} : [ t ~x ] -> whnf t fuel = t.
Proof.
  intros H.
  destruct fuel.
  cbn. remember eq_refl. remember (reduce t) as o.
  destruct o.
  - discriminate H.
  - reflexivity.
Defined.

(* Test *)
Definition test_term :=
  tApp
    (tLambda (tProd tNat tNat) (tApp (tRel 0) (tApp (tRel 0) (tZero))))
    (tLambda tNat (tSucc (tSucc (tRel 0)))).

Lemma whnf_valid t fuel {u} : whnf t fuel = u -> [ t ~* u ].
Proof.
  intros <-.
  induction fuel using WhnfFuel_ind_dep.
  destruct (reduce t) eqn: red in |-.
  - erewrite whnf_step > [|eassumption].
    (econstructor) > [eassumption|].
    apply (H _ red).
  - now (rewrite whnf_stop > [econstructor|]).
Defined.

Lemma whnf_det t u v :
    [ t ~* u ]
 -> [ t ~* v ]
 -> u = v.
Proof.
  induction 1.
  all: intros H2.
  - destruct H2.
    + rewrite H in H1. injection H1 as <-.
      eauto.
    + exfalso. now eapply red_nored.
  - destruct H2.
    + exfalso. now eapply red_nored.
    + reflexivity.
Defined.

Ltac2 whnf_det0 () := Control.enter (fun () =>
  match! goal with
    [ h1 : [ ?_t ~* ?u ], h2 : [ ?_t ~* ?v ] |- _] =>
      (let h1 := Control.hyp h1 in
      let h2 := Control.hyp h2 in
      let eq := Fresh.in_goal @eq in
      assert ($eq : $u = $v) by apply (whnf_det _ _ _ $h1 $h2);
      noconf $eq); clear $h2
    end).

Ltac2 Notation "whnf_det" := whnf_det0 ().

(* Nat realizability *)
Inductive NatREL t u : Prop :=
  | realZero : [ t ~* tZero ] -> [ u ~* tZero ] -> NatREL t u
  | realSucc {t' u'} : [ t ~* tSucc t' ] -> [ u ~* tSucc u' ] -> NatREL t' u' -> NatREL t u.

Require Import RelationClasses Morphisms.

Lemma NatREL_to_whnf {t} : Proper NatREL t -> exists u, [ t ~* u ].
Proof.
  intros H.
  now destruct H.
Defined.

Program Definition FunREL (RA : relation term) (RB : forall {a a'}, RA a a' -> relation term)
  f g : Prop := (forall a a' (raa' : RA a a'), RB raa' (tApp f a) (tApp g a')).

Inductive TypeREL_Packed T T' : forall R, Prop :=
  | realNat : [ T ~* tNat ] -> [ T' ~* tNat ] -> TypeREL_Packed T T' NatREL
  | realProd {A A' B B' RA RB} :
       [ T ~* tProd A B ]
    -> [ T' ~* tProd A' B' ]
    -> TypeREL_Packed A A' RA
    -> (forall a a' (Raa' : RA a a'), TypeREL_Packed B[a..] B'[a'..] (RB a a' Raa'))
    -> TypeREL_Packed T T' (FunREL RA RB).

Ltac2 rec terminate0 () := Control.enter (fun () =>
  try (eassumption
  || (eapply terminates_now > [reflexivity])
  || (eapply terminates_later > [reflexivity|terminate0 ()]))).

Ltac2 Notation "terminate" := terminate0 ().

Ltac2 rec real0 () := Control.enter (fun () =>
  hnf; try (lazy_match! goal with
    | [ |- NatREL ?t _ ] =>
      eassumption ||
      let a := Fresh.in_goal @term in
      let b := Fresh.in_goal @term2 in
      pose (ltac2:(terminate) : [ $t ~* _ ]) as $a;
      (econstructor) > [eassumption|(eassumption || terminate)|..];
      clear $a $b;
      fail || real0 ()
  end)).

Ltac2 Notation "real" := real0 ().


(* Tests *)
Definition succ_fun := tLambda tNat (tSucc (tRel 0)).

Lemma succ_fun_real : Proper (FunREL NatREL (fun _ _ _ => NatREL)) succ_fun.
Proof.
  intros ???; real.
Defined.

Definition compose_fun := tLambda (tProd tNat tNat) (tLambda (tProd tNat tNat) (tLambda tNat (tApp (tRel 1) (tApp (tRel 2) (tRel 0))))).


(* Irrelevance *)
Theorem TypeREL_det {T T' T'' RA RB} :
    TypeREL_Packed T T' RA
 -> TypeREL_Packed T T'' RB
 -> forall a a', RA a a' <-> RB a a'.
Proof.
  intros HA. revert HA T'' RB.
  induction 1.
  all: intros ? ? HB a a'.
  all: split.
  all: intros raa'.
  all: destruct HB.
  all: whnf_det.
  - eassumption.
  - eassumption.
  - intros b b' rbb'.
    unshelve (eapply H2 > [eauto|]) > [|now eapply IHHA |];
    apply raa'.
  - intros b b' rbb'.
    eapply (IHHA _ RA0) in rbb' as r'bb' > [|apply HB].
    specialize (raa' _ _ r'bb').
    eapply H2 > [|exact raa'].
    eauto.
Defined.


Definition TypeREL T T' := exists R, TypeREL_Packed T T' R.

Inductive TypeREL_Packed_Fuel {T T'} : Prop := {
  afterWhnfToProdDom : forall A A' B B',
       [ T ~* tProd A B ]
    -> [ T' ~* tProd A' B' ]
    -> TypeREL A A'
    -> (forall RA a a', RA a a' -> TypeREL_Packed A A' RA -> TypeREL B[a..] B'[a'..])
    -> @TypeREL_Packed_Fuel A A' ;
  afterWhnfToProdCod : forall A A' B B',
       [ T ~* tProd A B ]
    -> [ T' ~* tProd A' B' ]
    -> TypeREL A A'
    -> (forall RA a a', RA a a' -> TypeREL_Packed A A' RA -> TypeREL B[a..] B'[a'..])
    -> forall RA a a',  RA a a' -> TypeREL_Packed A A' RA ->
         @TypeREL_Packed_Fuel B[a..] B'[a'..] ;
}.

Arguments TypeREL_Packed_Fuel : clear implicits.


Theorem TypeREL_to_Fuel {T T'} (RTT' : TypeREL T T') : TypeREL_Packed_Fuel T T'.
Proof.
  destruct RTT' as (? & RTT').
  induction RTT'.
  all: (econstructor) > [|];
    intros **;
    whnf_det; whnf_det.
  - eassumption.
  - apply H2.
    eapply TypeREL_det > [..|eassumption]; eassumption.
Defined.

Theorem TypeREL_to_Whnf {T T'} (RTT' : TypeREL T T') : ∑ Tred (_ : [ T ~* Tred ]) T'red, [ T' ~* T'red ].
Proof.
  refine '((whnf T ?[fuel1] ; whnf_valid T ?fuel1 eq_refl
          ; whnf T' ?[fuel2] ; whnf_valid T' ?fuel2 eq_refl)).
  all:
    destruct RTT' as (? & []);
    now eapply terminates_to_fuel.
Defined.

Definition TypeREL_el {T T'} (RTT' : TypeREL T T') : ∑ R, TypeREL_Packed T T' R.
Proof.
  apply TypeREL_to_Fuel in RTT' as fuel.
  induction fuel using TypeREL_Packed_Fuel_rect.
  apply TypeREL_to_Whnf in RTT' as whnfs.
  destruct whnfs as (Tred & Treds & T'red & T'reds).
  destruct Tred; try (solve (exfalso; destruct RTT' as (? & []); whnf_det; whnf_det)).
  all: destruct T'red; try (solve (exfalso; destruct RTT' as (? & []); whnf_det; whnf_det)).
  - assert (TypeREL Tred1 T'red1).
    { destruct RTT' as (? & []); whnf_det; whnf_det; now econstructor. }
    assert (forall RA a a', RA a a' -> TypeREL_Packed Tred1 T'red1 RA -> TypeREL Tred2[a..] T'red2[a'..]).
    { intros ??? R P.
      destruct RTT' as (? & []); whnf_det; whnf_det; econstructor; unshelve (apply H3).
      now eapply TypeREL_det. }
    assert (X' : _) by (now eapply X).
    destruct X' as (RDom & realDom).
    assert (X0' : forall a a', RDom a a' -> ∑ R, TypeREL_Packed Tred2[a..] T'red2[a'..] R).
    { intros ???. now eapply X0. }
    econstructor.
    eapply realProd > [eassumption|eassumption| ..].
    eassumption.
    intros a a' Raa'.
    exact ((X0' a a' Raa') .π2).
  - econstructor.
    now apply realNat.
Defined.

Lemma TypeREL_Packed_Symmetric {T T' R} :
    TypeREL_Packed T T' R
 -> forall {R'}, TypeREL_Packed T' T R' -> forall a a', R a a' <-> R' a' a.
Proof.
  induction 1; destruct 1; whnf_det; whnf_det.
  - intros a a'.
    split; induction 1; now econstructor.
  - intros a a'.
    split; intros Raa';
    intros ?? raa'.
    + eapply IHTypeREL_Packed in raa' as ra'a > [|eauto].
      unshelve (eapply H3 > [eauto|]); eauto.
    + unshelve (eapply H3 > [|eapply Raa']) > [eapply IHTypeREL_Packed|]; eauto.
Defined.

Lemma TypeREL_Symmetric {T T'} :
    TypeREL T T'
 -> TypeREL T' T.
Proof.
  destruct 1 as (? & RTT').
  induction RTT'.
  - econstructor.
    + now econstructor.
  - destruct IHRTT' as (RA' & IHRA').
    eassert (forall a a' (Raa' : RA a a'), _).
      { intros ???.
        eapply TypeREL_el.
        now eapply H2. }
    econstructor.
    (econstructor) > [eassumption|eassumption|eassumption|..].
    intros ?? RA'aa'.
    refine '((X _ _ _) .π2).
    now eapply TypeREL_Packed_Symmetric.
Defined.

Lemma TypeREL_det_right {T T' T'' RA RB} :
    TypeREL_Packed T T'' RA
 -> TypeREL_Packed T' T'' RB
 -> forall a a', RA a a' <-> RB a a'.
Proof.
  intros H1 H2.
  eassert (H1sym : TypeREL T'' T). {(eapply TypeREL_Symmetric). now econstructor. }
  eassert (H2sym : TypeREL T'' T'). {(eapply TypeREL_Symmetric). now econstructor. }
  destruct H1sym as (? & H1sym).
  destruct H2sym as (? & H2sym).
  intros a a'.
  rewrite (TypeREL_Packed_Symmetric H1 H1sym).
  rewrite (TypeREL_Packed_Symmetric H2 H2sym).
  now eapply TypeREL_det.
Defined.

Lemma TypeREL_Packed_Conduché {A B C RAB RBC RAC} :
    TypeREL_Packed A B RAB
 -> TypeREL_Packed B C RBC
 -> TypeREL_Packed A C RAC
 -> (forall a b c, RAB a b -> RBC b c -> RAC a c)
 -> forall a c, RAC a c -> RAB a a × RBC a c.
Proof.
  intros HAB HBC HAC trans.
  intros a c rac.
  split.
  - assert (RAB a c) by (now eapply TypeREL_det).
    assert (TypeREL B A) as (RBA & HBA) by (eapply TypeREL_Symmetric; now econstructor).
    assert (RBA c a) by (now eapply TypeREL_Packed_Symmetric).
    assert (RBC c a) by (now eapply TypeREL_det).
    assert (RAC a a) by (now eapply trans).
    now eapply TypeREL_det.
  - now eapply TypeREL_det_right.
Defined.

Lemma TypeREL_Packed_Transitive {T T' T'' R R' R''} :
    TypeREL_Packed T T' R
 -> TypeREL_Packed T' T'' R'
 -> TypeREL_Packed T T'' R''
 -> forall a a' a'', R a a' -> R' a' a'' -> R'' a a''.
Proof.
  induction 1 in T'', R', R''; destruct 1; whnf_det; destruct 1; whnf_det; whnf_det.
  - intros a a' a''.
    induction 1 in a''; inversion 1; whnf_det; now econstructor.
  - intros f f' f'' rf rf'.
    intros a a'' raa''.
    assert (RA a a × RA0 a a'') as (RAaa & RA0aa'').
    {eapply TypeREL_Packed_Conduché > [| | | eapply IHTypeREL_Packed |]; eauto. }
    eapply H3 > [| | apply (rf _ _ RAaa) | apply (rf' _ _ RA0aa'') ]; eauto.
Defined.

Lemma TypeREL_Transitive {A B C} :
    TypeREL A B
 -> TypeREL B C
 -> TypeREL A C.
Proof.
  destruct 1 as (RAB & HAB).
  induction HAB in C; destruct 1 as (RBC & []); whnf_det.
  - econstructor; now apply realNat.
  - assert (HAA'0 : TypeREL A A'0). {apply IHHAB; now econstructor. }
    apply TypeREL_el in HAA'0 as (RAA'0 & HAA'0).
    assert (HBB'0 : forall a a', RAA'0 a a' -> ∑ R, TypeREL_Packed B[a..] B'0[a'..] R).
    { intros a a' RAA'0aa'.
      eapply (TypeREL_Packed_Conduché (RAB := RA) (RBC := RA0)) in RAA'0aa' as (RAaa & RA0aa') > [.. | eapply TypeREL_Packed_Transitive] > [| eauto ..].
      eapply TypeREL_el.
      eapply (H2 _ _ RAaa).
      econstructor.
      now (unshelve (eapply H6)). }
    assert (∑ R, forall a a' (raa' : RAA'0 a a'), TypeREL_Packed B[a..] B'0[a'..] (R a a' raa'))
    as (RBB'0' & HBB'0').
    { econstructor. intros a a' RAA'0aa'.
      unshelve (eapply projT2).
      eapply TypeREL_el.
      eapply (TypeREL_Packed_Conduché (RAB := RA) (RBC := RA0)) in RAA'0aa' as u > [.. | eapply TypeREL_Packed_Transitive] > [| eauto ..].
      eapply (H2 _ _ (fst u)).
      econstructor.
      now (unshelve (eapply H6)). }
    econstructor; now eapply realProd.
Defined.



Program Definition ExtREL (RΓ : REL (nat -> term)) (RA : RELe RΓ) : REL (nat -> term) := {|
  REL_rel ρ ρ' := exists (Rupρ : RΓ (↑ >> ρ) (↑ >> ρ')), RA.(RELe_REL) Rupρ (ρ 0) (ρ' 0)
|}.
Final Obligation of ExtREL.
Proof.
  econstructor.
  - intros ???.
    destruct H.
    econstructor.
    symmetry.
    do 2 (eapply RELe_Irrel_co).
    eassumption.
    Unshelve.
    symmetry; eassumption.
    etransitivity > [symmetry|]; eassumption.
  - intros ?????.
    destruct H.
    destruct H0.
    econstructor.
    etransitivity.
    eapply RELe_Irrel_co.
    eapply RELe_Irrel_co.
    eassumption.
    eapply RELe_Irrel_co.
    eapply RELe_Irrel_co.
    eassumption.
    Unshelve.
    now etransitivity.
    now symmetry.
    now (symmetry; etransitivity).
Defined.

Inductive ContextREL_Packed : context -> context -> forall R, Prop :=
  | nil_real : ContextREL_Packed ε ε TrueREL
  | cons_real {Γ Γ' RΓ A B RA} : ContextREL_Packed Γ Γ' RΓ
    -> (forall ρ ρ' (Rρ : RΓ ρ ρ'), TypeREL_Packed A[ρ] B[ρ'] (RA.(RELe_REL) Rρ))
    -> ContextREL_Packed (Γ ,, A) (Γ' ,, B) (ExtREL RΓ RA)
.


(* Irrelevance lemmas *)

Theorem ContextREL_det {Γ Γ' RΓ RΓ'} :
    ContextREL_Packed Γ Γ' RΓ
 -> ContextREL_Packed Γ Γ' RΓ'
 -> forall ρ ρ', RΓ ρ ρ' <-> RΓ' ρ ρ'.
Proof.
  intros HA. revert HA RΓ'.
  induction 1.
  - intros ? HΓ' ρ ρ'.
    inversion HΓ'.
    split; constructor.
  - intros ? HΓ' ρ ρ'.
    inversion HΓ'.
    subst.
    split.
    + intros (? & ?).
      unshelve econstructor.
      now eapply IHHA.
      now eapply TypeREL_det.
    + intros (? & ?).
      unshelve econstructor.
      now eapply IHHA.
      eapply TypeREL_det.
      apply H.
      apply H6.
      eassumption.
Defined.

Inductive TypeREL_Packed_Fuel T T' R : Prop := {
  real : TypeREL_Packed T T' R ;
  realProdUnfold {A B A' B' RA RB} :
      [ T ~* tProd A B ]
   -> [ T' ~* tProd A' B' ]
   -> 
}.

Lemma extract_Rel {T T'} : (exists R, TypeREL_Packed T T' R) -> relation term.
Proof.
  

(** **** Context well-formation *)
Inductive WfContextDecl : context -> Type :=
  | connil : [ |- ε ]
  | concons {Γ A} : 
      [ |- Γ ] -> 
      [ Γ |- A ] -> 
      [ |-  Γ ,, A]
(** **** Type well-formation *)
with WfTypeDecl  : context -> term -> Type :=
  | wfTypeProd {Γ} {A B} : 
      [ Γ |- A ] -> 
      [Γ ,, A |- B ] -> 
      [ Γ |- tProd A B ]
  | wfTypeNat {Γ} : 
      [|- Γ] ->
      [Γ |- tNat]
(** **** Typing *)
with TypingDecl : context -> term -> term -> Type :=
  | wfVar {Γ} {n decl} :
      [   |- Γ ] ->
      in_ctx Γ n decl ->
      [ Γ |- tRel n : decl ]
  | wfTermLam {Γ} {A B t} :
      [ Γ |- A ] ->
      [ Γ ,, A |- t : B ] ->
      [ Γ |- tLambda A t : tProd A B]
  | wfTermApp {Γ} {f a A B} :
      [ Γ |- f : tProd A B ] ->
      [ Γ |- a : A ] ->
      [ Γ |- tApp f a : B[a..] ]
  | wfTermNat {Γ} :
      [|-Γ] ->
      [Γ |- tNat : U]
  | wfTermZero {Γ} :
      [|-Γ] ->
      [Γ |- tZero : tNat]
  | wfTermSucc {Γ n} :
      [Γ |- n : tNat] ->
      [Γ |- tSucc n : tNat]
  | wfTermNatElim {Γ P hz hs n} :
    [Γ ,, tNat |- P ] ->
    [Γ |- hz : P[tZero..]] ->
    [Γ |- hs : elimSuccHypTy P] ->
    [Γ |- n : tNat] ->
    [Γ |- tNatElim P hz hs n : P[n..]]
(** **** Conversion of types *)
with ConvTypeDecl : context -> term -> term  -> Type :=
  | TypePiCong {Γ} {A B C D} :
      [ Γ |- A] ->
      [ Γ |- A ≅ B] ->
      [ Γ ,, A |- C ≅ D] ->
      [ Γ |- tProd A C ≅ tProd B D]
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
(** **** Conversion of terms *)
with ConvTermDecl : context -> term -> term -> term -> Type :=
  | TermBRed {Γ} {a t A B} :
          [ Γ |- A ] ->
          [ Γ ,, A |- t : B ] ->
          [ Γ |- a : A ] ->
          [ Γ |- tApp (tLambda A t) a ≅ t[a..] : B[a..] ]
  | TermAppCong {Γ} {a b f g A B} :
      [ Γ |- f ≅ g : tProd A B ] ->
      [ Γ |- a ≅ b : A ] ->
      [ Γ |- tApp f a ≅ tApp g b : B[a..] ]
  | TermLambdaCong {Γ} {t u A A' A'' B} :
      [ Γ |- A ] ->
      [ Γ |- A ≅ A' ] ->
      [ Γ |- A ≅ A'' ] ->
      [ Γ,, A |- t ≅ u : B ] ->
      [ Γ |- tLambda A' t ≅ tLambda A'' u : tProd A B ]
  | TermFunEta {Γ} {f A B} :
      [ Γ |- f : tProd A B ] ->
      [ Γ |- tLambda A (eta_expand f) ≅ f : tProd A B ]
  | TermSuccCong {Γ} {n n'} :
      [Γ |- n ≅ n' : tNat] ->
      [Γ |- tSucc n ≅ tSucc n' : tNat]
  | TermNatElimCong {Γ P P' hz hz' hs hs' n n'} :
      [Γ ,, tNat |- P ≅ P'] ->
      [Γ |- hz ≅ hz' : P[tZero..]] ->
      [Γ |- hs ≅ hs' : elimSuccHypTy P] ->
      [Γ |- n ≅ n' : tNat] ->
      [Γ |- tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : P[n..]]
  | TermNatElimZero {Γ P hz hs} :
      [Γ ,, tNat |- P ] ->
      [Γ |- hz : P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy P] ->
      [Γ |- tNatElim P hz hs tZero ≅ hz : P[tZero..]]
  | TermNatElimSucc {Γ P hz hs n} :
      [Γ ,, tNat |- P ] ->
      [Γ |- hz : P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy P] ->
      [Γ |- n : tNat] ->
      [Γ |- tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]]
  | TermRefl {Γ} {t A} :
      [ Γ |- t : A ] -> 
      [ Γ |- t ≅ t : A ]
  | TermConv {Γ} {t t' A B} :
      [ Γ |- t ≅ t': A ] ->
      [ Γ |- A ≅ B ] ->
      [ Γ |- t ≅ t': B ]
  | TermSym {Γ} {t t' A} :
      [ Γ |- t ≅ t' : A ] ->
      [ Γ |- t' ≅ t : A ]
  | TermTrans {Γ} {t t' t'' A} :
      [ Γ |- t ≅ t' : A ] ->
      [ Γ |- t' ≅ t'' : A ] ->
      [ Γ |- t ≅ t'' : A ]

  where "[   |- Γ ]" := (WfContextDecl Γ)
  and   "[ Γ |- T ]" := (WfTypeDecl Γ T)
  and   "[ Γ |- t : T ]" := (TypingDecl Γ T t)
  and   "[ Γ |- A ≅ B ]" := (ConvTypeDecl Γ A B)
  and   "[ Γ |- t ≅ t' : T ]" := (ConvTermDecl Γ T t t').

Section InductionPrinciples.

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
  intros PCon PTy PTm PTyEq PTmEq **.
  ltac1:(pose proof (_WfDeclInduction PCon PTy PTm PTyEq PTmEq) as H).
  destruct H as [?[?[? []]]].
  all: try (assumption ; fail).
  repeat (split > [assumption|]); assumption.
Qed.

Definition WfDeclInductionConcl :=
  ltac:(
    let t := eval cbv delta [WfDeclInductionType] beta in WfDeclInductionType in
    let t' := remove_steps t in
    exact t').

Print WfDeclInductionConcl.

End InductionPrinciples.

Arguments WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq : rename.

Theorem interp : WfDeclInductionConcl
  (fun Γ => ∑ RΓ, ContextREL_Packed Γ Γ RΓ)
  (fun Γ A => ∑ RΓ, ContextREL_Packed Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), TypeREL_Packed A[ρ] A[ρ'] (RA.(RELe_REL) Rρ)))
  (fun Γ A t => ∑ RΓ, ContextREL_Packed Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), TypeREL_Packed A[ρ] A[ρ'] (RA.(RELe_REL) Rρ) × RA.(RELe_REL)Rρ t[ρ] t[ρ']))
  (fun Γ A B => ∑ RΓ, ContextREL_Packed Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), TypeREL_Packed A[ρ] B[ρ'] (RA.(RELe_REL) Rρ)))
  (fun Γ A t u => ∑ RΓ, ContextREL_Packed Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), TypeREL_Packed A[ρ] A[ρ'] (RA.(RELe_REL) Rρ) × RA.(RELe_REL)Rρ t[ρ] u[ρ'])).
Proof.
  eapply WfDeclInduction.
  - econstructor. econstructor.
  - intros ??? _ ? (? & ? & ? & ?). econstructor.
    econstructor.
    eassumption.
    eassumption.
  - intros ???? (? & relΓ & RDom & relDom) ? (? & rel'Γ & RCod & relCod).
    cbn.
    econstructor.
    econstructor.
    + eassumption.
    + unshelve econstructor.
      * unshelve econstructor.
        -- intros ρ ρ' Rρρ'.
           refine '(FunREL (RDom _ _ Rρρ') _).
           unshelve econstructor.
           intros ? ? Rtt'.
           refine '(RCod (t .: ρ) (t' .: ρ') _).
           assert (ContextREL_Packed (Γ ,, A) (Γ ,, A) _) by (now econstructor).
           apply (ContextREL_det H1) > [eassumption|].
           econstructor.
           exact Rtt'.
           intros ? ? ? Rtt' Rt't'' b b'.
      * intros ?? Rρ.
        eapply realProd.


Inductive Realizability_context : context -> context -> ((nat -> term) -> (nat -> term) -> Type) -> Type :=
  | nil_real : Realizability_context ε ε (fun _ _ => unit)
  | cons_real {Γ Γ' RΓ A B RA} : Realizability_context Γ Γ' RΓ
    -> (forall ρ ρ' (Rρ : RΓ ρ ρ'), Realizability_Packed A[ρ] B[ρ'] (RA ρ ρ' Rρ))
    -> Realizability_context (Γ ,, A) (Γ' ,, B) (fun ρ ρ' => ∑ (Rupρ : RΓ (↑ >> ρ) (↑ >> ρ')), RA _ _ Rupρ (ρ 0) (ρ' 0)).

Derive Signature for Realizability_Packed Real_Nat Realizability_context.


Lemma redToNat_HProp {A} : HProp ([ A ⤳* tNat ]).
Proof.
  remember tNat.
  intros H1.
  induction H1.
  all: intros H2.
  - subst. depelim H2.
    * reflexivity.
    * depelim o.
  - depelim H2.
    * subst. depelim o.
    * eapply ored_det in o as yup > [|eassumption].
      subst.
      rewrite (OneRedAlg_HProp o o0).
      f_equal.
      eauto.
Defined.

(* XXX: Exact same proof *)
Lemma redToProd_HProp {A B C} : HProp ([ A ⤳* tProd B C ]).
Proof.
  remember (tProd B C).
  intros H1.
  induction H1.
  all: intros H2.
  - subst. depelim H2.
    * reflexivity.
    * depelim o.
  - depelim H2.
    * subst. depelim o.
    * eapply ored_det in o as yup > [|eassumption].
      subst.
      rewrite (OneRedAlg_HProp o o0).
      f_equal.
      eauto.
Defined.

Derive NoConfusion for sigT.

Lemma Realizability_irrel {A A'} (H1 H2 : ∑ RA, Realizability_Packed A A' RA)
  : forall t t', H1 .π1 t t' <~> H2 .π1 t t'.
Proof.
  revert H2.
  destruct H1 as (RA & H1).
  induction H1.
  - intros (RA' & H2).
    depelim H2.
    * rewrite (redToNat_HProp r r1).
      rewrite (redToNat_HProp r0 r2).
      reflexivity.
    * assert (eq : tNat = tProd _ _) by (eapply whred_det; > eassumption + econstructor).
      noconf eq.
  - intros (RA' & H2).
    depelim H2.
    * assert (eq : tNat = tProd _ _) by (eapply whred_det; > eassumption + econstructor).
      noconf eq.
    * assert (eq : tProd B C = tProd B0 C0) by (eapply whred_det; > eassumption + econstructor).
      noconf eq.
      assert (eq : tProd B' C' = tProd B'0 C'0) by (eapply whred_det; > eassumption + econstructor).
      noconf eq.
      rewrite (redToProd_HProp r r2) in * |- *.
      rewrite (redToProd_HProp r0 r3) in * |- *.
      specialize (IHRealizability_Packed (RB0 ; H2)).
      intros t t'. cbn.
      split.
      + intros YURP b b' breal.
        specialize (r4 b b' breal).
        eapply IHRealizability_Packed in breal as breal'.
        specialize (X b b' breal' (_ ; r4)).
        eapply X.
        eapply YURP.
      + intros YURP b b' breal.
        eapply IHRealizability_Packed in breal as breal'.
        specialize (r4 b b' breal').
        specialize (X b b' breal (_ ; r4)).
        eapply X.
        eapply YURP.
Defined.

Lemma Realizability_context_irrel {Γ Γ'} (H1 H2 : ∑ RΓ, Realizability_context Γ Γ' RΓ)
  : forall ρ ρ', H1 .π1 ρ ρ' <~> H2 .π1 ρ ρ'.
Proof.
  revert H2.
  destruct H1 as (? & RΓ).
  induction RΓ.
  all: intros (? & RΓ2) ρ.
  - depelim RΓ2.
    split; econstructor.
  - depelim RΓ2.
    split.
    + intros (Rρ & Rρ0).
      assert (Rρ' : RΓ2 (↑ >> ρ) (↑ >> ρ')). { now unshelve (eapply (IHRΓ (_; _))). }
      econstructor.
      now (eapply (Realizability_irrel (_ ; r _ _ Rρ) (_ ; r0 _ _ Rρ'))).
    + intros (Rρ' & Rρ0).
      assert (Rρ : RΓ (↑ >> ρ) (↑ >> ρ')). { now unshelve (eapply (IHRΓ (_; RΓ3))). }
      econstructor.
      now (eapply (Realizability_irrel (_ ; r _ _ Rρ) (_ ; r0 _ _ Rρ'))).
Defined.

Require Import CRelationClasses.

Lemma Realizability_AntiRed {A A' B B'} :
    (∑ RA, Realizability_Packed A A' RA)
 -> [ B ⤳* A ] -> [ B' ⤳* A' ]
 -> (∑ RB, Realizability_Packed B B' RB).
Proof.
  intros (? & RA).
  induction RA.
  all: intros BredA B'redA'.
  all: econstructor.
  all: eapply (PreOrder_Transitive _ _ _) in r > [|eassumption].
  all: eapply (PreOrder_Transitive _ _ _) in r0 > [|eassumption].
  all: now econstructor.
Defined.

Lemma Realizability_term_AntiRed {A A' RA} (_ : Realizability_Packed A A' RA)
  : forall {t t' u u'}, RA t t' -> [ u ⤳* t ] -> [ u' ⤳* t' ] -> RA u u'.
Proof.
  induction X.
  - intros ???? rtt' uredt u'redt'.
    depelim rtt'.
    all: eapply (PreOrder_Transitive _ _ _) in r1 > [|eassumption].
    all: eapply (PreOrder_Transitive _ _ _) in r2 > [|eassumption].
    all: now econstructor.
  - intros ???? H uredt u'redt' b0 b'0 breal0.
    eapply X0 > [| now (eapply redalg_app) ..].
    eapply H.
Defined.

Derive Signature for in_ctx WfContextDecl.

Theorem interp : WfDeclInductionConcl
  (fun Γ => ∑ RΓ, Realizability_context Γ Γ RΓ)
  (fun Γ A => ∑ RΓ, Realizability_context Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), Realizability_Packed A[ρ] A[ρ'] (RA ρ ρ' Rρ)))
  (fun Γ A t => ∑ RΓ, Realizability_context Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), Realizability_Packed A[ρ] A[ρ'] (RA ρ ρ' Rρ) × RA ρ ρ' Rρ t[ρ] t[ρ']))
  (fun Γ A B => ∑ RΓ, Realizability_context Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), Realizability_Packed A[ρ] B[ρ'] (RA ρ ρ' Rρ)))
  (fun Γ A t u => ∑ RΓ, Realizability_context Γ Γ RΓ ×
      ∑ RA, (forall ρ ρ' (Rρ : RΓ ρ ρ'), Realizability_Packed A[ρ] A[ρ'] (RA ρ ρ' Rρ) × RA ρ ρ' Rρ t[ρ] u[ρ'])).
Proof.
  eapply WfDeclInduction.
  - econstructor. econstructor.
  - intros ??? _ ? (? & HΓ & ? & HA).
    econstructor.
    econstructor.
    all: eassumption.
  - intros ???? (? & RΓ & Areals & RA) ? (? & ? & Breals & RB).
    depelim r.
    econstructor.
    (econstructor) > [|econstructor].
    exact RΓ.
    (* intros ? ? Rρ.
     * refine '(fun f f' => forall a a' (H : Areals _ _ Rρ a a'), Breals _ _ _ (tApp f a) (tApp f' a')). *)
    intros ? ? Rρ.
    eapply Prod_real.
    + apply redIdAlg.
    + apply redIdAlg.
    + unshelve (apply r0).
      now (eapply (Realizability_context_irrel (_ ; r) (_ ; RΓ))).
    + ltac1:(fold subst_term).
      intros b b' breal.
      specialize (RB (b .: ρ) (b' .: ρ')).
      rewrite !up_single_subst.
      apply RB.
      Unshelve.
      econstructor.
      exact breal.
  - intros ?? (? & RΓ).
    econstructor.
    split.
    eassumption.
    econstructor.
    intros ? ? Rρ.
    econstructor; econstructor.
  - intros ???? RΓ inctx.
    revert RΓ.
    induction inctx.
    + intros (? & RΓ).
      econstructor.
      split > [eassumption|].
      depelim RΓ.
      econstructor.
      intros ? ? Rρ.
      rewrite !renSubst_term.
      split.
      * apply r.
      * exact (Rρ .π2).
    + intros (? & RΓ).
      econstructor.
      split > [eassumption|].
      depelim RΓ.
      depelim H.
      specialize (IHinctx H (_ ; RΓ0)).
      destruct IHinctx as (? & RΓ1 & ? & RA0).
      econstructor.
      intros ? ? Rρ.
      rewrite !renSubst_term.
      split.
      * eapply RA0.
      * eapply RA0.
        Unshelve.
        destruct Rρ as (Rupρ & _).
        now eapply (Realizability_context_irrel (_ ; RΓ0) (_ ; RΓ1)).
  - intros ????? (? & RΓ1 & ? & RA) ? (? & RΓ2 & ? & Rt).
    depelim RΓ2.
    econstructor.
    split > [eassumption|].
    unshelve econstructor > [|].
    intros ?? Rρ.
    eapply (Realizability_context_irrel (_ ; RΓ2) (_ ; RΓ1)) in Rρ as Rρ'.
    split.
    eapply Prod_real > [econstructor|econstructor|..].
    + fold subst_term.
      eapply RA.
    + fold subst_term.
      intros b b' breal.
      eapply (Realizability_irrel (_ ; RA ρ ρ' Rρ') (_ ; r ρ ρ' Rρ)) in breal as breal'.
      rewrite !up_single_subst.
      eapply Rt.
    + intros b b' breal.
      
      specialize (Rt (b .: ρ) (b' .: ρ') ).
      assert ([ tApp (tLambda A t)[ρ] b ⤳* t[b .: ρ] ]).
      { econstructor. econstructor. fold subst_term. rewrite up_single_subst. now econstructor.  }
      assert ([ tApp (tLambda A t)[ρ'] b' ⤳* t[b' .: ρ'] ]).
      { econstructor. econstructor. fold subst_term. rewrite up_single_subst. now econstructor.  }
      eapply Realizability_term_AntiRed > [eapply Rt|..].
      eapply Rt. cbn.
