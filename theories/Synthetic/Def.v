Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.

(** We start with a small agnostic prelude to make this file self-contained. *)

Record sig@{i j} (A : Type@{i}) (B : A -> Type@{j}) := {
  fst : A;
  snd : B fst;
}.

Arguments fst {_ _}.
Arguments snd {_ _}.

(** Type of paths. For now we're not committing to a specific world, it may
    be univalent or satisfy UIP, or neither. For compatibility with the former
    you should still use the indices-matter setting.

    Later on, we will introduce HIT constructions via axioms, but again they
    make sense in both the univalent and the strict universes.
*)
Inductive path@{i} (A : Type@{i}) (x : A) : A -> Type@{i} := refl : path A x x.

Arguments path {A} _ _.
Arguments refl {A x}.

Notation "x = y" := (@path _ x y) : type_scope.

Notation "'rew' H 'in' H'" := (@path_rect _ _ (fun x _ => _) H' _ H)
  (at level 10, H' at level 10,
   format "'[' 'rew'  H  in  '/' H' ']'").
Notation "'rew' [ P ] H 'in' H'" := (@path_rect _ _ (fun x _ => P x) H' _ H)
  (at level 10, H' at level 10,
   format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").

Definition sym {A} {x y : A} (p : x = y) : y = x.
Proof.
destruct p; constructor.
Defined.

Definition comp {A} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
destruct q; exact p.
Defined.

Lemma ap : forall {A B} (f : A -> B) {x y : A} (e : x = y), f x = f y.
Proof.
intros.
refine (rew [fun z => f x = f z] e in refl).
Defined.

Lemma apfun : forall {A B} {f g : forall x : A, B x} (e : f = g), (forall x, f x = g x).
Proof.
intros.
refine (rew [fun h => f x = h x] e in refl).
Defined.

(** Due to the lack of sort polymorphism in this version of Rocq, we also
    have to state it for functions with a domain in SProp. *)
Lemma apsfun : forall {A : SProp} {B : A -> Type} {f g : forall x : A, B x} (e : f = g), (forall x, f x = g x).
Proof.
intros; destruct e; constructor.
Defined.

Record isEquiv@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) := {
  eqv_rev : B -> A;
  eqv_idl : forall (x : A), eqv_rev (f x) = x;
  eqv_idr : forall (y : B), f (eqv_rev y) = y;
  eqv_coh : forall (x : A), ap f (eqv_idl x) = eqv_idr (f x);
}.

Definition ishProp@{i} (A : Type@{i}) := forall (x : A) (e : x = x), e = refl.

(** We are still going to assume funext. *)
Axiom Funext@{i j k} : forall {A : Type@{i}} {B : A -> Type@{j}} f g,
  isEquiv (@apfun@{i j k} A B f g).

Lemma funext : forall A (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g.
Proof.
intros *; eapply Funext.
Defined.

(* Same issue with lack of sort polymorphism *)
Axiom sFunext@{i} : forall {A : SProp} {B : A -> Type@{i}} f g,
  isEquiv (@apsfun@{i} A B f g).

Lemma sfunext : forall (A : SProp) (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Proof.
intros *; eapply sFunext.
Defined.

Lemma rew_inj : forall {A} (P : A -> Type) {x y : A} {p q : P x} (e : x = y),
  (rew [P] e in p = rew [P] e in q) -> p = q.
Proof.
destruct e; intros r; exact r.
Defined.

Lemma funext_elim : forall {A B} {f g} e x P p,
  rew [fun h => P (h x)] @funext A B f g e in p =
  rew [P] e x in p.
Proof.
intros.
unfold funext.
pose (r := (Funext f g).(eqv_idr _) e).
set (e0 := e) at 1; destruct r; unfold e0; clear e0.
unfold apfun.
destruct (eqv_rev _ (Funext f g) e).
reflexivity.
Defined.

Lemma sfunext_elim : forall {A B} {f g} e x P p,
  rew [fun h => P (h x)] @sfunext A B f g e in p =
  rew [P] e x in p.
Proof.
intros.
unfold sfunext.
pose (r := (sFunext f g).(eqv_idr _) e).
set (e0 := e) at 1; destruct r; unfold e0; clear e0.
unfold apfun.
destruct (eqv_rev _ (sFunext f g) e).
reflexivity.
Defined.

(** We now start definining our sheaf theory proper. *)

(** General setting: we globally fix a Lawvere-Tierney topology. We depart from the
    usual presentation, which amounts to a monad on SProp, i.e.

    T : SProp -> SProp
    η : forall A, A -> T A
    bind : forall A B, T A -> (A -> T B) -> T B

    where all equations hold trivially due to the use of SProp.

    Rather, we give it through a set of generators. The usual setting can be
    retrieved by picking I := Σ P : SProp. T P and O (P, _) := P. *)

Axiom I : Set.
Axiom O : I -> SProp.

(** The type of "ideal" objects approximated by sheaves. It may be empty. *)
Definition ℙ := forall i : I, O i.

(** The meaty part: a synthetic definition of sheaves. *)
Record isSheaf@{u} (A : Type@{u}) : Type@{u} := {
  shf_elt : forall i : I, (O i -> A) -> A;
  shf_spc : forall i (x : A), x = shf_elt i (fun _ => x);
}.

Arguments shf_elt {_}.
Arguments shf_spc {_}.

Lemma isSheaf_eq_intro : forall A fp fq hp hq (ef : fp = fq),
  (rew [fun fr => forall (i : I) (x : A), x = fr i (fun _ : O i => x)] ef in hp = hq) ->
  Build_isSheaf A fp hp = Build_isSheaf A fq hq.
Proof.
destruct ef.
destruct 1.
constructor.
Defined.

Lemma rew_app : forall A Z (B : A -> Z -> Type) {z1 z2 : Z} f (e : z1 = z2) (x : A),
  (rew [fun z => forall x : A, B x z] e in f) x = rew [B x] e in f x.
Proof.
intros.
destruct e; reflexivity.
Defined.

Lemma sfunext_refl : forall (A : SProp) (B : A -> Type) (f : forall x : A, B x),
  sfunext A B f f (fun _ => refl) = refl.
Proof.
intros.
unfold sfunext.
destruct sFunext as [p q φ ψ]; cbn in *.
apply (q refl).
Qed.

(* Being a sheaf is a mere proposition. *)
Lemma isSheaf_ishProp : forall A (p q : isSheaf A), p = q.
Proof.
intros A [fp Hp] [fq Hq].
unshelve eapply isSheaf_eq_intro.
{ apply funext; intros i; apply funext; intros x.
  pose (epq := Hp i (fq i x)).
  refine (comp _ (sym epq)).
  refine (ap _ _).
  apply sfunext; intro o.
  change x with (fun _ : O i => x o) at 2.
  apply Hq. }
apply funext; intros i.
apply funext; intros x.
rewrite !rew_app.
match goal with [ |- path (path_rect _ _ _ _ _ (funext _ _ _ _ ?e)) _ ] =>
set (ei := e)
end.
pose (er := @funext_elim _ _ _ _ ei i (fun k => x = (k (fun _ => x)))); cbn in er.
refine (comp _ _); [apply er|clear er].
unfold ei; clear ei.
match goal with [ |- path (path_rect _ _ _ _ _ (funext _ _ _ _ ?e)) _ ] =>
set (ei := e)
end.
pose (er := @funext_elim _ _ _ _ ei (fun _ => x)); cbn in er.
refine (comp _ _); [apply er|clear er].
unfold ei; clear ei.
destruct Hq; cbn; clear fq Hq.
match goal with [ |- context [ap ?f ?e] ] =>
  assert (ef : ap f e = refl)
end.
{
  unfold ap.
  set (r := sfunext (O i) _ (fun _ => x) (fun _ => x) (fun _ => refl)).
  eapply (comp (y := ap (fp i) (rew [fun k => path (fun _ => x) k] r in refl))); cbn.
  { clearbody r.
    refine (match r as e in _ = k return
    rew [fun k => path (fp i _) (fp i k)] e in refl =
      ap (fp i) (rew [fun k => path _ k] e in refl) with refl => _ end); cbn.
    reflexivity. }
  enough (rew [path (fun _ => x)] r in refl = refl) as H by (rewrite H; constructor).
  enough (r = refl) as H by (rewrite H; constructor).
  apply sfunext_refl.
}
rewrite ef; cbn.
destruct Hp.
reflexivity.
Qed.

(** Internal types in the sheaf theory. *)
Record TypeШ@{u} := { typ : Type@{u}; shf : isSheaf@{u} typ }.

Coercion typ : TypeШ >-> Sortclass.

(** Sheaves are closed under Π-type codomain *)
Lemma isSheaf_Π : forall (A : Type) (B : A -> TypeШ), isSheaf (forall x : A, B x).
Proof.
intros.
exists (fun i (k : O i -> forall (x : A), B x) x => (B x).(shf).(shf_elt) i (fun o => k o x)).
{ intros i f; apply funext; intros x; apply shf_spc. }
Qed.

(** Sheafification *)
Module Import Sh.

Private Inductive Shf (A : Type) :=
| ret : A -> Shf A
| ask : forall i, (O i -> Shf A) -> Shf A.

Arguments ret {_}.
Arguments ask {_}.

Axiom eqn : forall {A} (i : I) (x : Shf A), ask i (fun _ => x) = x.

Fixpoint Shf_rect (A : Type) (P : Shf A -> Type)
  (ur : forall (x : A), P (ret x))
  (ua : forall (i : I) (k : O i -> Shf A),
    (forall o : O i, P (k o)) -> P (ask i k))
  (ue : forall (i : I) (x : Shf A) (px : P x),
    match eqn i x in _ = e return P e with refl => ua i (fun _ => x) (fun _ => px) end = px)
  (x : Shf A) {struct x} :
  P x :=
match x with
| ret x => ur x
| ask i k => ua i k (fun o => Shf_rect A P ur ua ue (k o))
end.

Fixpoint Shf_sind (A : Type) (P : Shf A -> SProp)
  (ur : forall (x : A), P (ret x))
  (ua : forall (i : I) (k : O i -> Shf A),
    (forall o : O i, P (k o)) -> P (ask i k))
  (x : Shf A) {struct x} :
  P x :=
match x with
| ret x => ur x
| ask i k => ua i k (fun o => Shf_sind A P ur ua (k o))
end.

End Sh.

(** If we have an ideal oracle, we can run the sheaf by just getting the
    answers to the questions from the oracle. *)
Definition eval {A} (x : Shf A) (α : ℙ) : A.
Proof.
unshelve refine (
Shf_rect A (fun _ => A) (fun x => x) (fun i k r => r (α i)) _ x
).
{ clear; intros; destruct eqn; reflexivity. }
Defined.

Section Permut.

Variable A : Type.
Variable i j : I.
Variable k : O i -> O j -> Shf A.

(** Effect order does not matter with sheaves, a big departure from more standard
    algebraic effects. *)
Lemma permut_equiv :
  ask i (fun o => ask j (fun q => k o q)) = ask j (fun q => ask i (fun o => k o q)).
Proof.
match goal with [ |- ?p = ?q ] => rewrite <- (eqn i q) end.
apply ap, sfunext; intros o.
apply ap, sfunext; intros q.
change (fun o' => k o' q) with (fun _ : O i => k o q).
rewrite eqn; reflexivity.
Qed.

End Permut.

(** Sheafified W-Types *)
Module Import WШ.

(** Sheafified inductive types are the same as their usual presentation except that
    they freely add the ask / eqn quotient. *)
Private Inductive WШ (A : TypeШ) (B : A -> TypeШ) :=
| sup_Ш : forall (a : A) (f : B a -> WШ A B), WШ A B
| ask_W : forall (i : I) (k : O i -> WШ A B), WШ A B.

Arguments sup_Ш {A B}.
Arguments ask_W {A B}.

Axiom eqn_W : forall {A B} (i : I) (x : WШ A B), ask_W i (fun _ => x) = x.

Fixpoint WШ_rect (A : TypeШ) (B : A -> TypeШ) (P : WШ A B -> Type)
  (us : forall (a : A) (f : B a -> WШ A B), (forall b : B a, P (f b)) -> P (sup_Ш a f))
  (ua : forall (i : I) (k : O i -> WШ A B),
    (forall o : O i, P (k o)) -> P (ask_W i k))
  (ue : forall (i : I) (x : WШ A B) (px : P x),
    match eqn_W i x in _ = e return P e with refl => ua i (fun _ => x) (fun _ => px) end = px)
  (x : WШ A B) {struct x} :
  P x :=
match x with
| sup_Ш a f => us a f (fun b : B a => WШ_rect A B P us ua ue (f b))
| ask_W i k => ua i k (fun o => WШ_rect A B P us ua ue (k o))
end.

End WШ.

(** We now prove the internal version in the sheaf theory that WШ is the sheaf interpretation of W-types.
    Note the type of P, which returns a sheaf rather than an arbitrary type. By contrast,
    we are not provided with the branches for the ask / eqn constructors,
    so we must find something to put in there. *)
Definition W_rect_Ш (A : TypeШ) (B : A -> TypeШ) (P : WШ A B -> TypeШ)
  (us : forall (a : A) (f : B a -> WШ A B), (forall b : B a, P (f b)) -> P (sup_Ш a f)) :
  forall x : WШ A B, P x.
Proof.
unshelve refine (WШ_rect A B (fun x => P x) us _ _).
+ intros i k r.
  refine ((P (ask_W i k)).(shf).(shf_elt) i (fun o => _)).
  refine (match eqn_W i (k o) in _ = z return P z -> P (ask_W i k) with refl => fun r => r end (r o)).
+ intros i x; simpl.
  (** The secret ingredient in the refine below is that for any term k,
      o : O i ⊢ (fun _ => k o) ≡ k : O i -> A. *)
  refine (
    match eqn_W i x as e in _ = z return
      forall px : P z,
      match e in _ = w return P w with
      | refl =>
          shf_elt (shf (P (ask_W i (fun _ : O i => x)))) i
            (fun _ : O i =>
             match e in _ = z return P z -> P (ask_W i (fun _ : O i => x)) with
             | refl => fun r : P (ask_W i (fun _ : O i => x)) => r
             end px)
      end = px
    with
    | refl => _
    end
  ).
  intros.
  symmetry.
  refine ((P _).(shf).(shf_spc) _ _).
Defined.

(** We build the internal sheaf CwF in the section below.
    This is a straightforward subuniverse construction. *)
Module CwF.

Definition Ctx@{i} := Type@{i}.

Definition Sub@{i} (Γ Δ : Ctx@{i}) := Γ -> Δ.

Definition Sub_idn@{i} (Γ : Ctx@{i}) : Sub Γ Γ := fun γ => γ.
Definition Sub_cmp@{i} (Γ Δ Ξ : Ctx@{i}) (σ : Sub Γ Δ) (τ : Sub Δ Ξ) := fun γ => τ (σ γ).

Record Typ@{i j} (Γ : Ctx@{i}) := {
  typ : forall γ : Γ, Type@{j};
  shf : forall γ, isSheaf (typ γ);
}.

Coercion typ : Typ >-> Funclass.

Arguments typ {Γ}.
Arguments shf {Γ}.

Definition Typ_subs@{i j} {Γ Δ : Ctx@{i}} (A : Typ@{i j} Δ) (σ : Sub Γ Δ) : Typ@{i j} Γ :=
  Build_Typ Γ (fun γ => A.(typ) (σ γ)) (fun γ => A.(shf) (σ γ)).

Record Trm@{i j} (Γ : Ctx@{i}) (A : Typ@{i j} Γ) := {
  trm : forall γ, A γ;
}.

Coercion trm : Trm >-> Funclass.

Definition Trm_subs@{i j} {Γ Δ : Ctx@{i}} {A : Typ@{i j} Δ} (t : Trm@{i j} Δ A) (σ : Sub Γ Δ) : Trm@{i j} Γ (Typ_subs A σ) :=
  Build_Trm Γ (Typ_subs A σ) (fun γ => t (σ γ)).

Definition Ext@{i j k} (Γ : Ctx@{i}) (A : Typ@{i j} Γ) : Ctx@{k} := sig@{i j} Γ (A.(typ)).

Definition Wkn@{i j} (Γ : Ctx@{i}) (A : Typ@{i j} Γ) : Sub (Ext Γ A) Γ := fst.

Definition Var0@{i j} {Γ : Ctx@{i}} (A : Typ@{i j} Γ) : Trm@{i j} (Ext Γ A) (Typ_subs A (Wkn Γ A)) :=
  Build_Trm _ (Typ_subs A (Wkn Γ A)) (fun γ => γ.(snd)).

End CwF.
