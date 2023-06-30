
Set Primitive Projections.
Record Sigma A B := pair { proj1 : A ; proj2 : B proj1 }.
Notation "'∑' x .. y , p" := (Sigma _ (fun x => .. (Sigma _ (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; .. ; y ; z )" := (pair _ _ x .. (pair _ _ y z) ..) : core_scope.
Notation "x .π1" := (@proj1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@proj2 _ _ x) (at level 3, format "x '.π2'").


Definition domΠ := ∑ A, A -> Type.
Definition homΠ (X Y : domΠ) := ∑ (f : Y.π1 -> X.π1), forall (y : Y.π1), X.π2 (f y) -> Y.π2 y.
Definition idΠ (X : domΠ) : homΠ X X := (fun x => x ; fun y x => x).
Definition compΠ {X Y Z} (f : homΠ Y Z) (g : homΠ X Y) : homΠ X Z :=
  let gf1 x := g.π1 (f.π1 x) in 
  (gf1 ; fun z (x : X.π2 (gf1 z)) => f.π2 _ (g.π2 _ x)).

Definition mapPi {X Y} (f : homΠ X Y) (h : forall x : X.π1, X.π2 x) (y : Y.π1) := f.π2 _ (h (f.π1 y)).

Lemma mapPiRefl {X : domΠ} (h : forall x : X.π1, X.π2 x) : mapPi (idΠ X) h = h.
Proof. reflexivity. Defined.

Lemma mapPiComp {X Y Z : domΠ} (f : homΠ Y Z) (g : homΠ X Y) (h : forall x : X.π1, X.π2 x) :
  mapPi f (mapPi g h) = mapPi (compΠ f g) h.
Proof. reflexivity. Defined.

Definition domΣ := ∑ A, A -> Type.
Definition homΣ (X Y : domΣ) := ∑ (f : X.π1 -> Y.π1), forall {x : X.π1}, X.π2 x -> Y.π2 (f x).
Definition idΣ (X : domΣ) : homΣ X X := let id x := x in (id ; fun y x => x : X.π2 (id y)).
Definition compΣ {X Y Z} (f : homΣ Y Z) (g : homΣ X Y) : homΣ X Z :=
  let fg1 x := f.π1 (g.π1 x) in
  (fg1 ; fun x1 x => f.π2 _ (g.π2 _ x) : Z.π2 (fg1 x1)).

Definition mapSig {X Y} (f : homΣ X Y) (h : ∑ x : X.π1, X.π2 x) := (f.π1 h.π1; f.π2 _ h.π2).

Lemma mapSigRefl {X : domΠ} (h : ∑ x : X.π1, X.π2 x) : mapSig (idΣ X) h = h.
Proof. reflexivity. Defined.

Lemma mapSigComp {X Y Z : domΣ} (f : homΣ Y Z) (g : homΣ X Y) (h : ∑ x : X.π1, X.π2 x) :
  mapSig f (mapSig g h) = mapSig (compΣ f g) h.
Proof. reflexivity. Qed.
