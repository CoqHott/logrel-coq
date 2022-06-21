Axiom context : Type.
Axiom term : Type.
Axiom tApp : term -> term -> term.


Definition RedRel := 
  context               -> 
  term                  -> 
 (term -> Type)         -> 
  Type.
Record LRPack (Γ : context) (A : term) (R : RedRel) := {
    relTerm : term -> Type;
    relLR : R Γ A  relTerm
}.
Notation "[ Γ ||-0 A | R ]" := (LRPack Γ A R) (at level 0).
Definition TeRelO {R : RedRel} (Γ : context) (t A : term) (L : [ Γ ||-0 A | R ]) : Type :=
    relTerm _ _ _ L A.
Notation "[ Γ ||-0 t ::: A | R ]" := (TeRelO Γ t A R) (at level 0).
Record TyPiRel1 (Γ : context) (A : term) (R : RedRel) : Type := {
    
}.
Notation "[ Γ ||-1Π A | R ]" := (TyPiRel1 Γ A R) (at level 0).

Inductive LR : RedRel := 
  | LRPi {Γ A} : [ Γ ||-1Π A | LR ] -> LR Γ A
      (fun t   => [ Γ ||-0 t ::: A | LR Γ A ]).
