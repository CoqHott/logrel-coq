Record Foo (x : Type -> Type) : Type := {}.

Fail Inductive Bar : Type -> Type :=
    | bar : Bar (Foo Bar).
(*Non strictly positive occurrence of "Bar" in "Bar (Foo Bar)".
Coq does not accept nested inductive types in indices, while Agda does. *)