Record Foo (x : Type -> Type) : Type := {}.

Inductive Bar : Type -> Type :=
    | bar : Bar (Foo Bar).
(*Non strictly positive occurrence of "Bar" in "Bar (Foo Bar)".*)