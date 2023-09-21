
Inductive direction :=
| Fun
| Cofun
| Discr
.

Definition dir_op (d: direction) : direction :=
  match d with
  | Fun => Cofun
  | Cofun => Fun
  | Discr => Discr
  end.

Definition dir_leq (d1: direction) (d2: direction) : Type :=
  match d1, d2 with
  | Discr, _ => unit
  | Fun, Fun => unit
  | Fun, Discr => False
  | Cofun, Cofun => unit
  | Cofun, Discr => False
  | Fun, Cofun => False
  | Cofun, Fun => False
  end.

