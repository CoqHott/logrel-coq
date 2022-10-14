From MetaCoq.PCUIC Require Import PCUICAst.

Definition isRel t :=
    match t with tRel _ => true | _ => false end.

Definition eta {A B : Type} (f : A -> B) : f = (fun x => f x) := eq_refl.
