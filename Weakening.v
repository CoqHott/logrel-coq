From MetaCoq.PCUIC Require Import PCUICAst.

Definition isRel t :=
    match t with tRel _ => true | _ => false end.



Check subst.