Require Import Untyped MLTTTyping LogicalRelation Properties Reduction LRInduction.

Set Universe Polymorphism.

Definition Sym0 {Γ A B l l'} (ha : [Γ ||-< zero | A]) (hb : [Γ ||-< zero | B]) :
    [Γ ||-< zero | A ≅ B | ha ] ->
    [Γ ||-< zero | B ≅ A | hb ].
Proof.
    intros.
    destruct ha.
    destruct hb.
    destruct valid.