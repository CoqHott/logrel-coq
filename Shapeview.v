Require Import MLTTTyping LogicalRelation.

Check LRPi.

Inductive ShapeView Γ (l l' : TypeLevel) : 
    forall A B, [Γ ||-< l | A] -> [Γ ||-< l' | B] -> Type 
:=
    | SVU {la l_a Γa lb l_b Γb} :
        ShapeView Γ l l' U U 
         (LRU_ Γa la l_a)
         (LRU_ Γb lb l_b)

    | SVne {A B} neA neB :
        ShapeView Γ l l' A B
        (LRne_ _ _ neA)
        (LRne_ _ _ neB)

    | SVPi {A B} Π0A Π0B Π1A Π1B:
        ShapeView Γ l l' A B
        (LRPi_ _ _ Π0A Π1A)
        (LRPi_ _ _ Π0B Π1B)
         
    | SVemb01 {A B p q} (leq : l = one) :
      ShapeView Γ zero l' A B p q ->
      ShapeView Γ l l' A B (LREmb_ _  (LESubst leq) p) q   
          . 