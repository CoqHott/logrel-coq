Require Import MLTTTyping LogicalRelation.

Set Universe Polymorphism.



Inductive ShapeView0 Γ : 
    forall A B, [Γ ||-< zero | A] -> [Γ ||-< zero | B] -> Type 
:=
    | SVne {A B} neA neB :
        ShapeView0 Γ A B
        (LRne_ _ zero  neA)
        (LRne_ _ zero neB)

    | SVPi {A B} Π0A Π0B Π1A Π1B:
        ShapeView0 Γ A B
        (LRPi_ _ _ Π0A Π1A)
        (LRPi_ _ _ Π0B Π1B)
         

          .

Inductive ShapeView1 Γ : 
    forall A B, [Γ ||-< one | A] -> [Γ ||-< one | B] -> Type 
:=
    (*| SVU {l_a Γa l_b Γb} :
      ShapeView Γ _ _
        (LRValidMk _ _ _
            (LRU (LogRelRec _) Γa _ l_a))
        (LRValidMk _ _ _
            (LRU (LogRelRec _) Γb _ l_b))

    | SVne {A B} neA neB :
      ShapeView Γ A B
        (LRne_ _ _ neA)
        (LRne_ _ _  neB)

    | SVPi {A B} Π0A Π0B Π1A Π1B :
        ShapeView Γ A B
        (LRPi_ _ _ Π0A Π1A)
        (LRPi_ _ _ Π0B Π1B)*)
         
    | SVemb01 {A B p q} (leq : l = one):
       @ShapeView Γ l l' A B p q ->
        ShapeView Γ A B (LREmb_ _  (LESubst leq) p) q.
(*universe error.....*)      
