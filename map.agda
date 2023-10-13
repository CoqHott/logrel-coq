{-# OPTIONS --rewriting #-}

-- Tested with agda 2.6.1
-- To setup agda and test this file, follow installation instructions at
-- https://agda.readthedocs.io/en/latest/getting-started/installation.html
-- and
-- https://agda.readthedocs.io/en/latest/getting-started/a-taste-of-agda.html


{- Prelude
  Definition of boolean, natural numbers and lists
-}

data bool : Set where
  true : bool
  false : bool

data nat : Set where
  Z : nat
  S : nat → nat

dbl : nat → nat
dbl Z = Z
dbl (S n) = S (S n)

-- 42 = 2*21 = 2*(1+2*2*5) = 2*(1+2*2*(1+2*2))
forty-two : nat
forty-two = dbl (S (dbl (dbl (S (dbl (S (S Z)))))))


data list (A : Set) : Set where
  nil : list A
  cons :  (a : A) (l : list A) → list A

{- Emulation of the functor laws on list using rewrite rules

  We axiomatize a functorial map operation on list and
  use the experimental rewriting feature of Agda
  (https://agda.readthedocs.io/en/latest/language/rewriting.html)
  to extend the equational theory with the corresponding rule.

  Note that the set of rewriting rules we provide are not deterministic
  (we cannot enforce the restriction to neutral list on map-comp
  as in the paper or the formal coq development).
  They should be confluent but the confluence checker won't be able to
  prove it automatically.

  We did not prove either that map-id is complete with respect to
  the equational theory in the paper.
-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


postulate map : (A B : Set) (f : A → B) (l : list A) → list B

-- Standard reduction rules of map on list constructors
postulate map-nil : (A B : Set) (f : A → B) → map A B f nil ≡ nil
postulate map-cons : (A B : Set) (f : A → B) (a : A) (l : list A) → map A B f (cons a l) ≡ cons (f a) (map A B f l)

-- Functor laws
postulate map-comp : (A B C : Set) (f : A → B) (g : B → C) (l : list A) → map B C g (map A B f l) ≡ map A C (λ x → g (f x)) l
postulate map-id : (A : Set) (l : list A) → map A A (λ x → x) l ≡ l

-- Asking agda to use these equations as rewrite rules from left to right
{-# REWRITE map-comp map-id map-nil map-cons #-}


-- Example 1.1: Representation change

-- The record type D correspond to { a : N ; b : B }
-- and D' to { x : B ; y : N ; z : N }

record D : Set where
  constructor mk
  field
    a : nat
    b : bool

record D' : Set where
  constructor mk
  field
    x : bool
    y : nat
    z : nat

-- Definition of glue and its retraction

glue : D → D'
D'.x (glue d) = d.(D.b)
D'.y (glue d) = d.(D.a)
D'.z (glue d) with d.(D.b)
... | true = d.(D.a)
... | false = forty-two

glue-retr : D' → D
D.a (glue-retr d') = d'.(D'.y)
D.b (glue-retr d') = d'.(D'.x)

-- Using map, we can lift this change of representation to lists

map-glue : list D → list D'
map-glue = map D D' glue

map-glue-retr : list D' → list D
map-glue-retr = map D' D glue-retr


-- The actual example: lifting the change of representation and back is the identity

example : (l : list D) → map _ _ glue-retr (map _ _ glue l) ≡ l
example l = refl

