record Foo (x : Set -> Set) :  Set where

data Bar : Set -> Set where
  bar : Bar (Foo Bar)
