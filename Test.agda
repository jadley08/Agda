module Test where

open import Data.Nat

data Bool : Set where
  true : Bool
  false : Bool

data MyNat : Set where
  zero : MyNat
  succ : MyNat -> MyNat
