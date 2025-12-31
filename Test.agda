module Test where

import kl1

open kl1

data Bit : Set where
  Zero : Bit
  Uno  : Bit

eqBit : (x y : Bit) → Dec (x ≡ y)
eqBit Zero Zero = yes refl
eqBit Uno Uno   = yes refl
eqBit Zero Uno  = no (λ ())
eqBit Uno Zero  = no (λ ())

open kl1.Syntax Bit eqBit

testRule : Rule
testRule = must (Zero :: []) (Uno :: [])
