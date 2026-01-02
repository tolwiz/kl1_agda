module Test where

import KL1 

open KL1 

data Bit : Set where
  Zero : Bit
  One  : Bit

eqBit : (x y : Bit) → Dec (x ≡ y)
eqBit Zero Zero = yes refl
eqBit One One   = yes refl
eqBit Zero One  = no (λ ())
eqBit One Zero  = no (λ ())

open KL1.Logic Bit eqBit

testRule : Rule
testRule = must (Zero :: []) (One :: [])

testAnd1 : (true ∧ true) ≡ true
testAnd1 = refl

testAnd2 : (true ∧ false) ≡ false
testAnd2 = refl

testAnd3 : (false ∧ true) ≡ false
testAnd3 = refl

testAnd4 : (false ∧ false) ≡ false
testAnd4 = refl

testList : List Bit
testList = Zero :: One :: []

testMember1 : (One ∈? testList) ≡ true
testMember1 = refl

testMember2 : (Zero ∈? testList) ≡ true
testMember2 = refl

testSubSet1 : ((One :: []) ⊆? testList) ≡ true
testSubSet1 = refl

testSubSet2 : (testList ⊆? testList) ≡ true
testSubSet2 = refl

testSubSet3 : ((Zero :: Zero :: One :: One :: Zero :: []) ⊆? (One :: [])) ≡ false
testSubSet3 = refl

testSubSetEmpty : ([] ⊆? testList) ≡ true
testSubSetEmpty = refl
