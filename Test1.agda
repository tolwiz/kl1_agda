module Test1 where

open import KL1

data MyAtom : Set where
  stripes : MyAtom
  buzz : MyAtom
  bee : MyAtom
  wasp : MyAtom

eqAtom : (x y : MyAtom) → Dec (x ≡ y)
eqAtom stripes stripes = yes refl
eqAtom stripes buzz    = no (λ ())
eqAtom stripes bee     = no (λ ())
eqAtom stripes wasp    = no (λ ())
eqAtom buzz    stripes = no (λ ())
eqAtom buzz    buzz    = yes refl
eqAtom buzz    bee     = no (λ ())
eqAtom buzz    wasp    = no (λ ())
eqAtom bee     stripes = no (λ ())
eqAtom bee     buzz    = no (λ ())
eqAtom bee     bee     = yes refl
eqAtom bee     wasp    = no (λ ())
eqAtom wasp    stripes = no (λ ())
eqAtom wasp    buzz    = no (λ ())
eqAtom wasp    bee     = no (λ ())
eqAtom wasp    wasp    = yes refl

open Logic MyAtom eqAtom
open Semantics1

r1 : Rule
r1 = may (stripes :: buzz :: []) (bee :: [])

r2 : Rule
r2 = may (stripes :: buzz :: []) (wasp :: [])

r3 : Rule
r3 = must (bee :: wasp :: []) []

myRules : List Rule
myRules = r1 :: r2 :: r3 :: []

initialState : World
initialState = stripes :: buzz :: []

simulation : List World
simulation = out₁ myRules initialState 5 
