module KL1 where

-- ==================================================================
-- === General definitions and helper functions 
-- ==================================================================
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
 
data Bool : Set where
  true  : Bool
  false : Bool

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false
infixr 6 _∧_

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b
infixr 5 _∨_ 

_⇒_ : Bool → Bool → Bool
true  ⇒ false = false
_     ⇒ _     = true
infixr 4 _⇒_

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
infixr 5 _::_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : {A : Set} →  (A → Bool) → List A → List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

concat : {A : Set} → List (List A) → List A
concat [] = []
concat (x :: xs) = x ++ concat xs

concatMap : {A B : Set} → (A → List B) → List A → List B
concatMap f xs = concat (map f xs)

data _≡_ {A : Set } (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Dec (P : Set) : Set where
  yes : (p : P) → Dec P
  no  : (np : ¬ P) → Dec P

-- ================================================================
-- === KL1
-- ================================================================
module Logic (Atom : Set) (_≟_ : (x y : Atom) → Dec (x ≡ y)) where
 
  -- ==============================================================
  -- === Common
  -- ==============================================================
  Body : Set
  Body = List Atom

  Head : Set
  Head = List Atom

  World : Set
  World = List Atom
  
  data Rule : Set where
    must : (b : Body) → (c : Head) → Rule
    may  : (b : Body) → (c : Head) → Rule
  
  _∈?_ : Atom → List Atom → Bool
  a ∈? [] = false
  a ∈? (x :: xs) with a ≟ x
  ... | yes _ = true
  ... | no  _ = a ∈? xs

  _⊆?_ : List Atom → List Atom → Bool
  [] ⊆? ys = true
  (x :: xs) ⊆? ys = (x ∈? ys) ∧ (xs ⊆? ys)
  infix 4 _⊆?_
  
  _∩?_ : List Atom → World → Bool
  []        ∩? w = false
  (x :: xs) ∩? w = (x ∈? w) ∨ (xs ∩? w)
  infix 7 _∩?_

  _∪_ : List Atom → List Atom → List Atom
  [] ∪ ys = ys
  (x :: xs) ∪ ys with x ∈? ys
  ... | true = xs ∪ ys
  ... | false = x :: (xs ∪ ys)
  infixr 5 _∪_

  _⊨?_ : World → Rule → Bool
  w ⊨? (may _ _) = true
  w ⊨? (must b c) = (b ⊆? w) ⇒ (c ∩? w)
  infix 5 _⊨?_

  _⊨*?_ : World → List Rule → Bool
  w ⊨*? [] = true
  w ⊨*? (r :: rs) = (w ⊨? r) ∧ (w ⊨*? rs)
  infix 5 _⊨*?_

  _≈?_ : World → World → Bool
  w1 ≈? w2 = (w1 ⊆? w2) ∧ (w2 ⊆? w1)
  infix 4 _≈?_

  _∈W?_ : World → List World → Bool
  w ∈W? [] = false
  w ∈W? (x :: xs) = (w ≈? x) ∨ (w ∈W? xs)
  infix 4 _∈W?_

  deduplicate : List World → List World
  deduplicate [] = []
  deduplicate (w :: ws) with w ∈W? ws
  ... | true = deduplicate ws
  ... | false = w :: deduplicate ws
  
  -- ==============================================================
  -- === Semantics 3.2 
  -- ==============================================================
  module Semantics1 where

    bodyOf : Rule → Body
    bodyOf (must b c) = b
    bodyOf (may b c)  = b
    
    ruleOptions : Rule → World → List (List Atom)
    ruleOptions r w with (bodyOf r) ⊆? w | r
    ... | false | _ = [] :: [] 
    ... | true  | must _ heads = map (λ h → h :: []) heads
    ... | true  | may  _ heads = [] :: (map (λ h → h :: []) heads)
  
    cartesian : {A : Set} → List (List (List A)) → List (List A)
    cartesian [] = [] :: []
    cartesian (options :: rest) =
      let tails = cartesian rest in
      concatMap (λ opt → map (λ t → opt ++ t) tails) options

    step : List Rule → World → List World
    step rules w =
      let
        allOptions = map (λ r → ruleOptions r w) rules
        additions  = cartesian allOptions
      in
        map (λ add → add ∪ w) additions

    cns : List Rule → World → ℕ → List World
    cns rules w zero = w :: [] 
    cns rules w (suc n) =
      let nexts = step rules w in
      concatMap (λ nw → cns rules nw n) nexts
  
    out₁ : List Rule → World → ℕ → List World
    out₁ rules initialWorld n = 
      let
        candidates = cns rules initialWorld n
        valid      = filter (λ w → w ⊨*? rules) candidates
      in
        deduplicate valid 

  -- ===============================================================
  -- === Semantics 3.3
  -- ===============================================================
  module Semantics2 where
