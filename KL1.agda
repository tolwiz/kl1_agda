module KL1 where

data Bool : Set where
  true  : Bool
  false : Bool

_∧_ : Bool → Bool → Bool
true ∧ b = b
false ∧ _ = false
infixr 6 _∧_

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
infixr 5 _::_

data _≡_ {A : Set } (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Dec (P : Set) : Set where
  yes : (p : P) → Dec P
  no  : (np : ¬ P) → Dec P

module Logic (Atom : Set) (_≟_ : (x y : Atom) → Dec (x ≡ y)) where
  -- ================
  -- ==== Syntax ====
  -- ================

  Body : Set
  Body = List Atom

  Head : Set
  Head = List Atom

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

  -- ===================
  -- ==== Semantics ====
  -- ===================

  World : Set
  World = List Atom

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)
