module kl1 where

open import Data.List using (List)
-- open import Relation.Binary.PropositionalEquality using (_≡_)
-- open import Relation.Nullary using (Dec)

data _≡_ {A : Set } (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Dec (P : Set) : Set where
  yes : (p : P) → Dec P
  no  : (np : ¬ P) → Dec P

module Syntax (Atom : Set) (_≟_ : (x y : Atom) → Dec (x ≡ y)) where
  Body : Set
  Body = List Atom

  Head : Set
  Head = List Atom

  data Rule : Set where
    must : (b : Body) → (c : Head) → Rule
    may  : (b : Body) → (c : Head) → Rule
