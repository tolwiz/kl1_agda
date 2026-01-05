module KL1 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

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

  _∩?_ : List Atom → World → Bool
  []        ∩? w = false
  (x :: xs) ∩? w = (x ∈? w) ∨ (xs ∩? w)
  infix 7 _∩?_

  _⊨?_ : World → Rule → Bool
  w ⊨? (may _ _) = true
  w ⊨? (must b c) = (b ⊆? w) ⇒ (c ∩? w)
  infix 5 _⊨?_

  _⊨*?_ : World → List Rule → Bool
  w ⊨*? [] = true
  w ⊨*? (r :: rs) = (w ⊨? r) ∧ (w ⊨*? rs)
  infix 5 _⊨*?_

  filter : {A : Set} →  (A → Bool) → List A → List A
  filter p [] = []
  filter p (x :: xs) with p x
  ... | true  = x :: filter p xs
  ... | false = filter p xs

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)
  
  concat : {A : Set} → List (List A) → List A
  concat [] = []
  concat (x :: xs) = x ++ concat xs

  concatMap : {A B : Set} → (A → List B) → List A → List B
  concatMap f xs = concat (map f xs)

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
    -- concatMap (λ (opt : List A) → map (λ (t : List A) → opt ++ t) tails) options
    concatMap (λ opt → map (λ t → opt ++ t) tails) options

  step : List Rule → World → List World
  --step rules w =
  --  map (λ add → w ++ add) (cartesian (map (λ r → ruleOptions r w) rules))
  step rules w =
    let
      allOptions : List (List (List Atom))
      allOptions = map (λ r → ruleOptions r w) rules

      additions : List (List Atom)
      additions = cartesian allOptions

      nextWorlds : List World
      nextWorlds = map (λ add → w ++ add) additions
    in
      nextWorlds
  
  cns : List Rule → World → ℕ → List World
  cns rules w zero = w :: [] 
  cns rules w (suc n) =
    -- concatMap (λ nw → cns rules nw n) (step rules w)
    let nexts = step rules w in
    concatMap (λ nw → cns rules nw n) nexts

  out₁ : List Rule → World → ℕ → List World
  out₁ rules initialWorld fuel =
    let
      candidates = cns rules initialWorld fuel
    in
      filter (λ w → w ⊨*? rules) candidates
