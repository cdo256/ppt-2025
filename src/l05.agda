{- Lecture 05 COMP4074 -}
variable A B C : Set

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
-- disjoint union , sums, coproducts

open import Data.Bool

data Fuzzy : Set where
  true false maybe : Fuzzy

-- pattern matching
bool→fuzzy : Bool → Fuzzy
bool→fuzzy false = false
bool→fuzzy true = true

-- create patterns, put variable in shed C-c C-c
foo : Bool ⊎ Fuzzy → Fuzzy
foo (inj₁ false) = false
foo (inj₁ true) = true
foo (inj₂ x) = x

paws : A ⊎ B → B ⊎ A
paws (inj₁ a) = inj₂ a
paws (inj₂ b) = inj₁ b

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
-- (cartesian) product

open _×_

-- proj₁ : A × B → A
-- proj₂ : A × B → B

{-
-- copattern matching
_,_ : A → B → A × B
proj₁ (a , b) = a
proj₂ (a , b) = b
-}

swap : A × B → B × A
proj₁ (swap x) = proj₂ x
proj₂ (swap x) = proj₁ x

-- combinator for functions using products ?

curry : (A × B → C) → (A → (B → C))
curry f a b = f (a , b)

uncurry : (A → B → C) → (A × B → C)
--uncurry g ab = g (proj₁ ab) (proj₂ ab)
uncurry g (a , b) = g a b

-- f : (A × B → C)
{- uncurry (curry f) (a , b)
   = curry f a b
   = f (a , b)

g : A → B → C
curry (uncurry g) a b
= uncurry g (a , b)
= g a b

isomorphism, isomorphic

C^(A × B) = (C^B)^A

-}

{-
How many elements ?


Bool ⊎ Fuzzy : 5 = 2 + 3

Bool × Fuzzy : 6 = 2 × 3

Bool → Fuzzy : 9 = 3^2

Fuzzy → Bool : 8 = 2^3

A → B as B^A
-}

bar : Bool → Fuzzy
bar false = {!!} -- 3
bar true = {!!} -- 3

xyz : Fuzzy → Bool
xyz true = {!!}
xyz false = {!!}
xyz maybe = {!!}


-- What is a combinator for sums.
-- A ⊎ B → C

case : (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

{-
paws : A ⊎ B → B ⊎ A
paws (inj₁ a) = inj₂ a
paws (inj₂ b) = inj₁ b
-}

paws-c : A ⊎ B → B ⊎ A
paws-c = case inj₂ inj₁ 

ccase : (A → C) × (B → C) → A ⊎ B → C
ccase = uncurry case

uncase : (A ⊎ B → C) → (A → C) × (B → C)
uncase f = (λ a → f (inj₁ a)) , λ b → f (inj₂ b)

-- C^(A + B) = C^A × C^B

-- there is one index law missing, which one and is it also an isomorphism ?

data ⊥ : Set where

case⊥ : ⊥ → A
case⊥ ()

-- A^0 = 1

record ⊤ : Set where
  constructor tt

tt' : ⊤
tt' = record {}

bb : ⊤ → Bool
bb tt = true
-- A^1 = A
