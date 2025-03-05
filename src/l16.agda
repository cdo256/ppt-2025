{-# OPTIONS --guardedness #-}
{- Lecture 15 COMP4074 -}

open import lib14
{-
Dependent types = types depending on values
(Dependent) Type Theory

Dependent type = Function into Set (= Type).

Set = type of (small) types

Vec : Set → ℕ → Set
Vec A n = lists over A of length n
[1,2,3] : Vec ℕ 3 

Fin : ℕ → Set
Fin n = { 0 , 1, .., n-1 }
Fin 0 = {}
Fin 1 = {0}
Fin 2 = {0 , 1}
Fin n contains n elements

List : Set → Set
List ℕ , ℕ : Set
polymorphic types vs proper dependent types
present in Haskell, haven't got Vec anf Fin
explanation of polymorphism
-}

{-
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
-}
data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

v123 : Vec ℕ 3  -- ℕ³
v123 = 1 ∷ 2 ∷ 3 ∷ []

-- dependent function type, Π-type
zeroes : (n : ℕ) → Vec ℕ n
zeroes zero = []
zeroes (suc n) = 0 ∷ zeroes n

{-
_++_ : List A → List A → List A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)
-}

_++v_ : {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++v bs = bs
(a ∷ as) ++v bs = a ∷ (as ++v bs)

{-
data ℕ : Set where -- \bN = ℕ
  zero : ℕ
  suc : ℕ → ℕ
-}

data Fin : ℕ → Set where 
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)
{-
Fin 0 = {]
Fin 1 = { zero {n = 0} }
Fin 2 = { zero {n = 1} , suc {n = 1} (zero {0})
-}
two3 : Fin 3
two3 = suc (suc zero)

fin0 : Fin 0 → ⊥
fin0 ()

max : {n : ℕ} → Fin (suc n)
max {zero} = zero
max {suc n} = suc (max {n})

emb : {n : ℕ} → Fin n → Fin (suc n)
emb (zero {n}) = zero {suc n}
emb (suc i) = suc (emb i)

inv : {n : ℕ} → Fin n → Fin n
inv zero = max
inv (suc i) = emb (inv i)

_!!_ : List A → ℕ → Maybe A
[] !! n = nothing
(a ∷ as) !! zero = just a
(a ∷ as) !! suc n = as !! n

-- can we fix it? With depedent types!
