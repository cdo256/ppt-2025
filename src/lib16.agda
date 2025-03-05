{-# OPTIONS --guardedness #-} -- for coinduction
{- 
Library for COMP4074.PPT

upto lecture 14
-}

{- products and sums -}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

variable
  A B C : Set

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b) -- C-c C-,
uncurry : (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

data _⊎_(A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

uncase : (A ⊎ B → C) → (A → C) × (B → C)
uncase f = (λ a → f (inj₁ a)) , λ b → f (inj₂ b)

case' : (A → C) × (B → C) → (A ⊎ B → C)
case' = uncurry case

-- Bool

data Bool : Set where
  false : Bool
  true : Bool

if_then_else_ : Bool → A → A → A
if false then x else y = y
if true then x else y = x

-- propositional logic

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

case⊥ : ⊥ → A
case⊥ ()

Prop = Set

infix 3 _∧_
_∧_ : Prop → Prop → Prop
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : Prop → Prop → Prop
P ∨ Q = P ⊎ Q

infix 1 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

infix 0 _⇔_
_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

True : Prop
True = ⊤

False : Prop
False = ⊥

¬_ : Prop → Prop
¬ P = P ⇒ False

variable P Q R : Prop

--- classical logic

TND : Prop → Prop
TND P = P ∨ ¬ P

RAA : Prop → Prop
RAA P = ¬ ¬ P → P

tnd→raa : TND P → RAA P
tnd→raa (inj₁ p) h = p
tnd→raa (inj₂ np) h = case⊥ (h np)

nntnd : ¬ ¬ (TND P)
nntnd h = h (inj₂ (λ p → h (inj₁ p)))

raa→tnd : RAA (P ∨ ¬ P) → TND P
raa→tnd h = h nntnd

infixl 2 _∨ᶜ_
_∨ᶜ_ : Prop → Prop → Prop
P ∨ᶜ Q = ¬ (¬ P ∧ ¬ Q)

-- Nat

data ℕ : Set where -- \bN = ℕ
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc m) = just m

infixl 0 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 1 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) * n !

infixr 2 _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * m ^ n

--- iterator and recursor for ℕ

variable M : Set

-- Iterator
It : M → (M → M) → ℕ → M
It m-z m-s zero = m-z
It m-z m-s (suc n) = m-s (It m-z m-s n)

RR : M → (ℕ → M → M) → ℕ → M
RR m-z m-s zero = m-z
RR m-z m-s (suc n) = m-s n (RR m-z m-s n)

-- Lists

infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A -- \::  

_++_ : List A → List A → List A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

ItList : M → (A → M → M) → List A → M
ItList m-nil m-cons [] = m-nil
ItList m-nil m-cons (a ∷ as) = m-cons a (ItList m-nil m-cons as)

-- Conatural numbers

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞

open ℕ∞ public

zero∞ : ℕ∞
pred∞ zero∞ = nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = just n

∞ : ℕ∞
pred∞ ∞ = just ∞


_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m +∞ n) with pred∞ m
pred∞ (m +∞ n) | nothing = pred∞ n
pred∞ (m +∞ n) | just m' = just (m' +∞ n)



ℕ→ℕ∞ : ℕ → ℕ∞
ℕ→ℕ∞ zero = zero∞ 
ℕ→ℕ∞ (suc n) = suc∞ (ℕ→ℕ∞ n)

{-# TERMINATING #-} -- a lie
ℕ∞→ℕ! : ℕ∞ → ℕ
ℕ∞→ℕ! n with pred∞ n
... | nothing = zero
... | just n' = suc (ℕ∞→ℕ! n')

record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    hd : A
    tl : Stream A

-- destructors
-- hd : Stream A → A
-- tl : Stream A → Stream A

open Stream public

from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

take : Stream A → ℕ → List A
take as zero = []
take as (suc n) = hd as ∷ take (tl as) n

fib : ℕ → ℕ → Stream ℕ
hd (fib m n) = m
tl (fib m n) = fib n (n + m)

-- vectors

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

_++v_ : {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++v bs = bs
(a ∷ as) ++v bs = a ∷ (as ++v bs)

data Fin : ℕ → Set where 
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

max : {n : ℕ} → Fin (suc n)
max {zero} = zero
max {suc n} = suc (max {n})

emb : {n : ℕ} → Fin n → Fin (suc n)
emb (zero {n}) = zero {suc n}
emb (suc i) = suc (emb i)

inv : {n : ℕ} → Fin n → Fin n
inv zero = max
inv (suc i) = emb (inv i)
