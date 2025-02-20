{- 
Library for COMP4074.PPT

upto lecture 10
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
