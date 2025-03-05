{- Lecture 09 COMP4074 -}

open import lib08 public

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A
-- Maybe X = ⊤ ⊎ X

pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc n) = just n

zs : Maybe ℕ → ℕ
zs nothing = zero
zs (just n) = suc n

-- pred ∘ zs = id
-- zs ∘ pred = id
-- Hence : ℕ ≅ Maybe ℕ
-- Q : Are there other types X, s.t. X ≅ Maybe X
-- and X ≇ ℕ .

-- recursion

dbl : ℕ → ℕ
dbl zero = zero 
dbl (suc x) = suc (suc (dbl x))

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- dbl (half 1) = 2
-- half (dbl x) = x
-- retract (half isomorphism)

infixl 0 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-
foo : ℕ → ℕ
foo n = suc (foo n)
-}

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


infix 3 _^^_

_^^_ : ℕ → ℕ → ℕ
m ^^ zero = 1
m ^^ suc n = m ^ m ^^ n

-- Ackermann function

ack : ℕ → ℕ → ℕ → ℕ
-- ack 1 m n = m + n  0 + n = n
-- ack 2 m n = m * n  0 * n = 0
-- ack 3 m n = n ^ m  n ^ 0 = 1
-- ...


ack zero m n = suc n
ack (suc zero) zero n = n
ack (suc (suc zero)) zero n = zero
ack (suc (suc (suc l))) zero n = 1
ack (suc l) (suc m) n = ack l n (ack (suc l) m n)
-- eg ack 2 (suc m) n = ack 1 n (ack 2 m n) = n + (m * n)

fast : ℕ → ℕ
fast n = ack n n n
-- how far can you compute fast
