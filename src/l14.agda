{-# OPTIONS --guardedness #-}

open import lib11 public hiding (pred)

pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc n) = just n

con : Maybe ℕ → ℕ
con nothing = zero
con (just n) = suc n

-- inductive types generated from constructors
-- pred is the destructor derived from this.

-- lambek's lemma, every inductive types has a destructor that forms an isomorphism

-- co-inductive types
-- Views the destructor as the primitive operation.
-- conatural: ℕ∞


record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞

open ℕ∞

zero∞ : ℕ∞
pred∞ zero∞ =  nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = just n

∞ : ℕ∞
pred∞ ∞ = just ∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (n +∞ m) with pred∞ n
pred∞ (n +∞ m) | nothing = pred∞ m
pred∞ (n +∞ m) | just x = just (x +∞ m)

ℕ→ℕ∞ : ℕ → ℕ∞
ℕ→ℕ∞ zero = zero∞
ℕ→ℕ∞ (suc n) = suc∞ (ℕ→ℕ∞ n)

{-# TERMINATING #-} -- lie
ℕ∞→ℕ! : ℕ∞ → ℕ
ℕ∞→ℕ! n with pred∞ n
... | nothing = zero
... | just n' = suc (ℕ∞→ℕ! n')

x3+5 : ℕ
x3+5 = ℕ∞→ℕ! ((ℕ→ℕ∞ 3) +∞ (ℕ→ℕ∞ 5))

-- infinite list. Never finite.
record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream public

_∷s_ : A → Stream A → Stream A
hd (a ∷s as) = a
tl (a ∷s as) = as

from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

take : Stream A → ℕ → List A
take as zero = []
take as (suc n) = hd as ∷ take (tl as) n

fib : ℕ → ℕ → Stream ℕ
hd ( fib m n )  = m
tl ( fib m n )  = fib n (n + m)

{-
Co-recursion:
f : M → Stream A
m-hd : M → A
m-tl : M → M

hd (f x) = m-hd x
tl (f x) = f (m-tl x)

CoIt = unfold
CoIt creates the inductive type
-}

CoIt : (M → A) → (M → M) → M → Stream A
CoIt m-hd m-tl x .hd = m-hd x
CoIt m-hd m-tl x .tl = CoIt m-hd m-tl (m-tl x)

from-c : ℕ → Stream ℕ
from-c = CoIt (λ n → n) suc

fib-c : ℕ → ℕ → Stream ℕ
fib-c n m = CoIt (λ (n , m) → n) (λ (n , m) → (m , (n + m))) (n , m)

{-
inductive types
_×_

coinductive types
_⊎_
_→_ - because all you can do is apply it.
-}
