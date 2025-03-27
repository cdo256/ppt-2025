{-# OPTIONS --guardedness #-}
{- Lecture 21 COMP4074 -}

open import lib20

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- this is a retract = 1/2 isomorphism

retract : (n : ℕ) → half (double n) ≡ n
retract zero = refl
retract (suc n) = cong suc (retract n)

{-
section : (n : ℕ) → double (half n) ≡ n
section zero = refl
section (suc zero) = {!!}
section (suc (suc n)) = {!!}
-}

-- induction = recursion with dependent types

{-
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
-}


-- what are the algebraic properties of addition?
--
-- a monoid (ℕ,0,+) :
-- left neutral : 0 + m ≡ m
-- right neutral : m + 0 ≡ m
-- associative : (l + m) + n ≡ l + (m + n)
-- a commutative monoid = monoid +
-- commutative : m + n ≡ n + m

lneutr : (m : ℕ) → 0 + m ≡ m
lneutr m = refl

rneutr : (m : ℕ) → m + 0 ≡ m
rneutr zero = refl
rneutr (suc m) = cong suc (rneutr m)

assoc : (l m n : ℕ) → (l + m) + n ≡ l + (m + n)
assoc zero m n = refl
assoc (suc l) m n = cong suc (assoc l m n)

comm-suc : (m n : ℕ) → suc (n + m) ≡ n + suc m
comm-suc m zero = refl
comm-suc m (suc n) = cong suc (comm-suc m n)

comm : (m n : ℕ) → m + n ≡ n + m
comm zero n = sym (rneutr n)
comm (suc m) n = trans (cong suc (comm m n)) (comm-suc m n)
{-
suc (m + n) ≡
suc (n + m) ≡
n + suc m
-}

-- recursion combinator
{-
M : ℕ → Set
f (n : ℕ) → M n
m-z : M zero
m s : (n : ℕ) → M n → M (suc n)
f zero = m-z
f (suc n) = m-s n (f n)

dependent recursor = eliminator
-}
Elim : (M : ℕ → Set)
     → M zero
     → ((m : ℕ) → M m → M (suc m))
     → (n : ℕ) → M n
Elim M m-z m-s zero = m-z
Elim M m-z m-s (suc n) = m-s n (Elim M m-z m-s n)

-- Elim -> It , RR
-- -> induction

retract-E : (n : ℕ) → half (double n) ≡ n
retract-E = Elim (λ n → half (double n) ≡ n) refl (λ n r-n → cong suc r-n)

