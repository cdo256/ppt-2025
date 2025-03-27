{-# OPTIONS --guardedness #-}
{- Lecture 22 COMP4074 -}

open import lib21
{-
Types for programs
Types for proofs

sort : List ℕ → List ℕ
--
Sorted : List ℕ → Prop
Perm : List ℕ → List ℕ → Set

sortSorts : (l : ℕ) → Sorted (sort l)
permSort : (l : ℕ) → Perm l (sort l)


equality

-}
variable l m n : ℕ

eqℕ : ℕ → ℕ → Bool
eqℕ zero zero = true
eqℕ zero (suc n) = false
eqℕ (suc m) zero = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕok : m ≡ n ⇔ eqℕ m n ≡ true
eqℕok = {!!}

-- (m ≡ n) ∨ ¬ (m ≡ n)
-- Dec A = A ∨ ¬ A = EM A

-- decidable vs decided
data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

no-conf : ¬ (zero ≡ suc n)
no-conf ()

injSuc : suc m ≡ suc n → m ≡ n
injSuc refl = refl

_≡?_ : (m n : ℕ) → Dec (m ≡ n)
zero ≡? zero = yes refl
zero ≡? suc n = no no-conf
suc m ≡? zero = no (λ p → no-conf (sym p))
suc m ≡? suc n with m ≡? n
... | yes p = yes (cong suc p)
... | no np = no (λ mn → np (injSuc mn))

-- _≡_ : ℕ → ℕ → Set is decidable
-- (m n : ℕ) → Dec (m ≡ n)
-- are all equalities decidable ?
-- are there undecidable predicates ?
-- halting problem : Halts : ℕ → Set
-- (m : ℕ) → Dec (Halts m)    = Decidable Halts
-- ¬ ((m : ℕ) → Dec (Halts m)) = ¬ (Decidable Halts)
-- -> ¬ EM
-- Church's thesis (CT) : all functions ℕ → ℕ are computable.
-- computable f = there exists a TM which computes f
-- CT → ¬ EM
-- CT : all functions are computable
-- EM : all propositions are decidable
-- _≡_ {A = ℕ → Bool}


