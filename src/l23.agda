{-# OPTIONS --guardedness #-}
{- Lecture 23 COMP4074 -}

open import lib22

-- ≤ : ℕ → ℕ → Set / Prop
-- m ≤ n = ∃[ i ∈ ℕ ] (i + m ≡ n)
-- m ≤' n = ∃[ i ∈ ℕ ] (m + i ≡ n)

data _≤_ : ℕ → ℕ → Set where
  le-0 : 0 ≤ n
  le-SS : m ≤ n → suc m ≤ suc n

le13 : 1 ≤ 3
le13 = le-SS le-0

nle32 : ¬ (3 ≤ 1)
nle32 (le-SS ())

-- what are the properties of ≤ ?
-- reflexive, transitive => preorder
-- antisymmetric m ≤ n → n ≤ m → m = n : partial order
-- total : m ≤ n ∨ n ≤ m
-- decidable
-- p q : m ≤ n → p ≡ q , isProp 

refl≤ : (m : ℕ) → m ≤ m
refl≤ zero = le-0
refl≤ (suc m) = le-SS (refl≤ m)

trans≤ : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
trans≤ 0 m n le-0 mn = le-0
trans≤ (suc l) (suc m) (suc n) (le-SS lm) (le-SS mn)
       = le-SS (trans≤ l m n lm mn)

antisym : m ≤ n → n ≤ m → m ≡ n
antisym le-0 le-0 = refl
antisym (le-SS mn) (le-SS nm) = cong suc (antisym mn nm)

leb : ℕ → ℕ → Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

leSS-inv : suc m ≤ suc n → m ≤ n
leSS-inv (le-SS mn) = mn

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes le-0
suc m ≤? zero = no λ ()
suc m ≤? suc n with m ≤? n
... | yes mn = yes (le-SS mn)
... | no ¬mn = no λ smsn → ¬mn (leSS-inv smsn)

data _≤'_ : ℕ → ℕ → Set where
  le'-refl : m ≤' m
  le'-S : m ≤' n → m ≤' suc n

le'-0 : 0 ≤' n
le'-0 {zero} = le'-refl
le'-0 {suc n} = le'-S (le'-0 {n = n})

le'-SS : m ≤' n → suc m ≤' suc n
le'-SS le'-refl = le'-refl
le'-SS (le'-S mn) = le'-S (le'-SS mn)

le-S : m ≤ n → m ≤ suc n
le-S le-0 = le-0
le-S (le-SS mn) = le-SS (le-S mn)

le⇔le' : m ≤ n ⇔ m ≤' n
proj₁ le⇔le' le-0 = le'-0
proj₁ le⇔le' (le-SS mn) = le'-SS (proj₁ le⇔le' mn)
proj₂ le⇔le' le'-refl = refl≤ _
proj₂ le⇔le' (le'-S mn) = le-S (proj₂ le⇔le' mn)

isProp≤ : (p q : m ≤ n) → p ≡ q
isProp≤ le-0 le-0 = refl
isProp≤ (le-SS p) (le-SS q) = cong le-SS (isProp≤ p q)

data _≤''_ : ℕ → ℕ → Set where
  le-0 : 0 ≤'' n
  le-SS : m ≤'' n → suc m ≤'' suc n
  le''-S : m ≤'' n → m ≤'' suc n  
-- m ≤' n = Δi (suc m) (suc n)
