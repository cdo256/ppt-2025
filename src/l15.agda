{-# OPTIONS --guardedness #-} -- for coinduction

open import lib14

-- unfold creates streams from functions (CoIt)

-- fold creates functions to recurse a structure (It)
CoIt : (M → A) → (M → M) → M → Stream A
CoIt m-hd m-tl x .hd = m-hd x
CoIt m-hd m-tl x .tl = CoIt m-hd m-tl (m-tl x)

from-c : ℕ → Stream ℕ
from-c = CoIt (λ n → n) suc

fib-c : ℕ → ℕ → Stream ℕ
fib-c n m = CoIt (λ (n , m) → n) (λ (n , m) → (m , (n + m))) (n , m)

-- _+∞'_ : ℕ∞ → ℕ∞ → ℕ∞
-- pred∞ (n +∞' m) with pred∞ n
-- pred∞ (n +∞' m) | nothing = pred∞ m
-- -- Can't call functions since that would trigger (potentially) infinite recursion.
-- pred∞ (n +∞' m) | just x = pred∞ (x +∞' m)

-- Note that coinductive types don't specify the type itse, whereas inductive types do make that distinction.
-- There is a distinction between co-iterators constructing types and destructors, but they are very similar concepts

-- input to iterators : algebra
-- inputs to coiterators : coalgebra

CoItℕ∞ : (M → Maybe M) → M → ℕ∞
pred∞ (CoItℕ∞ f x) with f x
... | nothing = nothing
... | just y = just (CoItℕ∞ f y)

∞-ci : ℕ∞
∞-ci = CoItℕ∞ (λ x → just x) tt

CoRℕ∞ : (M → ℕ∞ ⊎ Maybe M) → M → ℕ∞
CoRℕ∞ f x .pred∞ with f x
... | inj₁ n = pred∞ n
... | inj₂ nothing = nothing
... | inj₂ (just y) = just (CoRℕ∞ f y)

caseMaybe : M → (A → M) → Maybe A → M
caseMaybe m-n m-j nothing = m-n
caseMaybe m-n m-j (just x) = m-j x

_+∞-cr_ : ℕ∞ → ℕ∞ → ℕ∞
m +∞-cr n = CoRℕ∞ (λ x → caseMaybe (inj₁ n) (λ m'+n → inj₂ (just m'+n)) (pred∞ x)) m


_+∞-ci_ : ℕ∞ → ℕ∞ → ℕ∞
_+∞-ci_ n m = CoItℕ∞ {!!} {!!}

--

postulate
  F : Set → Set
  mapF : (A → B) → F A → F B

{-# NO_POSITIVITY_CHECK #-}
data μF : Set where
  conF : F μF → μF

-- TODO
ItF : (F M → M) → μF → M
ItF f (conF x) = f (mapF {!It f!} {!x!})

{-# NO_POSITIVITY_CHECK #-}
record νF : Set where
  coinductive
  field
    out : F νF

{-# TERMINATING #-}
CoItF : (M → F M) → M → νF
CoItF f x = {!mapF (CoItF f) (f x)!}

-- HOMEWORK: Derive corecursor.
