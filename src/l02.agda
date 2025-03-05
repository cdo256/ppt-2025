{- COMP4074 Lecture 2 -}

open import Data.Nat

-- What is a function from A to B
-- Set theory : R ⊆ A × B
-- s.t. ∀ a ∈ A, ∃! b : B, (a,b) ∈ R
-- Type Theory : functions are primitive
-- but relations are derived R : A → B → Prop

-- C-c C-l load

f : ℕ → ℕ  -- ℕ = \bN → =\to
f x = x + 2 -- a shed
-- C-c C-,    show type  
-- C-c C-SPC  check shed
-- C-c C-n    evaluate expression

{-
f 3
= (x + 2)[x := 3]
= 3 + 2
= 5
-}

n : ℕ
n = 4

-- λ = \Gl
f' : ℕ → ℕ
f' = λ x → 2 + x
{-
f' 3
= (λ x → 2 + x) 3  -- unfolding defn of f'
= (2 + x)[x := 3]  -- β reduction
= 2 + 3
= 5
-}

-- (λ x → M) N = M[ x := N ] -- β-reduction

-- how to define a function with several parameters
-- currying g' : ℕ × ℕ → ℕ
-- → is right-associative A → B → C = A → (B → C)
g : ℕ → ℕ → ℕ
g = λ x → λ y → x + y

-- g 2 : ℕ → ℕ
-- g 2 3 : ℕ

-- application is left associative
-- L M N = (L M) N

module _(y : ℕ) where

  tst : ℕ → ℕ
  tst = g y

{-
g y
= (λ x → λ y → x + y) y
= (λ y → x + y) [ x := y]
-- = (λ y → y + y) ???   -- name capture
= (λ z → x + z) [ x := y]
= (λ z → y + z)

(λ y → x + y) = (λ z → x + z) -- α-conversion
-}

-- λ x → M = λ y → M[x := y]

-- a higher order function
h : (ℕ → ℕ) → ℕ
h = λ k → k (k 3) 
{-
h f'
= (λ k → k (k 3))(λ x → 2 + x) -- unfolding definitions
= (k (k 3))[ k := λ x → 2 + x]
= (λ x → 2 + x) (( λ x → 2 + x) 3)
= (λ x → 2 + x) ((2 + x) [x := 3])
= (λ x → 2 + x) (2 + 3)
= (λ x → 2 + x) 5
= (2 + x)[x := 5]
= 2 + 5
= 7 
-}

{-
foo : ℕ → ℕ
foo = λ → λ
foo = 17
-}






