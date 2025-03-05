{- Lecture 3 COMP4074.PPT -}

{-
functions A → B
functions with several inputs: currying
A → B → C, f a b
β (λ x → M) N = M[x := N]
(λx → x)[x := 3] = λx → x
(λ x → y + x)[y := x]
= (λ z → y + z)[y := x] -- α conversion
= (λ z → x + z)

η : x # M x doesn't (freely) occur in M
λ x → M x = M
-}

variable A B C : Set

id : A → A
id = λ x → x

-- λ x → λ y → M = λ x y → M

-- o X = 0
-- o (φ → ψ) = max (o φ + 1, o ψ)

-- C-c C-r = refine
_∘_ : (B → C) → (A → B) → A → C
_∘_ = λ f g x → f (g x)
--f ∘ g = λ x → f (g x)

-- Schönfinkel : combinators (capital letters) 
-- Curry : build on Schönfinkel

K : A → B → A
K = λ x y → x
--K x y = x

S : (A → B → C) → (A → B) → A → C
S f g = λ x → f x (g x)

-- Theorem : All pure lambda terms can be represented using only S,K
-- ie no λ , no variables!

-- λ f g x → f (g x)

CC : (B → C) → (A → B) → A → C
CC = S (K S) K
{-
λ f g x → f (g x)
= λ f g → λ x → f (g x)
= λ f g → S (λ x → f) (λ x → g x)
= λ f g → S (K f) g
= λ f → (λ g → S (K f) g)
= λ f → S (K f)
= S (λ f → S) (λ f → K f)
= S (K S) K
-}

I : A → A
I {A = A} = S K (K {B = A → A})
--I = λ x → x

