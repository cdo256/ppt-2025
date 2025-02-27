{-# OPTIONS --guardedness #-}
open import lib11 public

data Ord : Set where
  zero : Ord
  suc : Ord → Ord
  lim : (ℕ → Ord) → Ord

T-Ord : Set → Set
T-Ord  X = ⊤ ⊎ (X ⊎ (ℕ → X))

emb : ℕ → Ord
emb zero = zero
emb (suc n) = suc (emb n)

ω : Ord
ω = lim emb

_+Ord_ : Ord → Ord → Ord
α +Ord zero = α
α +Ord suc β = suc (α +Ord β)
α +Ord lim x = {!!}

{-
let f : (A → A) → A
    f' : A → (A → A)
    f o f' = id
    f' o f = id
WTS A =~ 1
Suppose A finite then n = |A → A| = n^n so n^(n-1) = 1 thus n = 1
If A infinite. Then 
Take a, b in A
Have Let (x1, y1), (x2, y2) st f (x1 , y1) = f (x2 , y2)
Can use domain theory
-}

-- Can create non-terminating types. And allows you to prove ⊥
{-# NO_POSITIVITY_CHECK #-}

-- Unityped
data Λ : Set where
  ƛ : (Λ → Λ) → Λ

id-Λ : Λ
id-Λ = ƛ (λ x → x)

infixl 10 _$_
_$_ : Λ → Λ → Λ
_$_ (ƛ f) x = f x

S-Λ : Λ
S-Λ = ƛ (λ f → ƛ (λ g → ƛ (λ x → f $ x $ (g $ x))))

self-apply : Λ
self-apply = ƛ (λ x → x $ x)

Ω : Λ
Ω = self-apply $ self-apply

-- System F (Jean-Yves Girard)
data Reynolds : Set where
  weird : ((Reynolds → Bool) → Bool) → Reynolds

F-Reynolds : Set → Set
F-Reynolds X = (X → Bool) → Bool

F-Reynolds-map : (A → B) → F-Reynolds A → F-Reynolds B
F-Reynolds-map f x = {!!}

-- Reynolds - Positive but not strictly positive
-- every functor that admits an initial algebra is strictly positive?
-- Powerset functor F : 
-- Which functors admit initial algebras are a research area.
