{- Lecture 04 COMP4074 -}

module lib04 where

open import lib02

variable A B C : Set

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

{-
Given a term M : B using a variable x : A
with no λ but variables and S,K
we can derive a term
λ* x → M : A → B
of the same kind, ie no λ but variables + S,K
(deduction theorem)

We show this by induction over M.

λ* x → x = I = S K K

λ* x → y = K y

λ* x → M N = S (λ* x → M) (λ* x → N)

λ* x → S = K S

λ* x → K = K K

(λ* x → M N) L
= (M N)[x := L]
= (M [x := L]) (N [x := L])

(S (λ* x → M) (λ* x → N)) L
= (λ* x → M) L ((λ* x → N) L)   -- eqn for S
= M [x:=L] (N [x := L])

Optimisation rules
x # M -- x does not appear in M

λ* x → M = K M

λ* x → y z
= S (K y) (K z)  -- stupid
= K (y z)        -- clever


λ* x → M x = M

λ* x → y x
= S (K y) I      -- stupid
= y              -- clever

To prove theorem: Every pure lambda term can be represnetd
using oly S, K we apply the deduction theorem starting with
the innermost λ-abstraction.

-}

AA : (A → B → C) → (B → A → C)
AA = S (S (K S) (S (K K) S)) (K K)
--λ f b a → f a b
{-
λ f b a → (f a) b
= λ f b → S (λ a → f a) (λ a → b)
= λ f b → (S f) (K b)
= λ f → S (λ b → S f) (λ b → K b)
= λ f → (S (K (S f))) K
= λ f → S (λ f → (S (K (S f)))) (λ f → K)
= S (λ f → S (K (S f))) (K K)
= S (S (K S) (λ f → K (S f))) (K K)
= S (S (K S) (S (K K) (λ f → S f))) (K K)
= S (S (K S) (S (K K) S)) (K K)
-}


{-
Sums and products
 + ⊎ = \uplus , disjoint union, sum, coproduct
 ⊥ = \bot, empty sum, ∅
 × = \times, (cartesian) product
 ⊤ = unit type, tt : ⊤
combinators on types

sums = labelled sums
products = records
-}

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

open import Data.Bool

data Fuzzy : Set where
  true false maybe : Fuzzy

-- Bool ⊎ Fuzzy
-- inj₁ true

-- pattern matching
bool→fuzzy : Bool → Fuzzy
bool→fuzzy false = false
bool→fuzzy true = true

foo : Bool ⊎ Fuzzy → Fuzzy
foo (inj₁ b) = bool→fuzzy b
foo (inj₂ f) = f

x : Bool ⊎ Fuzzy
x =  inj₂ true
--x =  inj₁ true
-- Bool = { true,false }, Fuzzy = {true , false, maybe}
-- Bool ∪ Fuzzy = { true , false , maybe }
-- Bool ⊎ Fuzzy = {inj₁ true , inj₁ false, inj₂ true, inj₂ false, inj₂ maybe }
-- Bool' = { tt , ff}
-- Bool' ∪ Fuzzy = { tt , ff , true , false , maybe }
-- Bool' ⊎ Fuzzy {inj₁ tt , inj₁ ff, inj₂ true, inj₂ false, inj₂ maybe }
-- No ∪ , only ⊎

record _×_ (A B : Set) : Set where
  field
    proj₁ : A
    proj₂ : B

open _×_

-- proj₁ : A × B → A
-- proj₂ : A × B → B

-- copattern matching
_,_ : A → B → A × B
proj₁ (a , b) = a
proj₂ (a , b) = b
