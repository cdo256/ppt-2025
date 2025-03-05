{- Lecture 09 COMP4074 -}

open import lib09 public

dbl : ℕ → ℕ
dbl zero = zero 
dbl (suc x) = suc (suc (dbl x))

{-
f : ℕ → M

M : Set
M = Motive 

f zero = m-z
f (suc n) = m-s (f n)

Methods
m-z : M
m-s : M → M
-}

variable M : Set

-- Iterator
It : M → (M → M) → ℕ → M
It m-z m-s zero = m-z
It m-z m-s (suc n) = m-s (It m-z m-s n)

-- eliminator
-- fold , catamorphism

dbl-i : ℕ → ℕ
dbl-i = It zero λ n → suc (suc n)

half-i-aux : ℕ → ℕ × ℕ
-- half-i-aux n = (half n, half (suc n))
half-i-aux = It {M = ℕ × ℕ} (0 , 0)
                λ hn_hsn → (proj₂ hn_hsn) , (suc (proj₁ hn_hsn))

half-i : ℕ → ℕ
half-i n = proj₁ (half-i-aux n)

_+-i_ : ℕ → (ℕ → ℕ)
_+-i_ = It {M = ℕ → ℕ} (λ n → n) λ m+ n → suc (m+ n)

_*-i_ : ℕ → ℕ → ℕ
_*-i_ = It {M = ℕ → ℕ} (λ n → zero) (λ m* n → n +-i (m* n))


_!-aux : ℕ → ℕ × ℕ
-- !-aux n = (n , n !)
_!-aux = It {M = ℕ × ℕ} (0 , 1)
  λ n_n! → (suc (proj₁ n_n!)) , (suc (proj₁ n_n!) *-i (proj₂ n_n!)) 

_!-i : ℕ → ℕ
_!-i n = proj₂ (n !-aux)

{-
f : ℕ → M

M : Set
M = Motive 

f zero = m-z
f (suc n) = m-s n (f n)

Methods
m-z : M
m-s : ℕ → M → M
-}
-- the recursor
RR : M → (ℕ → M → M) → ℕ → M
RR m-z m-s zero = m-z
RR m-z m-s (suc n) = m-s n (RR m-z m-s n)
-- what is Meertens greek word for recursor

_!-r : ℕ → ℕ
_!-r = RR {M = ℕ} 1 (λ n n! → (suc n) * n!)

-- Can we define the recursor from the iterator?
-- just apply the method we used for !-i

-- simplified Ackermann
ack-s : ℕ → ℕ → ℕ → ℕ
ack-s zero m n = suc n
ack-s (suc l) m zero = m
ack-s (suc l) m (suc n) = ack-s l m (ack-s (suc l) m n)

-- Question : can we derive ack-s from It?
