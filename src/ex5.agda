{- Exercise 05 Proofs,Programs and Types (PPT) -}
{-# OPTIONS --guardedness #-}

open import lib17
{- Exercise 05

Part 1 - 60%
Part 2 - 20%
Part 3 - 20%

General advice: Don't try to be efficient!
Feel free to ask questions on moodle.

-}

{- Part 1: vectors and matrices 

We implement some basic operations on vectors and matrices.

If you don't know this or have forgotten it see for example: 
https://mathinsight.org/matrix_vector_multiplication
-}

Vector : ℕ → Set {- Vec n is an n-dimensional vector -}
Vector m = Vec ℕ m

{- some example vectors -}
v1 : Vector 3
v1 = 1 ∷ 2 ∷ 3 ∷ []

v2 : Vector 3
v2 = 2 ∷ 3 ∷ 0 ∷ []

{- A matrix is a vector of vectors. -}
Matrix : ℕ → ℕ → Set {- Matrix m n is an m x n Matrix -}
Matrix m n = Vec (Vector n) m

{- Some example of matrices -}
id3 : Matrix 3 3
id3 = (1 ∷ 0 ∷ 0 ∷ []) 
    ∷ (0 ∷ 1 ∷ 0 ∷ []) 
    ∷ (0 ∷ 0 ∷ 1 ∷ []) 
    ∷ []

inv3 : Matrix 3 3
inv3 = (0 ∷ 0 ∷ 1 ∷ []) 
     ∷ (0 ∷ 1 ∷ 0 ∷ []) 
     ∷ (1 ∷ 0 ∷ 0 ∷ []) 
     ∷ []

m3 : Matrix 3 3
m3 = (1 ∷ 2 ∷ 3 ∷ []) 
    ∷ (4 ∷ 5 ∷ 6 ∷ []) 
    ∷ (7 ∷ 8 ∷ 9 ∷ []) 
    ∷ []

m4 : Matrix 3 2
m4 = (1 ∷ 2 ∷ []) 
    ∷ (4 ∷ 5 ∷ []) 
    ∷ (7 ∷ 8 ∷ []) 
    ∷ []

{- multiplication of a scalar (a number) with a vector -}
_*v_ : {n : ℕ} → ℕ → Vector n → Vector n
_*v_ = {!!}

test1 : Vector 3
test1 = 2 *v v1
{- 2 ∷ 4 ∷ 6 ∷ [] -}

{- addition of vectors -}
_+v_ : {n : ℕ} → Vector n → Vector n → Vector n
_+v_ = {!!}

test2 : Vector 3
test2 = v1 +v v2
{- 3 ∷ 5 ∷ 3 ∷ [] -}

zeros : {n : ℕ} → Vector n
zeros {zero} = []
zeros {suc n} = zero ∷ zeros {n}

{- multiplication of a vector and a matrix 

This is usually done the other way around, but in our representation this one is easier. 
-}
_*vm_ : {m n : ℕ} → Vector m → Matrix m n → Vector n
_*vm_ = {!!}

test3 : Vector 2
test3 = v1 *vm m4
{- 30 ∷ 36 ∷ [] -}

test4 : Vector 3
test4 = v1 *vm m3
{- 30 ∷ 36 ∷ 42 ∷ [] -}

{- matrix multiplication -}
_*mm_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
_*mm_ = {!!}

test5 : Matrix 3 3
test5 = inv3 *mm m3
{-
(7 ∷ 8 ∷ 9 ∷ []) ∷ 
(4 ∷ 5 ∷ 6 ∷ []) ∷ 
(1 ∷ 2 ∷ 3 ∷ []) ∷ []
-}

test6 : Matrix 3 2
test6 = m3 *mm m4
{-
(30 ∷ 36 ∷ []) ∷ 
(66 ∷ 81 ∷ []) ∷ 
(102 ∷ 126 ∷ []) ∷ []
-}

test7 : Matrix 3 3
test7 = m3 *mm m3
{-
(30 ∷ 36 ∷ 42 ∷ []) ∷
(66 ∷ 81 ∷ 96 ∷ []) ∷
(102 ∷ 126 ∷ 150 ∷ [])
∷ []
-}

{- Part 2 : The transposition of a matrix, here we swap columns and rows.-}

transpose : {m n : ℕ} → Matrix m n → Matrix n m
transpose = {!!}

test8 : Matrix 2 3
test8 = transpose m4
{-
(1 ∷ 4 ∷ 7 ∷ []) ∷ 
(2 ∷ 5 ∷ 8 ∷ []) ∷ []
-}

test9 : Matrix 3 3
test9 = transpose m3
{-
(1 ∷ 4 ∷ 7 ∷ []) ∷ 
(2 ∷ 5 ∷ 8 ∷ []) ∷ 
(3 ∷ 6 ∷ 9 ∷ []) ∷ []
-}

{- Part 3 : The Sigma isomorphism (hard) -}

{- as an example here is the isomorphism for binary sum which we will done in the lecture. -}

record _≅_ (A B : Set) : Set where
  field
    φ : A → B -- \phi
    ψ : B → A -- \psi
    --eq₁ : ψ ∘ φ ≡ id
    --eq₂ : φ ∘ ψ ≡ id

open _≅_ public

variable m n : ℕ

inj₁f : Fin m → Fin (m + n)
inj₁f {.(suc _)} {n} zero = zero
inj₁f {.(suc _)} {n} (suc x) = suc (inj₁f x)

inj₂f : Fin n → Fin (m + n)
inj₂f {m = zero} i = i
inj₂f {m = suc m} i = suc (inj₂f i)

{-
case : (A → C) → (B → C) → (A ⊎ B → C)
-}
case-f : (Fin m → C) → (Fin n → C)
         → (Fin (m + n) → C)
case-f {m = zero} f g x = g x
case-f {m = suc m} f g zero = f zero
case-f {m = suc m} f g (suc x) =
       case-f {m = m} (λ i → f (suc i)) g x

plus-eq : (Fin m ⊎ Fin n) ≅ Fin (m + n)
φ (plus-eq {m} {n}) (inj₁ x) = inj₁f x
φ (plus-eq {m} {n}) (inj₂ y) = inj₂f y
ψ (plus-eq {m} {n}) z = case-f inj₁ inj₂ z

{- The definition of Σ for sequences of numbers. -}

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero f = 0
Σℕ (suc n) f = f zero + Σℕ n (λ x → f (suc x))

{- Derive the isomorphism for Σ

   Hint: plus-eq may come in handy. -}

Σiso : (n : ℕ)(f : Fin n → ℕ) → Fin (Σℕ n f) ≅ Σ (Fin n) λ x → Fin (f x)
Σiso = {!!}

{- some test cases -}

fin→ℕ : Fin n → ℕ
fin→ℕ zero = zero
fin→ℕ (suc i) = suc (fin→ℕ i)

tiso1 : Σ (Fin 5) λ x → Fin (fin→ℕ x)
tiso1 = φ (Σiso 5 fin→ℕ) (ψ (Σiso 5 fin→ℕ) (suc (suc (suc zero)) , suc zero)) 
-- suc (suc (suc zero)) , suc zero

tiso2 : Fin (Σℕ 5 fin→ℕ)
tiso2 = ψ (Σiso 5 fin→ℕ) (φ (Σiso 5 fin→ℕ) (suc (suc zero)))
-- suc (suc zero)

{- If you still don't feel challenged, do Π as well. -}
