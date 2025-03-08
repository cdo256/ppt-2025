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
map-v : {A B : Set} → {n : ℕ} → (A → B) → (Vec A n → Vec B n)
map-v f [] = []
map-v f (x ∷ xs) = f x ∷ (map-v f xs)

_*v_ : {n : ℕ} → ℕ → Vector n → Vector n
_*v_ x = map-v (λ y → y * x)

test1 : Vector 3
test1 = 2 *v v1
{- 2 ∷ 4 ∷ 6 ∷ [] -}

{- addition of vectors -}
_+v_ : {n : ℕ} → Vector n → Vector n → Vector n
_+v_ [] [] = []
_+v_ (x ∷ xs) (y ∷ ys) = (x + y) ∷ (xs +v ys)

test2 : Vector 3
test2 = v1 +v v2
{- 3 ∷ 5 ∷ 3 ∷ [] -}

zeros : {n : ℕ} → Vector n
zeros {zero} = []
zeros {suc n} = zero ∷ zeros {n}

{- multiplication of a vector and a matrix 

This is usually done the other way around, but in our representation this one is easier. 
-}

_·_ : {n : ℕ} → Vector n → Vector n → ℕ
[] · [] = 0
(x ∷ xs) · (y ∷ ys) = (x * y) + (xs · ys)

_*vm_ : {m n : ℕ} → Vector m → Matrix m n → Vector n
_*vm_ {zero} {n} [] [] =  zeros
_*vm_ {suc m} {n} (x ∷ xs) (ys ∷ yss) = (x *v ys) +v (xs *vm yss)

test3 : Vector 2
test3 = v1 *vm m4
{- 30 ∷ 36 ∷ [] -}

test4 : Vector 3
test4 = v1 *vm m3
{- 30 ∷ 36 ∷ 42 ∷ [] -}

{- matrix multiplication -}
_*mm_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
[] *mm _ = []
(xs ∷ xss) *mm yss = (xs *vm yss) ∷ (xss *mm yss)

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

-- {- Part 2 : The transposition of a matrix, here we swap columns and rows.-}

repeat-v : {A : Set} → {n : ℕ} → A → Vec A n
repeat-v {A} {zero} x = []
repeat-v {A} {suc n} x = x ∷ (repeat-v {A} {n} x)

append-mv : {m n : ℕ} → Matrix m n → Vector m → Matrix m (suc n)
append-mv [] [] = []
append-mv (xs ∷ xss) (y ∷ ys) =
  (y ∷ xs) ∷ append-mv xss ys

transpose : {m n : ℕ} → Matrix m n → Matrix n m
transpose [] = repeat-v []
transpose (xs ∷ xss) = append-mv (transpose xss) xs

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
    -- eq₁ : ψ ∘ φ ≡ id
    -- eq₂ : φ ∘ ψ ≡ id

open _≅_ public

-- Just some practice :)
refl : {A : Set} → A ≅ A
refl .φ = λ x → x
refl .ψ = λ x → x

sym : {A B : Set} → A ≅ B → B ≅ A
sym ab .φ = ψ ab
sym ab .ψ = φ ab

trans : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
trans ab bc .φ = λ a → (φ bc (φ ab a))
trans ab bc .ψ = λ c → (ψ ab (ψ bc c))

infixl 30 _∘̰_
_∘̰_ : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
_∘̰_ = trans

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

-- Σℕ n f = f 0 + f 1 + ... + f n
-- {-
{- Derive the isomorphism for Σ

   Hint: plus-eq may come in handy. -}

{-
  Fin (Σℕ (suc n) f)
= (definition of Σℕ)
  Fin (f 0 + (Σℕ n (λ x → f (suc x))))
≅ (plus-eq)
  Fin (f 0) ⊎ Fin (Σℕ n (λ x → f (suc x)))
≅ (recurse Σiso)
  Fin (f 0) ⊎ Σ (Fin n) (λ x → Fin (f (suc x)) x)
≅ (cases)
  Σ (Fin (suc n)) (λ x → Fin (f x))
-}

lift-⊎ : {A B A' B' : Set} → A ≅ A' → B ≅ B' → (A ⊎ B) ≅ (A' ⊎ B')
φ (lift-⊎ a≅a' b≅b') (inj₁ a) = inj₁ (φ a≅a' a)
φ (lift-⊎ a≅a' b≅b') (inj₂ b) = inj₂ (φ b≅b' b)
ψ (lift-⊎ a≅a' b≅b') (inj₁ a') = inj₁ (ψ a≅a' a')
ψ (lift-⊎ a≅a' b≅b') (inj₂ b') = inj₂ (ψ b≅b' b')

fin0≅⊥ : Fin 0 ≅ ⊥
φ fin0≅⊥ ()
ψ fin0≅⊥ ()

Σ∅≅⊥ : {F : Fin 0 → Set} → Σ (Fin 0) F ≅ ⊥
φ Σ∅≅⊥ ()
ψ Σ∅≅⊥ ()

Σiso : (n : ℕ)(f : Fin n → ℕ) →
  Fin (Σℕ n f) ≅ Σ (Fin n) (λ x → Fin (f x))
Σiso zero f = fin0≅⊥ ∘̰ sym Σ∅≅⊥
Σiso (suc n) f = sym plus-eq ∘̰ lift-⊎ refl recurse ∘̰ cases
  where
    recurse : Fin (Σℕ n (λ x → f (suc x))) ≅
           Σ (Fin n) (λ x → Fin (f (suc x)))
    recurse = Σiso n (λ x → f (suc x))
    cases : (Fin (f zero) ⊎ Σ (Fin n) (λ x → Fin (f (suc x)))) ≅
            Σ (Fin (suc n)) (λ x → Fin (f x))
    φ cases (inj₁ z) = (zero , z)
    φ cases (inj₂ (i , z)) = (suc i , z)
    ψ cases (zero , z) = inj₁ z
    ψ cases (suc i , z) = inj₂ (i , z)

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
-- -}

lift-× : {A B A' B' : Set} → A ≅ A' → B ≅ B' → (A × B) ≅ (A' × B')
φ (lift-× a≅a' b≅b') (a , b) = (φ a≅a' a , φ b≅b' b)
ψ (lift-× a≅a' b≅b') (a' , b') = (ψ a≅a' a' , ψ b≅b' b')

distr-l : {A B C : Set} → ((A ⊎ B) × C) ≅ ((A × C) ⊎ (B × C))
φ distr-l (inj₁ a , c) = inj₁ (a , c)
φ distr-l (inj₂ b , c) = inj₂ (b , c)
ψ distr-l (inj₁ (a , c)) = inj₁ a , c
ψ distr-l (inj₂ (b , c)) = inj₂ b , c

distr-r : {A B C : Set} → (C × (A ⊎ B)) ≅ ((C × A) ⊎ (C × B))
φ distr-r (c , inj₁ a) = inj₁ (c , a)
φ distr-r (c , inj₂ b) = inj₂ (c , b)
ψ distr-r (inj₁ (c , a)) = c , inj₁ a
ψ distr-r (inj₂ (c , b)) = c , inj₂ b


Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero f = 1
Πℕ (suc n) f = f zero * Πℕ n (λ x → f (suc x))

{-
   (Fin (suc m) × Fin n)
 ≅ (def of +)
   (Fin (m + 1) × Fin n)
 ≅ (plus-eq)
   (Fin m ⊎ Fin 1) × Fin n
 ≅ (distr x over ⊎)
   (Fin m × Fin n) ⊎ (Fin 1 × Fin n)
 ≅ (Fin 1)
   (Fin m × Fin n) ⊎ Fin n
 ≅ (recurse)
   Fin (m * n) ⊎ Fin n
 ≅ (plus-eq)
   Fin (m * n + n)
 ≅ (1 is identity over *)
   Fin (m * n + 1 * n)
 ≅ (* distributes over +)
   Fin ((m + 1) * n)
 = (def of +)
   Fin ((suc m) * n)
-}

×⊥ : (⊥ × A) ≅ ⊥
φ ×⊥ ()
ψ ×⊥ ()

×1 : (Fin 1 × A) ≅ A
φ ×1 (zero , x) = x
ψ ×1 x = (zero , x)

×0 : (Fin 0 × A) ≅ Fin 0
-- ×0 = lift-× fin0≅⊥ refl ∘̰ ×⊥ ∘̰  sym fin0≅⊥
φ ×0 (() , _)
ψ ×0 ()

mul-eq : (Fin m × Fin n) ≅ Fin (m * n)
mul-eq {m = zero} = ×0
mul-eq {m = suc m'} =
    lift-× (sym plus-eq) refl
  ∘̰ distr-l
  ∘̰ lift-⊎ ×1 mul-eq
  ∘̰ plus-eq

{-
  Fin (Πℕ (suc n) f)
= (definition of Πℕ)
  Fin (f 0 * (Πℕ n (λ x → f (suc x))))
≅ (mul-eq)
  Fin (f 0) × Fin (Πℕ n (λ x → f (suc x)))
≅ (recurse Πiso)
  Fin (f 0) × Π (Fin n) (λ x → Fin (f (suc x)) x)
≅ ?
  Π (Fin (suc n)) (λ x → Fin (f x))
-}


Πiso : (n : ℕ)(f : Fin n → ℕ) →
  Fin (Πℕ n f) ≅ Π (Fin n) (λ x → Fin (f x))
φ (Πiso zero f) zero ()
ψ (Πiso zero f) _ = zero
Πiso (suc n) f = sym mul-eq ∘̰ lift-× refl (Πiso n (λ x → f (suc x))) ∘̰ join
    where
      join : (Fin (f zero) × Π (Fin n) (λ x → Fin (f (suc x)))) ≅
        Π (Fin (suc n)) (λ x → Fin (f x))
      join .φ (a , g) = λ {zero → a ; (suc b) → g b}
      join .ψ g = g zero , λ x → g (suc x)

{- some test cases -}
g : Fin 3 → ℕ
g x = (suc (fin→ℕ x))
tpiso1 : Π (Fin 3) λ x → Fin (g x)
tpiso1 = φ (Πiso 3 g) (ψ (Πiso 3 g) λ x → zero) 
  -- where
  --  f : Π (Fin 3) (λ x → Fin (fin→ℕ x))
  --  f zero = suc (suc (suc zero))
  --  f (suc zero) = suc (suc (suc (suc zero)))
  --  f (suc (suc zero)) = zero

-- tpiso2 : Fin (Πℕ 5 fin→ℕ)
-- tpiso2 = ψ (Πiso 5 fin→ℕ) (φ (Πiso 5 fin→ℕ) (suc (suc zero)))
