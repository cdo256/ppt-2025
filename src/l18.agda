{-# OPTIONS --guardedness #-} -- for coinduction

open import lib17

infixl 5 _⊎_
infixl 2 _≅_

record _≅_ (A B : Set) : Set where
  field
    ϕ : A → B
    ψ : B → A
    -- ϕψ : ϕ ∘ ψ ≡ id
    -- ψϕ : ψ ∘ ϕ ≡ id\psi

open _≅_

variable n m : ℕ

-- Fin_inj : {n m : ℕ} → {leq : n ≤ m} → 

-- 'f' is for finite
inj₁-f : Fin m → Fin (m + n)
inj₁-f zero = zero
inj₁-f (suc i') = suc (inj₁-f i')

inj₂-f : Fin n → Fin (m + n)
inj₂-f {m = zero} i = i
inj₂-f {m = suc m'} i = suc (inj₂-f {m = m'} i)

case-f : {A : Set} → (Fin m → A) → (Fin n → A) → (Fin (m + n) → A)
case-f {m = zero} f g x = g x
case-f {m = suc m'} f g zero = f zero
case-f {m = suc m'} f g (suc x) = case-f (λ y → f (suc y)) g x

+-iso : Fin m ⊎ Fin n ≅ Fin (m + n)
+-iso .ϕ (inj₁ x) = inj₁-f x
+-iso .ϕ (inj₂ x) = inj₂-f x
+-iso .ψ = case-f inj₁ inj₂

_₂ : Fin m × Fin n ≅ Fin (m * n)
_₃ : {m n : ℕ} → Fin m → Fin n ≅ Fin (n ^ m)

Σ-f : (m : ℕ)(f  : Fin m → ℕ) → ℕ
Σ-f zero f = zero
Σ-f (suc m) f = f zero + Σ-f m (λ x → f (suc x))

-- prove Σ-iso : Fin (Σ-f m f) ≅ Σ[ i ∈ Fin m ] (Fin (f i))
Σ-iso : {f : Fin m → ℕ} → Fin (Σ-f m f) ≅ Σ[ i ∈ Fin m ] (Fin (f i))
Σ-iso {m = zero} = {!!}

t1 : ℕ
t1 = Σ-f {!5!} {!(λ x → 2 * (fin→ℕ x))!}
