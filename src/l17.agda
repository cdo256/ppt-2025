{-# OPTIONS --guardedness #-} -- for coinduction

open import lib16

_!!_ : List A → ℕ → Maybe A
[] !! n = nothing
(x ∷ xs) !! zero = just x
(x ∷ xs) !! (suc n) = xs !! n

variable m n : ℕ

_!!v_ : Vec A n → Fin n → A
(a ∷ as) !!v zero = a
(a ∷ as) !!v (suc n) = as !!v n

{-
dependent functions
A : Set, B : A → Set -- family
(x : A) → B x -- dependent funciton Π-type
-}

Π : (A : Set)(B : A → Set) → Set
Π A B = (x : A) → B x

-- ∈ means the same as :
syntax Π A (λ x → B) = Π[ x ∈ A ] B

_→'_ : Set → Set → Set
A →' B = Π[ _ ∈ A ] B

record Σ(A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁ -- depending on the first projection

open Σ

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

FlexVec : Set → Set
FlexVec A = Σ[ n ∈ ℕ ] (Vec A n)

fv123 : FlexVec ℕ
fv123 = 3 , ((1 ∷ 2 ∷ 3 ∷ []))

[]v : FlexVec A
[]v = 0 , []

_∷v_ : A → FlexVec A → FlexVec A
(x ∷v (n , xs)) = (suc n) , (x ∷ xs)

list→fv : List A → FlexVec A
list→fv [] = []v
list→fv (x ∷ xs) = x ∷v (list→fv xs)

fv→list : FlexVec A → List A
fv→list (zero , []) = []
fv→list ((suc n) , (x ∷ xs)) = x ∷ (fv→list (n , xs))

-- × is the non-dependent type of Σ
-- → is the non-dependent type of Π

-- × can be simulated by using Π with Bool
-- ⊎ can be simulated by using Σ with Bool

-- To get all types, need 0 (empty), 1 (unit), 2, Id (for equality), W and M -- look in to

If_Then_Else : Bool → Set → Set → Set
If false Then x Else y = y
If true Then x Else y = x

_⊎'_ : Set → Set → Set
A ⊎' B = Σ[ x ∈ Bool ] (If x Then A Else B)

inj₁' : A → A ⊎' B
inj₁' x = true , x

inj₂' : B → A ⊎' B
inj₂' x = false , x

_×''_ : Set → Set → Set
A ×'' B = Π[ x ∈ Bool ] (If x Then A Else B)

proj₁' : A ×'' B → A
proj₁' f = f true

proj₂' : A ×'' B → B
proj₂' f = f false

