{-# OPTIONS --guardedness #-} -- for coinduction

open import lib20 
open import Agda.Builtin.Sigma
open import Algebra.Bundles
open import Algebra.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.Core
open import Level

-- record Monoid : {A : Set}
--               → {e : A}
--               → {_⋆_ : A → A → A}
--               → Set₁ where
--   field
--     id₁ : {x : A} → e ⋆ x ≡ x
--     id₂ : {x : A} → x ⋆ e ≡ x
--     assoc : {x y z : A} → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)
-- 

ℕ-equiv : IsEquivalence _≡_
ℕ-equiv = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

ℕ+-cong : Congruent₂ _≡_ _+_
ℕ+-cong {x} {y} {u} {v} xy uv =
  trans (cong (λ z → x + z) uv)
        (cong (λ z → z + v) xy)

ℕ+-assoc : Associative _≡_ _+_
ℕ+-assoc zero y z = refl
ℕ+-assoc (suc x) y z =
        -- (((suc x) + y) + z)
  trans (cong (λ w → w + z) refl)
        -- ((suc (x + y)) + z)
    (trans refl
        -- (suc ((x + y) + z))
        (trans (cong ℕ.suc (ℕ+-assoc x y z))
        -- (suc (x + (y + z)))
        refl)) 
        -- (suc x + (y + z))

ℕ+-commute : Commutative _≡_ _+_
ℕ+-commute zero zero = refl
ℕ+-commute zero (suc y) =
  cong ℕ.suc (ℕ+-commute ℕ.zero y)
ℕ+-commute (suc x) zero =
  cong ℕ.suc (ℕ+-commute x ℕ.zero)
ℕ+-commute (suc x) (suc y) =
  cong ℕ.suc (trans (ℕ+-commute x (ℕ.suc y))
             (trans (cong ℕ.suc (ℕ+-commute y x))
                    (ℕ+-commute (ℕ.suc x) y)))

ℕ+Monoid : Monoid 0ℓ 0ℓ 
ℕ+Monoid = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _∙_ = _+_
  ; ε = ℕ.zero
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ℕ-equiv
        ; ∙-cong = ℕ+-cong
        }
      ; assoc = ℕ+-assoc 
      }
    ; identity = (λ _ → refl) , λ x → {!ℕ+-commute x ℕ.zero!}
    }


  }

