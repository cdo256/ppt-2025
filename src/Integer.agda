{-# OPTIONS -WnoUnsupportedIndexedMatch --guardedness #-} -- for coinduction

module Integer where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_)
open import Nat
open import Relation.Binary.PropositionalEquality
open import Algebra.Definitions
open import Algebra.Structures {A = ℕ} _≡_
open import Algebra.Bundles using (CommutativeSemiring; CommutativeRing)
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Data.Nat.Base
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Consequences using (flip-Connex)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable using (True; via-injection; map′; recompute)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (fromEquivalence)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infix 10 _≡ℤ_
infixl 30 _+ℤ_
infixl 40 _*ℤ_
infixl 50 -ℤ_

infixl 6 _∘_

ℤ : Set
ℤ = ℕ × ℕ

private
  variable
    k- k+ l- l+ m- m+ n- n+ : ℕ
    k l m n : ℤ

data _≡ℤ_ : ℤ → ℤ → Set where
  eq : m+ + n- ≡ n+ + m-
     → (m+ , m-) ≡ℤ (n+ , n-)

zrefl : n ≡ℤ n
zrefl {(n+ , n-)} = eq refl

zsym : m ≡ℤ n → n ≡ℤ m 
zsym {(m+ , m-)} {(n+ , n-)} (eq mn) = eq (sym mn)

ztrans : l ≡ℤ m → m ≡ℤ n → l ≡ℤ n 
ztrans {(l+ , l-)} {(m+ , m-)} {(n+ , n-)} (eq lm) (eq mn) =
  eq (ℕ+-inj (m+ + m-) (l+ + n-) (n+ + l-)  
    (begin
      (m+ + m-) + (l+ + n-)
        ≡⟨ ℕ+-assoc m+ m- (l+ + n-) ⟩
      m+ + (m- + (l+ + n-))
        ≡⟨ ℕ+-cong (refl {x = m+}) (sym (ℕ+-assoc m- l+ n-)) ⟩
      m+ + ((m- + l+) + n-)
        ≡⟨ ℕ+-cong (refl {x = m+}) (ℕ+-commute (m- + l+) n-) ⟩
      m+ + (n- + (m- + l+))
        ≡⟨ sym (ℕ+-assoc m+ n- (m- + l+)) ⟩
      (m+ + n-) + (m- + l+)
        ≡⟨ ℕ+-cong (refl {x = (m+ + n-)}) (ℕ+-commute m- l+) ⟩
      (m+ + n-) + (l+ + m-)
        ≡⟨ ℕ+-cong mn lm ⟩
      (n+ + m-) + (m+ + l-)
        ≡⟨ ℕ+-assoc n+ m- (m+ + l-) ⟩
      n+ + (m- + (m+ + l-))
        ≡⟨ ℕ+-cong (refl {x = n+}) (sym (ℕ+-assoc m- m+ l-)) ⟩
      n+ + ((m- + m+) + l-)
        ≡⟨ ℕ+-cong (refl {x = n+}) (ℕ+-commute (m- + m+) l-) ⟩
      n+ + (l- + (m- + m+))
        ≡⟨ sym (ℕ+-assoc n+ l- (m- + m+)) ⟩
      (n+ + l-) + (m- + m+)
        ≡⟨ ℕ+-commute (n+ + l-) (m- + m+) ⟩
      (m- + m+) + (n+ + l-)
        ≡⟨ ℕ+-cong (ℕ+-commute m- m+) refl ⟩
      (m+ + m-) + (n+ + l-)
      ∎))

_∘_ = ztrans

ℤ-equiv : IsEquivalence _≡ℤ_
ℤ-equiv = record
  { refl = zrefl
  ; sym = zsym
  ; trans = ztrans
  }

ℤ-Setoid : Setoid 0ℓ 0ℓ
ℤ-Setoid = record
  { Carrier = ℤ
  ; _≈_ = _≡ℤ_
  ; isEquivalence = ℤ-equiv
  }

open Setoid ℤ-Setoid
  hiding (refl; sym; trans)

-- open import Relation.Binary.Reasoning.Base.Single _≈_ zrefl ztrans
--   as SingleRelReasoning

-- module ≡ℤ-Reasoning where
--   infix 1 begin_
--   infixr 2 _≡ℤ⟨⟩_ _≡ℤ⟨_⟩_
--   infix 3 _∎
-- 
--   begin≡ℤ_ : {m n : ℤ} → m ≡ℤ n → m ≡ℤ n
--   begin≡ℤ m≡ℤn = m≡ℤn
-- 
--   _≡ℤ⟨⟩_ : (m : ℤ) {n : ℤ} → m ≡ℤ n → m ≡ℤ n
--   m ≡ℤ⟨⟩ m≡ℤn = m≡ℤn
-- 
--   _≡ℤ⟨_⟩_ : (l : ℤ) {m n : ℤ} → l ≡ℤ m → m ≡ℤ n → l ≡ℤ n
--   m ≡ℤ⟨ l≡ℤm ⟩ m≡ℤn = ztrans l≡ℤm m≡ℤn
-- 
--   _∎ : (n : ℤ) → n ≡ℤ n
--   n ∎ = zrefl

-- open ≡ℤ-Reasoning


-ℤ_ : ℤ → ℤ
-ℤ (n+ , n-) = (n- , n+)

_+ℤ_ : ℤ → ℤ → ℤ
(m+ , m-) +ℤ (n+ , n-) = (m+ + n+ , m- + n-)

-- Alternative definition
-- _*ℤ_ : ℤ → ℤ → ℤ
-- (m+ , m-) *ℤ (n+ , n-) = mul m+ m-
--   where
--     mul : ℕ → ℕ → ℕ × ℕ
--     mul zero zero = (zero , zero)
--     mul zero (suc m-) = (n- , n+) +ℤ mul zero m-
--     mul (suc m+) zero  = (n+ , n-) +ℤ mul m+ zero
--     mul (suc m+) (suc m-) = mul m+ m-

_*ℤ_ : ℤ → ℤ → ℤ
(m+ , m-) *ℤ (n+ , n-) = (m+ * n+ + m- * n- , m+ * n- + m- * n+)

ℤCong : Set
ℤCong = (f : ℤ → ℤ) → (m n : ℤ) → m ≡ n → f m ≡ f n

ℤ--cong : Congruent₁ (_≡ℤ_) (-ℤ_)
ℤ--cong {(m+ , m-)} {(n+ , n-)} (eq mn) =
  eq (begin
    proj₂ (m+ , m-) + proj₁ (n+ , n-)
      ≡⟨ refl ⟩
    m- + n+
      ≡⟨ ℕ+-commute m- n+ ⟩
    n+ + m-
      ≡⟨ sym mn ⟩
    m+ + n-
      ≡⟨ ℕ+-commute m+ n- ⟩
    n- + m+
      ≡⟨ refl ⟩
    proj₂ (n+ , n-) + proj₁ (m+ , m-)
    ∎)

ℤ+-cong : Congruent₂ (_≡ℤ_) (_+ℤ_)
ℤ+-cong {(k+ , k-)} {(l+ , l-)} {(m+ , m-)} {(n+ , n-)} (eq kl) (eq mn) =
  eq (begin
    (k+ + m+) + (l- + n-)
      ≡⟨ ℕ+-assoc k+ m+ (l- + n-) ⟩
    k+ + (m+ + (l- + n-))
      ≡⟨ ℕ+-cong (refl {x = k+}) (ℕ+-cong (refl {x = m+}) (ℕ+-commute l- n-)) ⟩
    k+ + (m+ + (n- + l-))
      ≡⟨ ℕ+-cong (refl {x = k+}) (sym (ℕ+-assoc m+ n- l-)) ⟩
    k+ + ((m+ + n-) + l-)
      ≡⟨ ℕ+-cong (refl {x = k+}) (ℕ+-commute (m+ + n-) l-) ⟩
    k+ + (l- + (m+ + n-))
      ≡⟨ sym (ℕ+-assoc k+ l- (m+ + n-)) ⟩
    (k+ + l-) + (m+ + n-)
      ≡⟨ ℕ+-cong kl mn ⟩
    (l+ + k-) + (n+ + m-)
      ≡⟨ ℕ+-assoc l+ k- (n+ + m-) ⟩
    l+ + (k- + (n+ + m-))
      ≡⟨ ℕ+-cong (refl {x = l+}) (sym (ℕ+-assoc k- n+ m-)) ⟩
    l+ + ((k- + n+) + m-)
      ≡⟨ ℕ+-cong (refl {x = l+}) (ℕ+-cong (ℕ+-commute k- n+) (refl )) ⟩
    l+ + ((n+ + k-) + m-)
      ≡⟨ ℕ+-cong (refl {x = l+}) (ℕ+-assoc n+ k- m-) ⟩
    l+ + (n+ + (k- + m-))
      ≡⟨ (sym (ℕ+-assoc l+ n+ (k- + m-))) ⟩
    (l+ + n+) + (k- + m-)
    ∎)

0ℤ : ℤ
0ℤ = (zero , zero)

1ℤ : ℤ
1ℤ = (suc zero , zero)

ℤ+-ident : Identity _≡ℤ_ 0ℤ _+ℤ_
ℤ+-ident = left , right 
  where
    left : (n : ℤ) → 0ℤ +ℤ n ≡ℤ n
    left (n+ , n-) = eq refl
    right : (n : ℤ) → n +ℤ 0ℤ ≡ℤ n
    right (n+ , n-) = eq (begin
      (n+ + zero) + n-
        ≡⟨ ℕ+-cong (proj₂ ℕ+-ident n+) refl ⟩
      n+ + n-
        ≡⟨ ℕ+-cong refl (sym (proj₂ ℕ+-ident n-)) ⟩
      n+ + (n- + zero)
      ∎)
ℤ+-assoc : Associative _≡ℤ_ _+ℤ_
ℤ+-assoc (l+ , l-) (m+ , m-) (n+ , n-) = eq (begin
  ((l+ + m+) + n+) + (l- + (m- + n-))
                   ≡⟨ ℕ+-cong (ℕ+-assoc l+ m+ n+) (sym (ℕ+-assoc l- m- n-)) ⟩
  (l+ + (m+ + n+)) + ((l- + m-) + n-)
  ∎)

ℤ+-commute : Commutative _≡ℤ_ _+ℤ_
ℤ+-commute (m+ , m-) (n+ , n-) = eq (begin
  (m+ + n+) + (n- + m-)
                   ≡⟨ ℕ+-cong (ℕ+-commute m+ n+) (ℕ+-commute n- m- ) ⟩
  (n+ + m+) + (m- + n-)
  ∎)

ℤ+-inverse : Inverse _≡ℤ_ 0ℤ -ℤ_ _+ℤ_
ℤ+-inverse = left , right
  where
    left : (n : ℤ) → -ℤ n +ℤ n ≡ℤ 0ℤ 
    left (n+ , n-) = eq (begin
      (proj₁ (-ℤ (n+ , n-)) + n+) + 0
        ≡⟨ refl ⟩
      (proj₁ (n- , n+) + n+) + 0
        ≡⟨ refl ⟩
      (n- + n+) + 0
        ≡⟨ ℕ+-commute (n- + n+) 0 ⟩
      0 + (n-  + n+)
        ≡⟨ ℕ+-cong refl (ℕ+-commute n- n+) ⟩
      0 + (n+ + n-)
        ≡⟨ refl ⟩
      0 + (proj₂ (n- , n+) + n-)
        ≡⟨ refl ⟩
      0 + (proj₂ (-ℤ (n+ , n-)) + n-)
      ∎) 
    right : (n : ℤ) → n +ℤ -ℤ n ≡ℤ 0ℤ 
    right n = ℤ+-commute n (-ℤ n) ∘ left n

ℤ*-commute : Commutative _≡ℤ_ _*ℤ_
ℤ*-commute (m+ , m-) (n+ , n-) = eq ((
  begin
    (m+ * n+ + m- * n-) + (n+ * m- + n- * m+)
      ≡⟨ ℕ+-cong refl (ℕ+-commute (n+ * m-) (n- * m+)) ⟩
    (m+ * n+ + m- * n-) + (n- * m+ + n+ * m-)
      ≡⟨ ℕ+-cong (ℕ+-cong (ℕ*-commute m+ n+) (ℕ*-commute m- n-))
                 (ℕ+-cong (ℕ*-commute n- m+) (ℕ*-commute n+ m-)) ⟩
    (n+ * m+ + n- * m-) + (m+ * n- + m- * n+)
    ∎))

ℤ-distr-l : ((l+ , l-) (m+ , m-) (n+ , n-) : ℤ)
           →    (l+ , l-) *ℤ ((m+ , m-) +ℤ (n+ , n-))
             ≡ℤ (l+ , l-) *ℤ (m+ , m-) +ℤ (l+ , l-) *ℤ (n+ , n-) 
ℤ-distr-l (l+ , l-) (m+ , m-) (n+ , n-) = eq (begin
  (l+ * (m+ + n+ ) + l- * (m- + n-)) + ((l+ * m- + l- * m+) + (l+ * n- + l- * n+))
    ≡⟨ ℕ+-cong refl (ℕ+-assoc (l+ * m-) (l- * m+) (l+ * n- + l- * n+)) ⟩
  (l+ * (m+ + n+ ) + l- * (m- + n-)) + (l+ * m- + (l- * m+ + (l+ * n- + l- * n+)))
    ≡⟨ ℕ+-cong refl (ℕ+-cong refl (ℕ+-cong refl (ℕ+-commute (l+ * n-) (l- * n+)))) ⟩
  (l+ * (m+ + n+ ) + l- * (m- + n-)) + (l+ * m- + (l- * m+ + (l- * n+ + l+ * n-)))
    ≡⟨ ℕ+-cong refl (ℕ+-cong refl (ℕ+-assoc (l- * m+) (l- * n+) (l+ * n-))) ⟩
  (l+ * (m+ + n+ ) + l- * (m- + n-)) + (l+ * m- + ((l- * m+ + l- * n+) + l+ * n-))
    ≡⟨ ℕ+-cong refl (ℕ+-cong refl (ℕ+-commute (l- * m+ + l- * n+) (l+ * n-))) ⟩
  (l+ * (m+ + n+) + l- * (m- + n-)) + (l+ * m- + (l+ * n- + (l- * m+ + l- * n+)))
    ≡⟨  ℕ+-cong refl (sym (ℕ+-assoc (l+ * m-) (l+ * n-) (l- * m+ + l- * n+))) ⟩
  (l+ * (m+ + n+) + l- * (m- + n-)) + ((l+ * m- + l+ * n-) + (l- * m+ + l- * n+))
    ≡⟨ ℕ+-cong refl (ℕ+-cong (proj₂ ℕ-distr l+ m- n-) (proj₂ ℕ-distr l- m+ n+)) ⟩
  (l+ * (m+ + n+) + l- * (m- + n-)) + (l+ * (m- + n-) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong refl (ℕ+-commute (l+ * (m- + n-)) (l- * (m+ + n+))) ⟩
  (l+ * (m+ + n+) + l- * (m- + n-)) + (l- * (m+ + n+) + l+ * (m- + n-))
    ≡⟨ ℕ+-assoc (l+ * (m+ + n+ )) (l- * (m- + n- )) ((l- * (m+ + n+) + l+ * (m- + n-))) ⟩
  l+ * (m+ + n+) + (l- * (m- + n-) + (l- * (m+ + n+) + l+ * (m- + n-)))
    ≡⟨ ℕ+-cong refl (sym (ℕ+-assoc (l- * (m- + n-)) (l- * (m+ + n+)) (l+ * (m- + n-)))) ⟩
  l+ * (m+ + n+) + (((l- * (m- + n-) + l- * (m+ + n+))) + l+ * (m- + n-))
    ≡⟨ ℕ+-cong refl (ℕ+-cong (proj₂ ℕ-distr l- (m- + n-) (m+ + n+)) refl) ⟩
  l+ * (m+ + n+) + ((l- * ((m- + n-) + (m+ + n+))) + l+ * (m- + n-))
    ≡⟨ ℕ+-cong refl (ℕ+-commute (l- * ((m- + n-) + (m+ + n+))) (l+ * (m- + n-))) ⟩
  l+ * (m+ + n+) + (l+ * (m- + n-) + l- * ((m- + n-) + (m+ + n+)))
    ≡⟨ ℕ+-cong refl (sym (ℕ+-assoc (l+ * (m+ + n+)) (l+ * (m- + n-)) (l- * ((m- + n-) + (m+ + n+))))) ⟩
  (l+ * (m+ + n+) + l+ * (m- + n-)) + l- * ((m- + n-) + (m+ + n+))
    ≡⟨ ℕ+-cong (sym (proj₁ ℕ-distr l+ (m+ + n+) (m- + n-))) (ℕ*-cong refl (ℕ+-commute (m- + n-) (m+ + n+))) ⟩
  l+ * ((m+ + n+) + (m- + n-)) + l- * ((m+ + n+) + (m- + n-))
    ≡⟨ sym (proj₂ ℕ-distr ((m+ + n+) + (m- + n-)) l+ l-) ⟩
  (l+ + l-) * ((m+ + n+) + (m- + n-))
    ≡⟨ proj₁ ℕ-distr (l+ + l-) (m+ + n+) (m- + n-) ⟩
  (l+ + l-) * (m+ + n+) + (l+ + l-) * (m- + n-)
    ≡⟨ ℕ+-cong (proj₂ ℕ-distr (m+ + n+) l+ l-) (proj₂ ℕ-distr (m- + n-) l+ l-) ⟩
  (l+ * (m+ + n+) + l- * (m+ + n+)) + (l+ * (m- + n-) + l- * (m- + n-))
    ≡⟨ ℕ+-cong refl (ℕ+-commute (l- * (m- + n-)) (l+ * (m- + n-))) ⟩
  (l+ * (m+ + n+) + l- * (m+ + n+)) + (l- * (m- + n-) + l+ * (m- + n-))
    ≡⟨ ℕ+-assoc (l+ * (m+ + n+)) (l- * (m+ + n+)) (l- * (m- + n-) + l+ * (m- + n-)) ⟩
  l+ * (m+ + n+) + (l- * (m+ + n+) + (l- * (m- + n-) + l+ * (m- + n-)))
    ≡⟨ ℕ+-cong refl (ℕ+-commute (l- * (m+ + n+)) (l- * (m- + n-) + l+ * (m- + n-))) ⟩
  l+ * (m+ + n+) + ((l- * (m- + n-) + l+ * (m- + n-)) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong refl (ℕ+-cong (ℕ+-cong (ℕ*-cong refl (ℕ+-commute m- n-)) refl) refl) ⟩
  l+ * (m+ + n+) + ((l- * (n- + m-) + l+ * (m- + n-)) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong refl (ℕ+-assoc (l- * (n- + m-)) (l+ * (m- + n-)) (l- * (m+ + n+))) ⟩
  l+ * (m+ + n+) + (l- * (n- + m-) + (l+ * (m- + n-) + l- * (m+ + n+)))
    ≡⟨ sym (ℕ+-assoc (l+ * (m+ + n+)) (l- * (n- + m-)) (l+ * (m- + n-) + l- * (m+ + n+))) ⟩
  (l+ * (m+ + n+) + l- * (n- + m-)) + (l+ * (m- + n-) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong (ℕ+-cong (proj₁ ℕ-distr l+ m+ n+) (proj₁ ℕ-distr l- n- m-)) refl ⟩
  ((l+ * m+ + l+ * n+) + (l- * n- + l- * m-)) + (l+ * (m- + n-) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong (ℕ+-assoc (l+ * m+) (l+ * n+) (l- * n- + l- * m-)) refl ⟩
  (l+ * m+ + (l+ * n+ + (l- * n- + l- * m-))) + (l+ * (m- + n-) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong (ℕ+-cong refl (ℕ+-assoc (l+ * n+) (l- * n-) (l- * m-))) refl ⟩
  (l+ * m+ + ((l+ * n+ + l- * n-) + l- * m-)) + (l+ * (m- + n-) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong (ℕ+-cong refl (ℕ+-commute ((l+ * n+) + (l- * n-)) (l- * m-))) refl ⟩
  (l+ * m+ + (l- * m- + (l+ * n+ + l- * n-))) + (l+ * (m- + n-) + l- * (m+ + n+))
    ≡⟨ ℕ+-cong (sym (ℕ+-assoc (l+ * m+) (l- * m-) (l+ * n+ + l- * n-))) refl ⟩
  ((l+ * m+ + l- * m-) + (l+ * n+ + l- * n-)) + (l+ * (m- + n-) + l- * (m+ + n+))
  ∎)

ℤ*-cong-r : (l m n : ℤ)
          → m ≡ℤ n 
          → l *ℤ m ≡ℤ l *ℤ n 
ℤ*-cong-r (l+ , l-) (m+ , m-) (n+ , n-) (eq m≡n) = eq (begin
  (l+ * m+ + l- * m-) + (l+ * n- + l- * n+)
    ≡⟨ ℕ+-assoc (l+ * m+) (l- * m-) (l+ * n- + l- * n+) ⟩ 
  l+ * m+ + (l- * m- + (l+ * n- + l- * n+))
    ≡⟨ ℕ+-cong refl (sym (ℕ+-assoc (l- * m-) (l+ * n-) (l- * n+))) ⟩ 
  l+ * m+ + ((l+ * n- + l- * n+) + l- * m-)
    ≡⟨ ℕ+-cong refl (ℕ+-assoc (l+ * n-) (l- * n+) (l- * m+)) ⟩ 
  l+ * m+ + (l+ * n- + (l- * n+ + l- * m-))
    ≡⟨ sym (ℕ+-assoc (l+ * m+) (l+ * n-) (l- * n+ + l- * m-)) ⟩ 
  (l+ * m+ + l+ * n-) + (l- * n+ + l- * m-)
    ≡⟨ ℕ+-cong (sym (proj₁ ℕ-distr l+ m+ n-)) (sym (proj₁ ℕ-distr l- n+ m-)) ⟩ 
  l+ * (m+ + n-) + l- * (n+ + m-)
    ≡⟨ ℕ+-cong (ℕ*-cong refl m≡n) (ℕ*-cong refl (sym m≡n)) ⟩ 
  l+ * (n+ + m-) + l- * (m+ + n-)
    ≡⟨ ℕ+-cong (proj₁ ℕ-distr l+ n+ m-) (proj₁ ℕ-distr l- m+ n-) ⟩
  (l+ * n+ + l+ * m-) + (l- * m+ + l- * n-)
    ≡⟨ ℕ+-assoc (l+ * n+) (l+ * m-) (l- * m+ + l- * n-) ⟩ 
  l+ * n+ + (l+ * m- + (l- * m+ + l- * n-))
    ≡⟨ ℕ+-cong refl (sym (ℕ+-assoc (l+ * m-) (l- * m+) (l- * n-))) ⟩ 
  l+ * n+ + ((l+ * m- + l- * m+) + l- * n-)
    ≡⟨ ℕ+-cong refl (ℕ+-commute (l+ * m- + l- * m+) (l- * n-)) ⟩ 
  l+ * n+ + (l- * n- + (l+ * m- + l- * m+))
    ≡⟨ sym (ℕ+-assoc (l+ * n+) (l- * n-) (l+ * m- + l- * m+)) ⟩ 
  (l+ * n+ + l- * n-) + (l+ * m- + l- * m+)
  ∎)

ℤ*-cong-l : (l m n : ℤ)
          → l ≡ℤ m
          → l *ℤ n ≡ℤ m *ℤ n 
ℤ*-cong-l l m n l≡m =
     (ℤ*-commute l n)
   ∘ (ℤ*-cong-r n l m l≡m)
   ∘ (ℤ*-commute n m)

ℤ*-cong : Congruent₂ _≡ℤ_ _*ℤ_ 
ℤ*-cong {k} {l} {m} {n} k≡l m≡n = 
    ℤ*-cong-l k l m k≡l
  ∘ ℤ*-cong-r l m n m≡n

ℤ-distr : _DistributesOver_ _≡ℤ_ _*ℤ_ _+ℤ_ 
ℤ-distr = left , right 
  where
    left : (l m n : ℤ)
         →    l *ℤ (m +ℤ n)
           ≡ℤ l *ℤ m +ℤ l *ℤ n 
    left = ℤ-distr-l
    right : (l m n : ℤ)
          →    (m +ℤ n) *ℤ l 
            ≡ℤ m *ℤ l +ℤ n *ℤ l
    right l m n = 
        ℤ*-commute (m +ℤ n) l 
      ∘ ℤ-distr-l l m n
      ∘ (ℤ+-cong (ℤ*-commute l m) (ℤ*-commute l n)) 

ℤ*-assoc : Associative _≡ℤ_ _*ℤ_
ℤ*-assoc l@(l+ , l-) m@(m+ , m-) n@(n+ , n-) = eq (begin
  proj₁ ((l *ℤ m) *ℤ n) + proj₂ (l *ℤ (m *ℤ n))
                    ≡⟨ refl ⟩
  (proj₁ (l *ℤ m) * n+ +
   proj₂ (l *ℤ m) * n-) +
   (l+ * proj₂ (m *ℤ n) +
    l- * proj₁ (m *ℤ n))
                    ≡⟨ refl ⟩
  ((l+ * m+ + l- * m-) * n+ +
   (l+ * m- + l- * m+) * n-) +
   (l+ * (m+ * n- + m- * n+) +
    l- * (m+ * n+ + m- * n-))
                    ≡⟨ ℕ+-cong (ℕ+-cong (proj₂ ℕ-distr n+ (l+ * m+) (l- * m-))
                                        (proj₂ ℕ-distr n- (l+ * m-) (l- * m+)))
                               (ℕ+-cong (proj₁ ℕ-distr l+ (m+ * n-) (m- * n+))
                                        (proj₁ ℕ-distr l- (m+ * n+) (m- * n-))) ⟩
  (((l+ * m+) * n+ + (l- * m-) * n+) +
   ((l+ * m-) * n- + (l- * m+) * n-)) +
  ((l+ * (m+ * n-) + l+ * (m- * n+)) +
   (l- * (m+ * n+) + l- * (m- * n-)))
                    ≡⟨ ℕ+-cong (ℕ+-cong (ℕ+-cong (ℕ*-assoc l+ m+ n+) (ℕ*-assoc l- m- n+))
                                        (ℕ+-cong (ℕ*-assoc l+ m- n-) (ℕ*-assoc l- m+ n-)))
                               (ℕ+-cong (ℕ+-cong (sym (ℕ*-assoc l+ m+ n-)) (sym (ℕ*-assoc l+ m- n+)))
                                        (ℕ+-cong (sym (ℕ*-assoc l- m+ n+)) (sym (ℕ*-assoc l- m- n-)))) ⟩
  ((l+ * (m+ * n+) + l- * (m- * n+)) +
   (l+ * (m- * n-) + l- * (m+ * n-))) +
  (((l+ * m+) * n- + (l+ * m-) * n+) +
   ((l- * m+) * n+ + (l- * m-) * n-))
                    ≡⟨ ℕ+-cong (ℕ+-assoc (l+ * (m+ * n+)) (l- * (m- * n+))
                                         (l+ * (m- * n-) + l- * (m+ * n-)))
                               (sym (ℕ+-assoc ((l+ * m+) * n- + (l+ * m-) * n+)
                                              ((l- * m+) * n+) ((l- * m-) * n-))) ⟩
  (l+ * (m+ * n+) + (l- * (m- * n+) +
   (l+ * (m- * n-) + l- * (m+ * n-)))) +
  ((((l+ * m+) * n- + (l+ * m-) * n+) +
   (l- * m+) * n+) + (l- * m-) * n-)
                    ≡⟨ ℕ+-cong (ℕ+-cong refl (ℕ+-assoc (l- * (m- * n+))
                                        (l+ * (m- * n-)) (l- * (m+ * n-))))
                               (ℕ+-cong (ℕ+-assoc ((l+ * m+) * n-) ((l+ * m-) * n+)
                                        ((l- * m+) * n+)) refl) ⟩
  (l+ * (m+ * n+) + ((l- * (m- * n+) +
   l+ * (m- * n-)) + l- * (m+ * n-))) +
  (((l+ * m+) * n- + ((l+ * m-) * n+ +
   (l- * m+) * n+)) + (l- * m-) * n-)
                    ≡⟨ ℕ+-cong (ℕ+-cong refl (ℕ+-assoc (l- * (m- * n+)) 
                        (l+ * (m- * n-)) (l- * (m+ * n-))) ) refl ⟩
  (l+ * (m+ * n+) + (l- * (m- * n+)) +
   (l+ * (m- * n-) + l- * (m+ * n-))) +
  (((l+ * m+) * n- + ((l+ * m-) * n+ +
   (l- * m+) * n+)) + (l- * m-) * n-)
                    ≡⟨ ℕ+-cong (ℕ+-cong refl (ℕ+-commute (l- * (m- * n+))
                                        (l+ * (m- * n-) + l- * (m+ * n-))))
                               (ℕ+-cong (ℕ+-commute (l+ * m+ * n-)
                                        ((l+ * m-) * n+ + (l- * m+) * n+)) refl) ⟩
  (l+ * (m+ * n+) + ((l+ * (m- * n-) +
   l- * (m+ * n-)) + l- * (m- * n+))) +
  ((((l+ * m-) * n+ + (l- * m+) * n+) +
   (l+ * m+) * n-) + (l- * m-) * n-)
                    ≡⟨ ℕ+-cong (ℕ+-cong refl
                                        (ℕ+-assoc (l+ * (m- * n-)) (l- * (m+ * n-)) (l- * (m- * n+))))
                               refl ⟩
  (l+ * (m+ * n+) + (l+ * (m- * n-) +
   (l- * (m+ * n-) + l- * (m- * n+)))) +
  ((((l+ * m-) * n+ + (l- * m+) * n+) +
   (l+ * m+) * n-) + (l- * m-) * n-)
                    ≡⟨ ℕ+-cong (sym (ℕ+-assoc (l+ * (m+ * n+)) (l+ * (m- * n-))
                                              (l- * (m+ * n-) + l- * (m- * n+))))
                               (ℕ+-assoc ((l+ * m-) * n+ + (l- * m+) * n+)
                                        ((l+ * m+) * n-) ((l- * m-) * n-)) ⟩
  ((l+ * (m+ * n+) + l+ * (m- * n-)) +
   (l- * (m+ * n-) + l- * (m- * n+))) +
  (((l+ * m-) * n+ + (l- * m+) * n+) +
   ((l+ * m+) * n- + (l- * m-) * n-))
                    ≡⟨ ℕ+-cong (ℕ+-cong (sym (proj₁ ℕ-distr l+ (m+ * n+) (m- * n-)))
                                        (sym (proj₁ ℕ-distr l- (m+ * n-) (m- * n+))))
                               (ℕ+-cong (sym (proj₂ ℕ-distr n+ (l+ * m-) (l- * m+)))
                                        (sym (proj₂ ℕ-distr n- (l+ * m+) (l- * m-)))) ⟩
  (l+ * (m+ * n+ + m- * n-) +
   l- * (m+ * n- + m- * n+)) +
  ((l+ * m- + l- * m+) * n+ +
   (l+ * m+ + l- * m-) * n-)
                    ≡⟨ ℕ+-cong refl refl ⟩
  (l+ * proj₁ (m *ℤ n) + l- * proj₂ (m *ℤ n)) +
  (proj₂ (l *ℤ m) * n+ + proj₁ (l *ℤ m) * n-)
                    ≡⟨ ℕ+-cong refl refl ⟩
  proj₁ (l *ℤ (m *ℤ n)) + proj₂ ((l *ℤ m) *ℤ n) 
  ∎)

ℤ*-ident : Identity _≡ℤ_ 1ℤ _*ℤ_
ℤ*-ident = left , right
  where
    left : (n : ℤ) → 1ℤ *ℤ n ≡ℤ n 
    left (n+ , n-) = eq (begin
      (1 * n+ + 0 * n-) + n-
        ≡⟨ ℕ+-cong (ℕ+-cong (proj₁ ℕ*-ident n+) (proj₁ ℕ-zero n-)) refl ⟩
      (n+ + 0) + n-
        ≡⟨ ℕ+-cong (proj₂ ℕ+-ident n+) refl ⟩
      n+ + n-
        ≡⟨ ℕ+-cong refl (sym (proj₂ ℕ+-ident n-)) ⟩
      n+ + (n- + 0)
        ≡⟨ ℕ+-cong refl (ℕ+-cong (sym (proj₁ ℕ*-ident n-)) (sym (proj₁ ℕ-zero n+))) ⟩
      n+ + (1 * n- + 0 * n+)
      ∎)
    right : (n : ℤ) → n *ℤ 1ℤ ≡ℤ n
    right n = ℤ*-commute n 1ℤ ∘ left n
      
ℤ-zero : Zero _≡ℤ_ 0ℤ _*ℤ_
ℤ-zero = left , right
  where
    left : (n : ℤ) → 0ℤ *ℤ n ≡ℤ 0ℤ
    left (n+ , n-) = eq (begin
      (0 * n+ + 0 * n-) + 0
        ≡⟨ ℕ+-cong (ℕ+-cong (proj₁ ℕ-zero n+) (proj₁ ℕ-zero n-)) refl ⟩
      (0 + 0) + 0
        ≡⟨ ℕ+-assoc 0 0 0 ⟩
      0 + (0 + 0)
        ≡⟨ ℕ+-cong refl (ℕ+-cong (sym (proj₁ ℕ-zero n-)) (sym (proj₁ ℕ-zero n+))) ⟩
      0 + (0 * n- + 0 * n+)
      ∎) 
    right : (n : ℤ) → n *ℤ 0ℤ ≡ℤ 0ℤ 
    right n = ℤ*-commute n 0ℤ ∘ left n

ℤ-CommutativeRing : CommutativeRing 0ℓ 0ℓ
ℤ-CommutativeRing = record
  { Carrier = ℤ
  ; _≈_ = _≡ℤ_
  ; _+_ = _+ℤ_
  ; _*_ = _*ℤ_
  ; -_ = -ℤ_
  ; 0# = 0ℤ
  ; 1# = 1ℤ
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = record
                  { refl = zrefl
                  ; sym = zsym
                  ; trans = ztrans
                  }
                ; ∙-cong = {!ℤ+-cong!}
                }
              ; assoc = ℤ+-assoc
              }
            ; identity = ℤ+-ident
            }
          ; inverse = ℤ+-inverse ;
          ⁻¹-cong = ℤ--cong
          }
        ; comm = ℤ+-commute
        }
      ; *-cong = ℤ*-cong
      ; *-assoc = ℤ*-assoc
      ; *-identity = ℤ*-ident
      ; distrib = ℤ-distr
      }
    ; *-comm = ℤ*-commute
    }
  }
