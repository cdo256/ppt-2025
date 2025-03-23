{-# OPTIONS -WnoUnsupportedIndexedMatch --guardedness #-} -- for coinduction

module Integer2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_)
open import Nat
open import Relation.Binary.PropositionalEquality
open import Algebra.Definitions
open import Algebra.Structures {A = ℕ} _≡_

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Algebra.Bundles using (Magma; Semigroup; CommutativeSemigroup;
  CommutativeMonoid; Monoid; Semiring; CommutativeSemiring; CommutativeSemiringWithoutOne)
open import Algebra.Definitions.RawMagma using (_,_)
open import Algebra.Morphism

open import Algebra.Consequences.Propositional
  using (comm+cancelˡ⇒cancelʳ; comm∧distrʳ⇒distrˡ; comm∧distrˡ⇒distrʳ)
open import Algebra.Construct.NaturalChoice.Base
  using (MinOperator; MaxOperator)
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp as LatticeMinMaxOp
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties using (T?)
open import Data.Nat.Base
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (inj₁; inj₂; _⊎_; [_,_]′)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_; flip; _$_; id; _∘′_; _$′_)
open import Function.Bundles using (_↣_)
open import Level using (0ℓ)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core
  using (_⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Consequences using (flip-Connex)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable using (True; via-injection; map′; recompute)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (fromEquivalence)

open Relation.Binary.PropositionalEquality.≡-Reasoning
-- open import Relation.Binary.Reasoning.Syntax
--   using (module ≈-syntax)

open import Function.Bundles
  using (_↔_)

infix 10 _≡ℤ_
infixl 30 _+ℤ_ _-ℤ_
infixl 40 _*ℤ_
infixl 50 -ℤ_

ℤ : Set
ℤ = ℕ × ℕ

infix 5 _≡0

data _≡0 : ℤ → Set where
  eq0 : {n+ n- : ℕ}
      → n+ ≡ n-
      → (n+ , n-) ≡0

-ℤ_ : ℤ → ℤ
-ℤ (n+ , n-) = (n- , n+)

_+ℤ_ : ℤ → ℤ → ℤ
(m+ , m-) +ℤ (n+ , n-) = (m+ + n+ , m- + n-)

_-ℤ_ : ℤ → ℤ → ℤ
m -ℤ n = m +ℤ -ℤ n 

_*ℤ_ : ℤ → ℤ → ℤ
(m+ , m-) *ℤ (n+ , n-) = (m+ * n+ + m- * n- , m+ * n- + m- * n+)

data _≡ℤ_ : ℤ → ℤ → Set where
  eq : {m+ m- n+ n- : ℕ}
     → m+ + n- ≡ n+ + m-
     → (m+ , m-) ≡ℤ (n+ , n-)

0ℤ : ℤ
0ℤ = (zero , zero)

1ℤ : ℤ
1ℤ = (suc zero , zero)

0≡→≡0 : (n : ℤ) → (n ≡ℤ 0ℤ) → (n ≡0)
0≡→≡0 (n+ , n-) (eq n≡0) = eq0 (
  trans (sym (proj₂ ℕ+-ident n+))
        n≡0)

≡0→0≡ : (n : ℤ) → (n ≡0) → (n ≡ℤ 0ℤ)
≡0→0≡ (n+ , n-) (eq0 n≡0) = eq (
  trans (proj₂ ℕ+-ident n+)
        n≡0)

zrefl : {n : ℤ} → n ≡ℤ n
zrefl {(n+ , n-)} = eq refl

zsym : {m n : ℤ} → m ≡ℤ n → n ≡ℤ m 
zsym {(m+ , m-)} {(n+ , n-)} (eq mn) = eq (sym mn)

ztrans : {l m n : ℤ} → l ≡ℤ m → m ≡ℤ n → l ≡ℤ n 
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

{-

open Setoid ℤ-Setoid
  hiding (refl; sym; trans)

-- open import Relation.Binary.Reasoning.Base.Single _≈_ zrefl ztrans
--   as SingleRelReasoning

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

ℤ-distr : (_DistributesOver_) (_≡ℤ_) (_*ℤ_) (_+ℤ_) 
ℤ-distr = left , right 
  where
    left : ((l+ , l-) (m+ , m-) (n+ , n-) : ℤ)
         →    (l+ , l-) *ℤ ((m+ , m-) +ℤ (n+ , n-))
           ≡ℤ (l+ , l-) *ℤ (m+ , m-) +ℤ (l+ , l-) *ℤ (n+ , n-) 
    left (l+ , l-) (m+ , m-) (n+ , n-) = eq (begin
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
    right : ((l+ , l-) (m+ , m-) (n+ , n-) : ℤ)
          →    ((m+ , m-) +ℤ (n+ , n-)) *ℤ (l+ , l-)
            ≡ℤ (m+ , m-) *ℤ (l+ , l-) +ℤ (n+ , n-) *ℤ (l+ , l-)
    right = {! begin
      ?
        ≈⟨ ? ⟩
      ?
      ∎!}
       


-- ℕ*-cong : Congruent₂ (_≡ℤ_) (_*ℤ_)
-- ℕ*-cong {x} {y} {u} {v} xy uv =
--   trans (cong (λ z → x * z) uv)
--         (cong (λ z → z * v) xy)
-- ℤ*-cong : Congruent₂ (_≡ℤ_) (_*ℤ_)
-- ℤ*-cong {(k+ , k-)} {(l+ , l-)} {(m+ , m-)} {(n+ , n-)} (eq kl) (eq mn) = eq (
--   begin
--     (k+ * m+ + k- * m-) + (l+ * n- + l- * n+)
--       ≡⟨ {!!} ⟩
--     (k+ * m+ + k- * m-) + (l+ * n- + l- * n+) + 
--       ≡⟨ {!!} ⟩
--     (l+ * n+ + l- * n-) + (k+ * m- + k- * m+)
--     ∎)

{-
  l- * m- + l+ * m- + l- * m+ + l+ * m+
+ k- * n- + k+ * n- + k- * n+ * k+ * n+ 
+ k+ * m+ + k- * m- + l+ * n- + l- * n+
= l- * (m- + m+ + n+) + l+ + (m- + m+ + n-)
+ k- * (n- + n+ + m-) + k+ + (n- + n+ + m+)
= l- * (m+ + m+ + n-) + l+ + (m- + m+ + n-)
+ k- * (n- + n- + m+) + k+ + (n+ + n+ + m-)
-}

-- ℕ*-commute : Commutative _≡_ _*_
-- ℕ*-commute zero zero = refl
-- ℕ*-commute zero (suc y) = ℕ*-commute ℕ.zero y
-- ℕ*-commute (suc x) zero = ℕ*-commute x ℕ.zero 
-- ℕ*-commute (suc x) (suc y) = begin
--   ℕ.suc x * ℕ.suc y
--                      ≡⟨ refl ⟩
--   ℕ.suc y + x * ℕ.suc y 
--                      ≡⟨ ℕ+-cong refl (ℕ*-commute x (ℕ.suc y)) ⟩
--   ℕ.suc y + ℕ.suc y * x
--                      ≡⟨ ℕ+-cong refl refl ⟩
--   ℕ.suc y + (x + y * x)
--                      ≡⟨ refl ⟩
--   ℕ.suc (y + (x + y * x))
--                      ≡⟨ cong ℕ.suc (sym (ℕ+-assoc y x (y * x))) ⟩
--   ℕ.suc ((y + x) + y * x)
--                      ≡⟨ cong ℕ.suc (ℕ+-cong (ℕ+-commute y x) (ℕ*-commute y x)) ⟩
--   ℕ.suc ((x + y) + x * y)
--                      ≡⟨ cong ℕ.suc (ℕ+-assoc x y (x * y)) ⟩
--   ℕ.suc (x + (y + x * y))
--                      ≡⟨ cong ℕ.suc refl ⟩
--   ℕ.suc (x + (ℕ.suc x * y))
--                      ≡⟨ refl ⟩
--   ℕ.suc x + (ℕ.suc x * y)
--                      ≡⟨ ℕ+-cong refl (ℕ*-commute (ℕ.suc x) y) ⟩
--   ℕ.suc x + (y * ℕ.suc x)
--                      ≡⟨ refl ⟩
--   ℕ.suc y * ℕ.suc x
--   ∎
-- 
-- ℕ-distr : (_DistributesOver_) (_≡_) (_*_) (_+_) 
-- ℕ-distr = ldistr , rdistr 
--   where
--     ldistr : (l m n : ℕ) → l * (m + n) ≡ l * m + l * n
--     ldistr ℕ.zero m n = refl
--     ldistr (ℕ.suc l) m n = begin
--       ℕ.suc l * (m + n)
--                    ≡⟨ refl ⟩
--       (m + n) + l * (m + n)
--                    ≡⟨ ℕ+-cong (ℕ+-commute m n) (ldistr l m n) ⟩
--       (n + m) + (l * m + l * n)
--                    ≡⟨ ℕ+-assoc n m (l * m + l * n) ⟩
--       n + (m + (l * m + l * n))
--                    ≡⟨ ℕ+-cong refl (sym (ℕ+-assoc m (l * m) (l * n))) ⟩
--       n + ((m + l * m) + l * n)
--                    ≡⟨ ℕ+-cong refl (ℕ+-cong refl refl) ⟩
--       n + (ℕ.suc l * m + l * n)
--                    ≡⟨ sym (ℕ+-assoc n ((ℕ.suc l) * m) (l * n)) ⟩
--       (n + ℕ.suc l * m) + l * n
--                    ≡⟨ ℕ+-cong (ℕ+-commute n (ℕ.suc l * m)) refl ⟩
--       (ℕ.suc l * m + n) + l * n
--                    ≡⟨ ℕ+-assoc (ℕ.suc l * m) n (l * n) ⟩
--       ℕ.suc l * m + (n + l * n)
--                    ≡⟨ refl ⟩
--       ℕ.suc l * m + ℕ.suc l * n
--       ∎
--     rdistr : (l m n : ℕ) → (m + n) * l ≡ m * l + n * l
--     rdistr l m n = begin
--       (m + n) * l
--                    ≡⟨ ℕ*-commute (m + n) l ⟩
--       l * (m + n)
--                    ≡⟨ ldistr l m n ⟩
--       l * m + l * n
--                    ≡⟨ ℕ+-cong (ℕ*-commute l m) (ℕ*-commute l n) ⟩
--       m * l + n * l
--       ∎
-- 
-- ℕ*-assoc : Associative _≡_ _*_
-- ℕ*-assoc ℕ.zero m n = begin
--   (ℕ.zero * m) * n
--                     ≡⟨ ℕ*-cong refl refl ⟩
--   ℕ.zero * n
--                     ≡⟨ refl ⟩
--   ℕ.zero
--                     ≡⟨ refl ⟩
--   ℕ.zero * (m * n)
--   ∎
-- ℕ*-assoc (ℕ.suc l) m n = begin
--   (ℕ.suc l * m) * n
--                     ≡⟨ refl ⟩
--   (m + l * m) * n
--                     ≡⟨ proj₂ ℕ-distr  n m (l * m) ⟩
--   (m * n) + (l * m) * n
--                     ≡⟨ ℕ+-cong refl (ℕ*-assoc l m n) ⟩
--   (m * n) + l * (m * n)
--                     ≡⟨ refl ⟩
--   ℕ.suc l * (m * n)
--   ∎
-- 
-- ℕ*-ident : Identity _≡_ 1 _*_
-- ℕ*-ident = left , right
--   where
--     left : (x : ℕ) → 1 * x ≡ x
--     left x = ℕ+-commute x 0
--     right : (x : ℕ) → x * 1 ≡ x
--     right x = trans (ℕ*-commute x 1) (ℕ+-commute x 0)
--       
-- ℕ-zero : Zero _≡_ 0 _*_
-- ℕ-zero = left , right
--   where
--     left : (x : ℕ) → 0 * x ≡ 0 
--     left _ = refl 
--     right : (x : ℕ) → x * 0 ≡ 0 
--     right x = ℕ*-commute x 0
-- 
-- ℕ-CommutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
-- ℕ-CommutativeSemiring = record
--   { Carrier = ℕ
--   ; _≈_ = _≡_
--   ; _+_ = _+_
--   ; _*_ = _*_
--   ; 0# = ℕ.zero
--   ; 1# = ℕ.suc ℕ.zero
--   ; isCommutativeSemiring = record
--     { isSemiring = record
--       { zero = ℕ-zero
--       ; isSemiringWithoutAnnihilatingZero = record
--         { +-isCommutativeMonoid = record
--           { isMonoid = record
--             { isSemigroup = record
--               { isMagma = record
--                 { isEquivalence = ℕ-equiv
--                 ; ∙-cong = ℕ+-cong
--                 }
--               ; assoc = ℕ+-assoc 
--               }
--             ; identity = (λ _ → refl) , λ x → ℕ+-commute x ℕ.zero
--             }
--           ; comm = ℕ+-commute
--           }
--         ; *-cong = ℕ*-cong
--         ; *-assoc = ℕ*-assoc
--         ; *-identity = ℕ*-ident
--         ; distrib = ℕ-distr
--         }
--       }
--     ; *-comm = ℕ*-commute
--     }
--   }
-}
