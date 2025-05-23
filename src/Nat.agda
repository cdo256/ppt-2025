{-# OPTIONS -WnoUnsupportedIndexedMatch --guardedness #-} -- for coinduction


module Nat where

open import Data.Product
  using (proj₁; proj₂)

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
open import Data.Product.Base using (∃; _×_; _,_)
open import Data.Sum.Base as Sum using (inj₁; inj₂; _⊎_; [_,_]′)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_; flip; _$_; id; _∘′_; _$′_)
open import Function.Bundles using (_↣_)
open import Function.Metric.Nat using (TriangleInequality; IsProtoMetric; IsPreMetric;
  IsQuasiSemiMetric; IsSemiMetric; IsMetric; PreMetric; QuasiSemiMetric;
  SemiMetric; Metric)
open import Level using (0ℓ)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core
  using (_⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary
open import Relation.Binary.Consequences using (flip-Connex)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable using (True; via-injection; map′; recompute)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (fromEquivalence)

open import Algebra.Definitions
open import Algebra.Structures {A = ℕ} _≡_

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- open import Data.Nat public
--   using (ℕ; zero; suc; _+_; _*_)
-- open import Data.Product
--   using (proj₁; proj₂)
-- open import Agda.Builtin.Sigma
-- open import Algebra.Bundles
-- -- open import Algebra.Definitions
-- open import Algebra.Properties.Semiring.Mult
-- open import Relation.Binary.Structures
-- open import Relation.Binary.Core
-- -- open import Relation.Binary.Definitions
-- --   using (_DistributesOver_)
-- open import Relation.Binary.PropositionalEquality
--   using (refl; sym; trans; cong)
-- open Relation.Binary.PropositionalEquality.≡-Reasoning
-- -- open Relation.Binary.≡-Reasoning
-- open import Level
--   using (0ℓ; Level)
-- 
-- open import Algebra.Definitions {A = ℕ} _≡_

private
  variable
    ℓ : Level.Level

ℕ-equiv : IsEquivalence {a = 0ℓ} {A = ℕ} _≡_
ℕ-equiv = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

ℕ+-cong : Congruent₂ (_≡_) (_+_)
ℕ+-cong {x} {y} {u} {v} xy uv =
  trans (cong (λ z → x + z) uv)
        (cong (λ z → z + v) xy)

ℕ+-ident : Identity _≡_ 0 _+_
ℕ+-ident = left , right 
  where
    left : (x : ℕ) → 0 + x ≡ x
    left x = refl
    right : (x : ℕ) → x + 0 ≡ x
    right ℕ.zero = refl
    right (ℕ.suc x) = begin
      ℕ.suc x + 0
                   ≡⟨ refl ⟩
      ℕ.suc (x + 0)
                   ≡⟨ cong ℕ.suc (right x) ⟩
      ℕ.suc x
      ∎

ℕ+-assoc : Associative _≡_ _+_
ℕ+-assoc zero y z = refl
ℕ+-assoc (suc x) y z = begin
  (ℕ.suc x + y) + z
                   ≡⟨ refl ⟩
  (ℕ.suc (x + y)) + z
                   ≡⟨ refl ⟩
  ℕ.suc ((x + y) + z)
                   ≡⟨ cong ℕ.suc (ℕ+-assoc x y z) ⟩
  ℕ.suc (x + (y + z))
                   ≡⟨ refl ⟩
  ℕ.suc x + (y + z)
  ∎

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

ℕ*-cong : Congruent₂ (_≡_) (_*_)
ℕ*-cong {x} {y} {u} {v} xy uv =
  trans (cong (λ z → x * z) uv)
        (cong (λ z → z * v) xy)

ℕ*-commute : Commutative _≡_ _*_
ℕ*-commute zero zero = refl
ℕ*-commute zero (suc y) = ℕ*-commute ℕ.zero y
ℕ*-commute (suc x) zero = ℕ*-commute x ℕ.zero 
ℕ*-commute (suc x) (suc y) = begin
  ℕ.suc x * ℕ.suc y
                     ≡⟨ refl ⟩
  ℕ.suc y + x * ℕ.suc y 
                     ≡⟨ ℕ+-cong refl (ℕ*-commute x (ℕ.suc y)) ⟩
  ℕ.suc y + ℕ.suc y * x
                     ≡⟨ refl ⟩
  ℕ.suc y + (x + y * x)
                     ≡⟨ refl ⟩
  ℕ.suc (y + (x + y * x))
                     ≡⟨ cong ℕ.suc (sym (ℕ+-assoc y x (y * x))) ⟩
  ℕ.suc ((y + x) + y * x)
                     ≡⟨ cong ℕ.suc (ℕ+-cong (ℕ+-commute y x) (ℕ*-commute y x)) ⟩
  ℕ.suc ((x + y) + x * y)
                     ≡⟨ cong ℕ.suc (ℕ+-assoc x y (x * y)) ⟩
  ℕ.suc (x + (y + x * y))
                     ≡⟨ cong ℕ.suc refl ⟩
  ℕ.suc (x + (ℕ.suc x * y))
                     ≡⟨ refl ⟩
  ℕ.suc x + (ℕ.suc x * y)
                     ≡⟨ ℕ+-cong refl (ℕ*-commute (ℕ.suc x) y) ⟩
  ℕ.suc x + (y * ℕ.suc x)
                     ≡⟨ refl ⟩
  ℕ.suc y * ℕ.suc x
  ∎

ℕ-distr : (_DistributesOver_) (_≡_) (_*_) (_+_) 
ℕ-distr = ldistr , rdistr 
  where
    ldistr : (l m n : ℕ) → l * (m + n) ≡ l * m + l * n
    ldistr ℕ.zero m n = refl
    ldistr (ℕ.suc l) m n = begin
      ℕ.suc l * (m + n)
                   ≡⟨ refl ⟩
      (m + n) + l * (m + n)
                   ≡⟨ ℕ+-cong (ℕ+-commute m n) (ldistr l m n) ⟩
      (n + m) + (l * m + l * n)
                   ≡⟨ ℕ+-assoc n m (l * m + l * n) ⟩
      n + (m + (l * m + l * n))
                   ≡⟨ ℕ+-cong (refl {x = n}) (sym (ℕ+-assoc m (l * m) (l * n))) ⟩
      n + ((m + l * m) + l * n)
                   ≡⟨ refl ⟩
      n + (ℕ.suc l * m + l * n)
                   ≡⟨ sym (ℕ+-assoc n ((ℕ.suc l) * m) (l * n)) ⟩
      (n + ℕ.suc l * m) + l * n
                   ≡⟨ ℕ+-cong (ℕ+-commute n (ℕ.suc l * m)) refl ⟩
      (ℕ.suc l * m + n) + l * n
                   ≡⟨ ℕ+-assoc (ℕ.suc l * m) n (l * n) ⟩
      ℕ.suc l * m + (n + l * n)
                   ≡⟨ refl ⟩
      ℕ.suc l * m + ℕ.suc l * n
      ∎
    rdistr : (l m n : ℕ) → (m + n) * l ≡ m * l + n * l
    rdistr l m n = begin
      (m + n) * l
                   ≡⟨ ℕ*-commute (m + n) l ⟩
      l * (m + n)
                   ≡⟨ ldistr l m n ⟩
      l * m + l * n
                   ≡⟨ ℕ+-cong (ℕ*-commute l m) (ℕ*-commute l n) ⟩
      m * l + n * l
      ∎

ℕ*-assoc : Associative _≡_ _*_
ℕ*-assoc ℕ.zero m n = begin
  (ℕ.zero * m) * n
                    ≡⟨ refl ⟩
  ℕ.zero * n
                    ≡⟨ refl ⟩
  ℕ.zero
                    ≡⟨ refl ⟩
  ℕ.zero * (m * n)
  ∎
ℕ*-assoc (ℕ.suc l) m n = begin
  (ℕ.suc l * m) * n
                    ≡⟨ refl ⟩
  (m + l * m) * n
                    ≡⟨ proj₂ ℕ-distr  n m (l * m) ⟩
  (m * n) + (l * m) * n
                    ≡⟨ ℕ+-cong refl (ℕ*-assoc l m n) ⟩
  (m * n) + l * (m * n)
                    ≡⟨ refl ⟩
  ℕ.suc l * (m * n)
  ∎

ℕ*-ident : Identity _≡_ 1 _*_
ℕ*-ident = left , right
  where
    left : (x : ℕ) → 1 * x ≡ x
    left x = ℕ+-commute x 0
    right : (x : ℕ) → x * 1 ≡ x
    right x = trans (ℕ*-commute x 1) (ℕ+-commute x 0)
   
ℕ-zero : Zero _≡_ 0 _*_
ℕ-zero = left , right
  where
    left : (x : ℕ) → 0 * x ≡ 0 
    left _ = refl 
    right : (x : ℕ) → x * 0 ≡ 0 
    right x = ℕ*-commute x 0

ℕ+-inj : (l m n : ℕ) → l + m ≡ l + n → m ≡ n
ℕ+-inj zero m n lmln = lmln
ℕ+-inj (suc l) m n lmln = 
    ℕ+-inj l m n (cong pred lmln)

ℕ-CommutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
ℕ-CommutativeSemiring = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = ℕ.zero
  ; 1# = ℕ.suc ℕ.zero
  ; isCommutativeSemiring = record
    { isSemiring = record
      { zero = ℕ-zero
      ; isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = ℕ-equiv
                ; ∙-cong = ℕ+-cong
                }
              ; assoc = ℕ+-assoc 
              }
            ; identity = (λ _ → refl) , λ x → ℕ+-commute x ℕ.zero
            }
          ; comm = ℕ+-commute
          }
        ; *-cong = ℕ*-cong
        ; *-assoc = ℕ*-assoc
        ; *-identity = ℕ*-ident
        ; distrib = ℕ-distr
        }
      }
    ; *-comm = ℕ*-commute
    }
  }
