
open import Agda.Primitive  
open import Relation.Binary.Bundles
  using (Setoid)
open import Algebra.Bundles
  using (Monoid)
open Monoid using (_≈_; Carrier)
-- open import Algebra.Bundles.Monoid using (_≈_)
open import Level using (0ℓ)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_)


infix 10 _⋆_
-- infix 5 _~_

data AssociatorTree : ℕ → Set where
  # : AssociatorTree 1
  _⋆_ : {m n : ℕ} → AssociatorTree m → AssociatorTree n → AssociatorTree (m + n)

record Associator : Set (lsuc 0ℓ) where
  field
    M : Monoid 0ℓ 0ℓ 
    arity : ℕ
    left right : AssociatorTree arity

  _~_ : {A : Associator} → {arity : ℕ}
      → (a b : AssociatorTree arity)
      → {x y : ACarrier A} → x ≈ y

x : AssociatorTree 3
x = # ⋆ (# ⋆ #)

y : AssociatorTree 3
y = (# ⋆ #) ⋆ #


