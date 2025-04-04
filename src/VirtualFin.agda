module VirtualFin where

-- Def 1.1
open import Data.Nat
  using (_+_; ℕ)
open import Data.Fin
  hiding (_+_)

private
  variable
    l m n : ℕ

infix 20 [-]

_[-]_ : {X A Y : FinSet} → (X ⊎ A → Y ⊎ A) → (X : Set) → Fin l → Fin m
_[-]_  = {!!} 
