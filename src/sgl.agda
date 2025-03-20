{-# OPTIONS --guardedness #-}

open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Relation.Binary.PropositionalEquality as Eq

-- data ℕ : Set where 
--   zero : ℕ
--   suc : ℕ → ℕ

-- TODO: This is a bad definition.
--   Do we need a disambiguator?
record Peg : Set where
  coinductive

record FiniteSet (A : Set) : Set where
  constructor finset
  field
    elements : List A

record Link : Set where
  constructor L
  field
    role : Node
    obj : Node
    i : ℕ

record Fork : Set where
  constructor L
  field
    links : Set OutLink

data Node : Set where
  fnode : Fork → Node
  pnode : Fork → Node

record Link : Set where
  constructor L
  field
    subj : Node
    role : Node
    obj : Node
    i : ℕ



postulate
  nzero : Node
  nsuc : Node → Node



-- data Graph : Link → Prop where
