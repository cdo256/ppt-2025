{-# OPTIONS --guardedness #-} -- for coinduction

{- Exercise 6, COMP4074 -}

open import lib20

CLASS = {P : Prop} → RAA P

{- Part 1 (80%)

Logic poker, this time with predicate logic.

The rules of logic poker are given a proposition P you can either

1) prove P (without any assumptions)
2) prove P → ⊥ (that means usually to instantiate the sets and 
              predicates to construct a counterexample)
3) prove CLASS -> P

You can loose points when you choose 3 where 1 would have been
sufficient. That is the poker aspect.

Note that case 2 can be a bit tricky because you have to construct 
a counterexample. However, using Bool and equality should be sufficient.
-}

P01 : Prop
P01 = {A B : Set}{R : A → B → Prop} →
      ((∀[ x ∈  A ] ∃[ y ∈ B ] R x y)) →
      (∃[ y ∈ B ] ∀[ x ∈ A ] R x y)
p01 : ¬ P01
p01 p = let p' = p {A = Bool} {B = Bool} {R = ¬_} ? {!!} in {!!}

P02 = {A B : Set}{R : A → B → Prop} →
     (∃[ y ∈ B ] (∀[ x ∈ A ] R x y))
     → (∀[ x ∈ A ] (∃[ y ∈ B ] R x y))
P03 = {A : Set}{P : A → Prop} →
     ¬ (∃[ x ∈ A ] P x) → ∀[ x ∈  A ] ¬ (P x)
P04 = {A : Set}{P : A → Prop} →
       (∀[ x ∈ A ] ¬ (P x)) → ¬ (∃[ x ∈  A ] P x)
P05 = {A : Set}{P : A → Prop} →
      (¬ (∀[ x ∈ A ] P x)) → ∃[ x ∈ A ] ¬ (P x)
P06 = {A : Set}{P : A → Prop} →
      (∃[ x ∈ A ] ¬ (P x)) → (¬ (∀[ x ∈ A ] P x))
P07 = {A : Set}{P : A → Prop} →
      (¬ (¬ (∀[ x ∈ A ] P x))) → ∀[ x ∈  A ] ¬ (¬ (P x))
P08 = {A : Set}{P : A → Prop} →
      (∀[ x ∈  A ] ¬ (¬ (P x))) → (¬ (¬ (∀[ x ∈ A ] P x)))
P09 = {A : Set}{P : A → Prop} →
      (∃[ x ∈ A ] ⊤) → (∃[ x ∈ A ] P x) → ∀[ x ∈ A ] P x
P10 = {A : Set}{P : A → Prop} →
      (∃[ x ∈ A ] ⊤) → (∃[ y ∈ A ] (P y → ∀[ x ∈ A ] P x))

{- Part 2 (20 %) -}

{- There are actually two versions of the J-combinator
   and we want to prove that they are equivaent.
-}

-- J-ML is the type of Martin-Loef's J-combinator
J-ML = {A : Set}(M : {a b : A} → (a ≡ b) → Set)
    → ({a : A} → M (refl {a = a}))
    → {a b : A}(p : a ≡ b) → M p

-- J-PM is a variant introduced by Paulin-Mohring
-- also called based path induction
J-PM = {A : Set}{a : A}(M : {b : A} → (a ≡ b) → Set)
    → (M (refl {a = a}))
    → {b : A}(p : a ≡ b) → M p

-- in the following do not use mattern matching or any function that has been
-- derived using pattern matching - this includes J from the library.

module _(j-ml : J-ML) where

  -- you can only use j-ml here
  j-pm : J-PM
  j-pm = {!!}


module _(j-pm : J-PM) where

  -- you can only use j-pm here
  j-ml : J-ML
  j-ml = {!!}






