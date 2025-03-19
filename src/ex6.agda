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

P01 = {A B : Set}{R : A → B → Prop} →
      ((∀[ x ∈  A ] ∃[ y ∈ B ] R x y)) →
      (∃[ y ∈ B ] ∀[ x ∈ A ] R x y)
p01 : P01 → ⊥
p01 p = let
    b , z = p {A = Bool} {B = Bool} {R = R'} λ {false → false , tt ; true → true , tt }
    p₂ : R' true true → R' true false
    p₂ rtt = {! !}
  in
    {!!}
  where
    R' : Bool → Bool → Prop
    R' true true = ⊤
    R' false false  = ⊤
    R' _ _ = ⊥

P02 = {A B : Set}{R : A → B → Prop} →
     (∃[ y ∈ B ] (∀[ x ∈ A ] R x y))
     → (∀[ x ∈ A ] (∃[ y ∈ B ] R x y))
p02 : P02
p02 = λ (y , ex) x → y , ex x

P03 = {A : Set}{P : A → Prop} →
     ¬ (∃[ x ∈ A ] P x) → ∀[ x ∈  A ] ¬ (P x)
p03 : P03
p03 = λ ¬∃ x px → ¬∃ (x , px)

P04 = {A : Set}{P : A → Prop} →
       (∀[ x ∈ A ] ¬ (P x)) → ¬ (∃[ x ∈  A ] P x)
p04 : P04
p04 = λ ∀¬p (x , px) → ∀¬p x px

P05 = {A : Set}{P : A → Prop} →
      (¬ (∀[ x ∈ A ] P x)) → ∃[ x ∈ A ] ¬ (P x)
p05 : CLASS → P05
-- p05 raa ¬∀P = raa (λ ¬¬∃P → ¬¬∃P (λ (x , px) → {!!}))
p05 raa ¬∀P = raa (λ ¬∃¬P → ¬∃¬P {!!})

P06 = {A : Set}{P : A → Prop} →
      (∃[ x ∈ A ] ¬ (P x)) → (¬ (∀[ x ∈ A ] P x))
-- P06 : ∃¬P → ∀P → ⊥
p06 : P06
p06 (x , ¬px) ∀p = ¬px (∀p x)

P07 = {A : Set}{P : A → Prop} →
      (¬ (¬ (∀[ x ∈ A ] P x))) → ∀[ x ∈  A ] ¬ (¬ (P x))
-- (¬∀P → ⊥) → ∀x (¬Px → ⊥)
p07 : P07
p07 ¬¬∀p x ¬px =
  let
    ¬∀p = λ ∀p → ¬px (∀p x)
  in
    ¬¬∀p ¬∀p

P08 = {A : Set}{P : A → Prop} →
      (∀[ x ∈  A ] ¬ (¬ (P x))) → (¬ (¬ (∀[ x ∈ A ] P x)))
-- (∀x (¬Px → ⊥)) → ¬∀Px → ⊥
p08 : CLASS → P08
p08 raa = λ ∀¬¬p ¬∀p → ¬∀p λ x → raa (∀¬¬p x)

P09 = {A : Set}{P : A → Prop} →
      (∃[ x ∈ A ] ⊤) → (∃[ x ∈ A ] P x) → ∀[ x ∈ A ] P x
-- ∃x → (∃P → ∀P)
p09' : P09 → ⊥
p09' p09 = p09 (true , tt) (true , tt) false P'
  where
    P' : Bool → Prop
    P' true = ⊤
    P' false = ⊥

-- P' : Bool → Prop
-- P' true = ⊤
-- P' false = ⊥

P10 = {A : Set}{P : A → Prop} →
      (∃[ x ∈ A ] ⊤) → (∃[ y ∈ A ] (P y → ∀[ x ∈ A ] P x))
p10 : {A : Set}{P' : A → Prop} → CLASS → P10
p10 {A}{P'} raa (z , _) =
    {!!}
   where
    red1 : (∃[ x ∈ A ] (¬ P' x)) → (∃[ y ∈ A ] (P' y → ∀[ x ∈ A ] P' x))
    red1 (x , ¬px) = x , λ px → case⊥ (¬px px)
    red2 : ¬ ( ∃[ x ∈ A ] (¬ P' x)) → (∃[ y ∈ A ] (P' y → ∀[ x ∈ A ] P' x))
    red2 ¬∃¬P = raa λ ¬∃ → {!¬∃ λ y → ? !}

-- E¬P → ⊥
--  |- WTS Px → ∀ z P z
--  |- Suppose ¬P x
--     | Then P y 

-- P y <= P x
-- P y minimal
-- 
-- ∃P → P y
-- ¬∃P → 

-- P x 
-- ∃A → ∃y ∀x (¬Py or Px)
-- y = true, x = false
-- ∀y ∃x (Py and ¬Px)
-- p10' : P10 → ⊥
-- p10' p10 with (p10 {A = Bool} {P = P'}) (true , tt)
-- ... | (true , q) = q tt false
-- ... | (false , q) = {!q  !}
-- let
--     (true , q) = (p10 {A = Bool} {P = P'}) (true , tt)
--     (false , q) = (
--     foo = q (P' y) false
--   in {!q (P' true) false!}

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






