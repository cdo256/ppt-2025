{-# OPTIONS --guardedness #-}

open import lib25 hiding (List; _×_)

{-
Predicative hierarchy
Set : Set1 : Set2 : ...

(Set : Set) → ⊥
Frege -> Begriffsschrift (unlimited comprehension)
      -> Russell's paradox
UnlimitedComp : (Set → Prop) → Σ[ X ∈ Set ] (∀[ Y ∈ Set ](Y ∈ X ⇔ P X))

R = { X : Set . X ∉ X }

Zermelo:
data Set' : Set where
  empty : Set
  pair : Set → Set → Set
  _≈_ : 
  
  prop : Set → Prop
zermelo only
 Axiom of extensionality
 (X , Y : Set) → ({X , Y} : Set)
 PowerSet : (X : Set) → Σ[ Y : Set ] (Set' P)
 infinity -- gets an inductive set
   {} ∈ I
   x ∈ I → {x} u x ∈ I -- von-neumann neumerals
   x ∈ I → {x} ∈ I -- zermelo numerals
 Axiom of replacement
 Axiom of regularity -- there is a least element.
ZF + C
-}

{-
Per Martin-Lof (1972): Foundations of intuinistic mathematics
  - remove powerset and choice
  - and excluded middle ?
System T: Type theory using natural numbers, lambda and recursion
  - Language of peano arithmetic'
System F: Girard
  - 'System of second order logic'

MLTT:
  Had Type : Type
  Could formulate system F

System U: Girard
  Has two impredicative levels
  Can be formulated as two levels of lambda calculus.
  Second order logic + system F
  Couldn't prove normalization theorem theorem
  Proved inconsistent
  Girard's Paradox
  Therefore System U and MLTT is inconsistent
  
Predicative type theory: Girard (1970's)
  Thierry Coquand : Paradox of trees - russels paradox in type theory
-}

{-# NO_UNIVERSE_CHECK #-}
data Tree : Set where
  node : (I : Set) → (I → Tree) → Tree

{-# NO_UNIVERSE_CHECK #-}
data _∈_ : Tree → Tree → Set where
  is-∈ : (I : Set)(f : I → Tree)(i : I)
       → f i ∈ node I f
  
⟨⟩ : Tree
⟨⟩ = node ⊥ λ ()

⟨⟨⟩⟩ : Tree
⟨⟨⟩⟩ = node ⊤ (λ _ → ⟨⟩)

union : Tree → Tree → Tree
union (node I f) (node J g) = node (I ⊎ J) h
  where
    h : (I ⊎ J) → Tree
    h (inj₁ x) = f x
    h (inj₂ x) = g x

good : Tree → Set
good t = ¬ (t ∈ t)

russell : Tree
russell = node (Σ[ t ∈ Tree ] (good t)) (λ x → x .Σ.proj₁)

bad : (russell ∈ russell) ⇔ ¬ (russell ∈ russell)
bad .proj₁ (is-∈ .(Σ Tree good) .(λ x → x .Σ.proj₁) (.russell , p)) = p
bad .proj₂ h = is-∈ _ _ (russell , h) 

exx : ¬ (P ⇔ ¬ P)
exx {P = P} (pnp , npp) = pnp (npp (λ z → pnp z z)) (npp (λ z → pnp z z))
  where np : ¬ P
        np p = pnp p p

boom : ⊥
boom = exx bad
