{- COMP4074 Lecture 1 -}

{-
Proofs, Programs & Types
What is a type?
What is the difference between types and sets?

Sets are dynamic
∀ x , x ∈ ℕ , x + 0 = x
ℕ = { {} , {{}} , {{},{{}}}, ... }

∀ x : ℕ , x + 0 = x

What is Type Theory?

a programming language
used in proof assistants:
  Lean, Coq, (Isabelle), Idris, agda
alternative foundations of Mathematics
Zermelo-Fraenkel set theory (ZFC)
Homotopy Type Theory (cubical agda)

History
1972 Per Martin-Löf
constructive foundation of Mathematics
predicative, extensional , intensional TT
NuPRL , Cornell
Calculus of Constructions (impredicative)
90 : Coq , Paris (Thierry Coquand) Gerard Huet
Catarina : agda , Ulf Norell
about 2010: Vladimir Voevodsky
Homotopy Type Theory

Overview
- simple types (functions, products and sums)
- combinators (S,K)
- propositions as types (PaT) for prop.logic
- inductive types , coinductive types
- dependent types
- PaT for predicate logic
- equality types
- proofs & programs (integrated verification)
- Deduction (TT in TT)
- Universes & paradoxes
- HoTT & cubical agda

-}
