{-# OPTIONS --guardedness #-}

open import lib23

-- open import Data.String

{-
Metatheory
Propositional logic in Agda (with just →

Formual , [⇒] , atoms = strings, Con - context
⊢ : Formula → Prop
_⊢_ : Con → Formula → Prop 
semantics
-}

data Form : Set where
  Atom : ℕ → Form
  _[⇒]_ : Form → Form → Form

infixr 10 _[⇒]_

K-F : Form
K-F = Atom 0 [⇒] Atom 1 [⇒] Atom 0

-- (P → Q → R) → (P → Q) → (P → R) 
S-F : Form
S-F = (Atom 0 [⇒] Atom 1 [⇒] Atom 2)
  [⇒] (Atom 0 [⇒] Atom 1)
  [⇒] (Atom 0 [⇒] Atom 2)

data Con : Set where
  • : Con
  _▹_ : Con → Form → Con

infix 5 _⊢_
infixl 10 _▹_

variable Γ Δ : Con
variable ϕ ψ θ : Form

data _⊢_ : Con → Form → Set where
  -- introduction
  zero : Γ ▹ ϕ ⊢ ϕ
  -- weakening
  suc : Γ ⊢ ϕ → Γ ▹ ψ ⊢ ϕ
  -- ⇒-into
  lam : (Γ ▹ ϕ ⊢ ψ) → (Γ ⊢ ϕ [⇒] ψ)
  -- 
  app : (Γ ⊢ ϕ [⇒] ψ) → (Γ ⊢ ϕ) → (Γ ⊢ ψ) 

-- debruijn indices 'count the number of lambdas needs to be traversed to result.'

kk : P → Q → P
kk = λ x _ → x

k-d : • ⊢ K-F
k-d = lam (lam (suc zero))

ss : (P → Q → R) → (P → Q) → P → R
ss = λ pqr → λ pq → λ p → pqr p (pq p)
-- λ λ λ 2 0 (1 0)

s-d : • ⊢ S-F
s-d =  lam (lam (lam (app (app (suc (suc zero)) zero) (app (suc zero) zero))))

bad : Form
bad = (Atom 0 [⇒] Atom 1) [⇒] (Atom 1 [⇒] Atom 0)

-- How to prove this?
-- With semantics
no-d : ¬ (• ⊢ bad)
no-d (lam d) = {!!}
no-d (app d e) = {!!}

-- Proof theory : ⊢
-- Model theory. What do things mean?
