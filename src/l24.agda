{-# OPTIONS --guardedness #-}
{- Lecture 24 COMP4074 -}

postulate String : Set
{-# BUILTIN STRING String #-}

open import lib23

{-
Metatheory
Propositional logic, only implication

Formulas , [⇒] , atoms = strings
⊢ : Formula → Prop
_⊢_ : Con → Formula → Prop
semantics

-}

data Form : Set where
  Atom : String → Form
  _[⇒]_ : Form → Form → Form

infixr 10 _[⇒]_

-- P → Q → P
K-F : Form
K-F = Atom "P" [⇒] Atom "Q" [⇒] Atom "P"

-- (P → Q → R) → (P → Q) → P → R
S-F : Form
S-F = (Atom "P" [⇒] Atom "Q" [⇒] Atom "R")
    [⇒] (Atom "P" [⇒] Atom "Q")
    [⇒] Atom "P" [⇒] Atom "R"

data Con : Set where
  • : Con -- \bu
  _▷_ : Con → Form → Con

variable Γ Δ : Con
variable φ ψ θ : Form -- \phi \psi \theta

infix 5 _⊢_
infixl 8 _▷_

-- natural deduction , Gerhard Gentzen

data _⊢_ : Con → Form → Set where
  zero : Γ ▷ φ ⊢ φ
  suc : Γ ⊢ φ → Γ ▷ ψ ⊢ φ
  lam : Γ ▷ φ ⊢ ψ → Γ ⊢ φ [⇒] ψ
  app : Γ ⊢ φ [⇒] ψ → Γ ⊢ φ → Γ ⊢ ψ

kk : P → Q → P
kk = λ p → λ q → p
-- λ λ 1
-- deBruijn indices

k-d : • ⊢ K-F
k-d = lam (lam (suc zero))

ss : (P → Q → R) → (P → Q) → P → R
ss = λ pqr → λ pq → λ p → pqr p (pq p)
-- λ λ λ 2 0 (1 0)

s-d : • ⊢ S-F
s-d = lam (lam (lam (app (app (suc (suc zero)) zero)
          (app (suc zero) zero))))

-- (P → Q) → Q → P
-- P = ⊥, Q = ⊤ 
bad : Form
bad = (Atom "P" [⇒] Atom "Q") [⇒] (Atom "Q" [⇒] Atom "P") 

no-d : ¬ (• ⊢ bad)
no-d (lam (suc (lam d))) = {!!}
no-d (lam (suc (app (lam d) d₁))) = {!!}
no-d (lam (suc (app (app d d₂) d₁))) = {!!}
no-d (lam (lam d)) = {!!}
no-d (lam (app d d₁)) = {!!}
no-d (app d e) = {!!}

-- how can I prove no-d ?
-- proof theory : ⊢
-- model theory : what do things mean? , sound , completenss
