{-# OPTIONS --guardedness #-}
{- Lecture 26 COMP4074 -}

open import lib25

data Form : Set where
  Atom : String → Form
  _[⇒]_ : Form → Form → Form

infixr 10 _[⇒]_

data Con : Set where
  • : Con -- \bu
  _▷_ : Con → Form → Con

variable Γ Δ : Con
variable φ ψ θ : Form 

infix 5 _⊢_
infixl 8 _▷_

data _⊢_ : Con → Form → Set where
  zero : Γ ▷ φ ⊢ φ
  suc : Γ ⊢ φ → Γ ▷ ψ ⊢ φ
  lam : Γ ▷ φ ⊢ ψ → Γ ⊢ φ [⇒] ψ
  app : Γ ⊢ φ [⇒] ψ → Γ ⊢ φ → Γ ⊢ ψ

infix 5 ⊢SK_

data ⊢SK_ : Form → Set where
  KK : ⊢SK φ [⇒] ψ [⇒] φ
  SS : ⊢SK (φ [⇒] ψ [⇒] θ) [⇒] (φ [⇒] ψ) [⇒] (φ [⇒] θ)
  app : ⊢SK φ [⇒] ψ → ⊢SK φ → ⊢SK ψ

infix 5 _⊢SKv_

data _⊢SKv_ : Con → Form → Set where
  zero : Γ ▷ φ ⊢SKv φ
  suc : Γ ⊢SKv φ → Γ ▷ ψ ⊢SKv φ
  app : Γ ⊢SKv φ [⇒] ψ → Γ ⊢SKv φ → Γ ⊢SKv ψ
  KK : Γ  ⊢SKv φ [⇒] ψ [⇒] φ
  SS : Γ ⊢SKv (φ [⇒] ψ [⇒] θ) [⇒] (φ [⇒] ψ) [⇒] (φ [⇒] θ)

II : Γ ⊢SKv φ [⇒] φ
II {φ = φ} = app (app SS KK) (KK {ψ = φ})

k-d : • ⊢ φ [⇒] ψ [⇒] φ
k-d = lam (lam (suc zero))

s-d : • ⊢ (φ [⇒] ψ [⇒] θ) [⇒] (φ [⇒] ψ) [⇒] (φ [⇒] θ)
s-d = lam (lam (lam (app (app (suc (suc zero)) zero)
          (app (suc zero) zero))))

dedThm : Γ ▷ φ ⊢SKv ψ → Γ ⊢SKv φ [⇒] ψ
-- λ x → x
dedThm zero = II
-- λ x → M, x # M
dedThm (suc d) = app KK d
-- λ x → M N = ? S (λ x → M) (λ x → N)
dedThm (app d e) = app (app SS (dedThm d)) (dedThm e)
-- λ x → K = K K
dedThm KK = app KK KK
-- λ x → S = K S
dedThm SS = app KK SS

eqLem : Γ ⊢ φ → Γ ⊢SKv φ
eqLem zero = zero
eqLem (suc d) = suc (eqLem d)
eqLem (lam d) = dedThm (eqLem d)
eqLem (app d e) = app (eqLem d) (eqLem e)

skvLem : • ⊢SKv φ → ⊢SK φ
skvLem (app d e) = app (skvLem d) (skvLem e)
skvLem KK = KK
skvLem SS = SS

eqThm : • ⊢ φ ⇔ ⊢SK φ
proj₁ eqThm d = skvLem (eqLem d)
proj₂ eqThm KK = k-d
proj₂ eqThm SS = s-d
proj₂ eqThm (app d e) = app (proj₂ eqThm d) (proj₂ eqThm e)

str : Γ ▷ φ ⊢SKv ψ → Maybe (Γ ⊢SKv ψ)
str zero = nothing
str (suc d) = just d
str (app d e) with str d
... | nothing = nothing
... | just d' with str e
... | nothing = nothing
... | just e' = just (app d' e')
str KK = just KK
str SS = just SS

-- λ x → M x
-- lam (app d zero), str d = just d'
-- = d'

dedThm' : Γ ▷ φ ⊢SKv ψ → Γ ⊢SKv φ [⇒] ψ
dedThm' d with str d
... | just d' = app KK d'
... | nothing with d
... | zero = {!!}
... | suc x = {!!} --
... | app x x₁ = {!!}
... | KK = {!!} --
... | SS = {!!} --.

-- left as an exercise.
