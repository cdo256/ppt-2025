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

-- infix 5 _⊢_
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

-- semantics : meaning

-- environment  truth assignment
-- assigns a proposition to each atom

Env = String → Prop

myEnv : Env
myEnv "P" = ⊥
myEnv "Q" = ⊤
myEnv _ = ⊥

variable ρ : Env

⟦_⟧ : Form → Env → Prop -- \[[ .. \]], Scott brackets
⟦ Atom x ⟧ ρ = ρ x
⟦ φ [⇒] ψ ⟧ ρ = ⟦ φ ⟧ ρ → ⟦ ψ ⟧ ρ  -- meta-circular

⟦_⟧C : Con → Env → Prop
⟦ • ⟧C ρ = ⊤
⟦ Γ ▷ φ ⟧C ρ = ⟦ Γ ⟧C ρ ∧ ⟦ φ ⟧ ρ

sound : Γ ⊢ φ → ⟦ Γ ⟧C ρ → ⟦ φ ⟧ ρ
sound zero (γ , x) = x
sound (suc d) (γ , x) = sound d γ
sound (lam d) γ = λ x → sound d (γ , x)
sound (app d e) γ = (sound d γ) (sound e γ)

no-d : ¬ (• ⊢ bad)
no-d d = sound {ρ = myEnv} d tt (λ x → tt) tt

-- soundness : everything which is provable is true
-- completeness : everything which is true is provable

complete : ({ρ : Env} →  ⟦ Γ ⟧C ρ → ⟦ φ ⟧ ρ) → Γ ⊢ φ
complete = {!!}


pierce : ((P ⇒ Q) ⇒ P) ⇒ P
pierce = λ f → f (λ p → {!!})
-- P = ⊥ , (P ⇒ Q) ⇒ P = ⊤, P ⇒ Q = ⊥ not possible

P-F : Form
P-F = ((Atom "P" [⇒] Atom "Q") [⇒] Atom "P") [⇒] Atom "P"

-- no-pierce : ¬ (• ⊢ P-F)
-- no-pierce = {!!}

-- variable ϕ ψ θ : Form

infix 5 _⊢_
infixl 8 _▹_

-- data _⊢_ : Con → Form → Set where
--   zero : Γ ▹ ϕ ⊢ ϕ
--   suc : Γ ▹ ϕ → Γ ▹ ψ ⊢ ϕ
--   lam : Γ ▹ ϕ ⊢ ψ → GG ⊢ ϕ [⇒] ψ
--   app : Γ ⊢ ϕ [⇒] ψ → Γ ⊢ ϕ → Γ ⊢ ψ

infix 5 ⊢SK_

data ⊢SK_ : Form → Set where
  KK : ⊢SK φ [⇒] ψ [⇒] φ
  SS : ⊢SK (φ [⇒] ψ [⇒] θ) [⇒] (φ [⇒] ψ) [⇒] (φ [⇒] θ)
  app : ⊢SK φ [⇒] ψ → ⊢SK φ → ⊢SK ψ

II : ⊢ ϕ [⇒] ϕ
II {ϕ = ϕ} = app (app SS KK) (KK {ψ = ϕ})

k-d : • ⊢ ϕ [⇒] ψ [⇒] ϕ
k-d = lam (lam (suc zero))
s
s-d : • ⊢ (ϕ [⇒] ψ [⇒] θ) [⇒] (ϕ [⇒] ψ) [⇒] (ϕ [⇒] θ)
s-d = lam (lam (lam (app (app (suc (suc zero)) zero)
                         (app (suc zero) zero)))) 

infix 5 _⊢SKv_`

data _⊢SKv_ : Con → Form → Set where
  zero : Γ ▹ φ ⊢SKv ϕ
  suc : Γ ▹ ϕ → Γ ▹ ψ ⊢SKv ϕ
  lam : Γ ▹ ϕ ⊢SKv ψ → GG ⊢SKv ϕ [⇒] ψ
  app : Γ ⊢SKv ϕ [⇒] ψ → Γ ⊢SKv ϕ → Γ ⊢SKv ψ
  SS : • ⊢ ϕ [⇒] ψ [⇒] ϕ
  KK : • ⊢ (ϕ [⇒] ψ [⇒] θ) [⇒] (ϕ [⇒] ψ) [⇒] (ϕ [⇒] θ)

eqLem : Γ ⊢ ϕ → Γ ⊢SKv ϕ
eqLem = ? -- recursively pattern match.
eqLem zero = zero
eqLem (suc d) = suc (eqLem d)
eqLem (lam d) = ?
eqLem (app d e) (eqLem d) (eqLem e)

skvLem : • ⊢SKv ϕ → SKv ϕ
skvLem (app d e) = app (skvLem d) (skvLem e)

dedThm : Γ ⊢ ϕ → Γ ⊢SKv ϕ [⇒] ψ
proj₂ dedThm zero = II
-- (λ x. M) M N  = ? S (λ x → M) (λ x → M N)
proj₂ dedThm (suc d) = ? -- x deesn't occur in M
proj₂ ddedThm λ → K = K K
proj₂ dedThm KK = app KK k-d
proj₂ dedThm SS = s-d
proj₂ dedThm (app d e) = app (proj₂ eqThm d) (proj₂ eqThm e)

-- strenthi=ens a derivation. Gives us a definition of
str : Γ ▹ φ ⊢SKv ψ → Maybe (Γ ⊢SKv) when
str zero = nothing
str (suc d) = d
str (app d e) with just (str d)
... | nothing = nothing
... | just d' with str e as
 ... |nothing = nothing
 ... | just e' just (app d' e')
 str KK = just KK
 str SS = just SS 


-- exercise
-- λ x → M
-- lam (app d zero), str d = just d'
-- d = d'
dedThm' : Γ ▹ φ ⊢SKv ψ → Γ ⊢ SKv φ [⇒] ψ
dedThm' d with string d
... | just d' = app KK d'
... | nothing = with d
... | zero = nothing
... | suc x = ?
... | app x y = ?
... | KK = ?
... | SS = ?
