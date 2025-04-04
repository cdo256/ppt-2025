{-# OPTIONS --guardedness --without-K #-}
{- Exercise 8, G54PPT (COMP4074) 2025 -}
{- BONUS EXERCISE

Can replace the previous exercise with the lowes number of marks.
Otherwise it won't count for the final mark.
-}

open import lib25

{-
Part 1 :

Prove uniqueness of equality proofs for |_≡_ {ℕ}| without using |K|, that is with the flag
--without-K+ enabled. 
-}

-- J : (M : {a b : A} → (a ≡ b) → Set)
--     → ({a : A} → M (refl {a = a}))
--     → {a b : A}(p : a ≡ b) → M p

-- J-PM = {A : Set}{a : A}(M : {b : A} → (a ≡ b) → Set)
--     → (M (refl {a = a}))
--     → {b : A}(p : a ≡ b) → M p



injSuc-cong : {m n : ℕ} → (p : suc m ≡ suc n) → p ≡ cong suc (injSuc p)
injSuc-cong {m} {n} p = J (λ {a} {b} q → {!q ≡ cong suc q!}) {!!} {!!}
  where M' : (m n : ℕ) → {q r : m ≡ n} → q ≡ r → Set
        M' m n {q} {r} eq = {!cong suc (injSuc q) ≡ cong suc (injSuc r)!}

Irrelevant : Set
Irrelevant = ∀ {x y : ℕ} (p q : x ≡ y) → p ≡ q

UIP : Set
UIP = Irrelevant

norm : {m n : ℕ} → m ≡ n → m ≡ n
norm {m} {n} q with (m ≡? n)
... | yes p = p
... | no np = case⊥ (np q) 

norm-const : ∀ {a b : ℕ} (p q : a ≡ b)
           → norm p ≡ norm q
norm-const {a} {b} p q with (a ≡? b)
... | yes _ = refl
... | no neq = case⊥ (neq p)

trans-sym : ∀ {a b : ℕ} (p : a ≡ b)
          → trans (sym p) p ≡ refl
trans-sym refl = refl

canonical : (f : {a b : ℕ} → a ≡ b → a ≡ b)
          → ∀ {a b : ℕ} (p : a ≡ b)
          → trans (sym (f refl)) (f p) ≡ p
canonical f {a} {b} refl = trans-sym (f refl)

constant→UIP : (f : {a b : ℕ} → a ≡ b → a ≡ b)
             → ({a b : ℕ}(p q : a ≡ b) → f p ≡ f q)
             → UIP
constant→UIP f f-const p q = begin
  p
    ≡⟨ sym (canonical f p) ⟩
  trans (sym (f refl)) (f p)
    ≡⟨ cong (trans _) (f-const p q) ⟩
  trans (sym (f refl)) (f q)
    ≡⟨ canonical f q ⟩
  q
  ∎

uipℕ : {m n : ℕ}(p q : m ≡ n) → p ≡ q
uipℕ {m} {n} = constant→UIP norm norm-const

{-
Part 2 : Show that the Pierce formula is not provable
-}

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

id : • ⊢ Atom "P" [⇒] Atom "P"
id = lam zero

maxℕ : ℕ → ℕ → ℕ
maxℕ zero n = n
maxℕ (suc m) zero = m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

ord : Form → ℕ
ord (Atom _) = 1
ord (φ [⇒] ψ) = maxℕ (ord φ) (ord ψ) + 1

-- np : (• ⊢ φ) → Σ[ ψ ∈ Form ]
--                (Σ[ χ ∈ Form ]
--                 (φ ≡ (ψ [⇒] χ)))
-- np (app {φ = φ} p q) = {!!}
-- np p = {!!}

npq : ¬ (• ⊢ Atom "P" [⇒] Atom "Q")
npq (lam (suc pq)) = {!!}
npq (lam (app pq pq₁)) = {!!}
npq (app pq pq₁) = {!!}

P-F : Form
P-F = ((Atom "P" [⇒] Atom "Q") [⇒] Atom "P") [⇒] Atom "P"

Assignment : Set
Assignment = String → Bool

⟦⇒⟧ : Bool → Bool → Bool
⟦⇒⟧ false false = true
⟦⇒⟧ false true = true
⟦⇒⟧ true false = false
⟦⇒⟧ true true = true

⟦_⟧_ : Form → Assignment → Bool
⟦ Atom x ⟧ ρ = ρ x
⟦ φ [⇒] ψ ⟧ ρ = ⟦⇒⟧ (⟦ φ ⟧ ρ) (⟦ ψ ⟧ ρ)

no-pierce-assign : ∀ {ρ : Assignment} → ⟦ P-F ⟧ ρ ≡ false
no-pierce-assign {ρ} with (ρ "P") | (ρ "Q")
... | false | false = {!!}
... | false | true  = {!!}
... | true  | false = {!!}
... | true  | true  = {!!}

no-pierce : ¬ (• ⊢ P-F)
no-pierce x = {!!}

np : ∀ (ϕ : Form) → ¬ (• ⊢ Atom s)
np s (app p q) = {!!}
