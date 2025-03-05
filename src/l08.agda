{- Lecture 08 COMP4074 -}

open import lib06 public

dm1 : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
proj₁ dm1 h = (λ p → h (inj₁ p)) , λ q → h (inj₂ q)
proj₂ dm1 (np , nq) (inj₁ p) = np p
proj₂ dm1 (np , nq) (inj₂ q) = nq q

-- excluded middle P ∨ ¬ P
-- tertium non datur - the 3rd is not given

TND : Prop → Prop
TND P = P ∨ ¬ P 

dm2 : TND P → ¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q
proj₁ (dm2 (inj₁ p)) h = inj₂ (λ q → h (p , q))
proj₁ (dm2 (inj₂ np)) h = inj₁ np
proj₂ (dm2 pnp) (inj₁ np) (p , q) = np p
proj₂ (dm2 pnp) (inj₂ nq) (p , q) = nq q

-- indirect proof: to prove P, show that ¬ P is false (¬ ¬ P)
-- Reductio ad absurdum , reduction to the absurd

aar : P → ¬ ¬ P
aar p np = np p

RAA : Prop → Prop
RAA P = ¬ ¬ P → P

-- exercise : dm2 using RAA
-- RAA ? → ¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q

tnd→raa : TND P → RAA P
tnd→raa (inj₁ p) h = p
tnd→raa (inj₂ np) h = case⊥ (h np)

{-
raa→tnd : RAA P → TND P
raa→tnd = {!!}
unprovable
-}

-- |/- ∀ P : Prop . TND P
-- |/- ¬ (∀ P : Prop . TND P)
nntnd : ¬ ¬ (TND P)
nntnd h = h (inj₂ (λ p → h (inj₁ p)))

-- ¬ (TND P) = (P ∨ ¬ P) → ⊥
-- ⇔ ¬ P ∧ ¬ ¬ P

raa→tnd : RAA (P ∨ ¬ P) → TND P
raa→tnd h = h nntnd

-- How to understand classical logic
-- Prop = Bool works for prop logic
-- but not for predicate logic, P : ℕ → Prop
-- ∀ x : ℕ, P x : Prop

-- CProp̂p = { P : Prop | RAA P } -- negative propositions

negative translation

-- RAA P, RAA Q
-- ? : RAA (P ∧ Q)
-- ? : RAA (P ⇒ Q), don't need RAA P
-- ? : RAA True
-- ? : RAA False
-- ? : RAA (¬ P)  for any P
-- ¬ ¬ ¬ P → ¬ P
-- P ∨ᶜ Q = ¬ (¬ P ∧ ¬ Q)
-- ? : RAA (P ∨ᶜ Q)

-- inj₁ᶜ : P → P ∨ᶜ Q
-- inj₂ᶜ : Q → P ∨ᶜ Q
-- caseᶜ : (P → R) → (Q → R) → P ∨ᶜ Q → R , need RAA R

-- P : A → Prop
-- ∀ x : A, RAA (P x)
-- RAA (∀ x : A, P X)
-- ∃ᶜ x : A, P x = ¬ (∀ x : P, ¬ P x)

-- CPS-translation, continuation passing style
-- use return type R
-- translate A to (A → R) → R
-- call-cc corresponds to TND








