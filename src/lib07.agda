{- Lecture 07 COMP4074 -}

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

raa→tnd : RAA P → TND P
raa→tnd = {!!}


