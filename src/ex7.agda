{-# OPTIONS --guardedness #-}
{- Exercise 7, G54PPT (COMP4074) 2025 -}
open import lib23

{- Part 1 (80%)

we define binary trees (BT), show that equality of binary trees is
decidable.

-}

data BT : Set where
  leaf : BT
  node : BT → BT → BT

no-node-leaf : {t u : BT} → ¬ (node t u ≡ leaf)
no-node-leaf = λ ()

cong-node : {t₁ t₂ u₁ u₂ : BT}
          → (t₁ ≡ u₁)
          → (t₂ ≡ u₂)
          → (node t₁ t₂ ≡ node u₁ u₂)
cong-node {t₁} {t₂} {u₁} {u₂} ≡1 ≡2 =
  trans (cong (λ x → node x t₂) ≡1)
        (cong (λ x → node u₁ x) ≡2)

inj-node : {t₁ t₂ u₁ u₂ : BT}
         → (node t₁ t₂ ≡ node u₁ u₂)
         → (t₁ ≡ u₁) × (t₂ ≡ u₂) 
inj-node refl = refl , refl

_≡BT?_ : (t u : BT) → Dec (t ≡ u)
leaf ≡BT? leaf = yes refl
leaf ≡BT? node u v = no (λ x → no-node-leaf (sym x))
node t t₁ ≡BT? leaf = no (λ x → no-node-leaf x)
node t₁ t₂ ≡BT? node u₁ u₂ with (t₁ ≡BT? u₁) | (t₂ ≡BT? u₂)
... | yes x | yes y = yes (cong-node x y)
... | yes _ | no ny =
  no (λ z → ny (proj₂ (inj-node z)))
... | no nx | _ =
  no (λ z → nx (proj₁ (inj-node z)))


{- Part 2 (20 %) 

We are back at division again, but this time the goal is to implement
division together with its correctness proof which means we need to
write a function that constructs elements of DivSpec.

-}

fin2nat : Fin n → ℕ
fin2nat zero = zero
fin2nat (suc i) = suc (fin2nat i)

record DivSpec (m n : ℕ) : Set where
  field
    div : ℕ
    rem : Fin (suc n)
    eq : m ≡ fin2nat rem + div * (suc n)

open DivSpec

-- If m, n : ℕ s.t. m ≤ n then return an equivalent m' : Fin (suc n).
-- Essentially nat2fin
fin-embed : (m n : ℕ) → m ≤ n → Σ[ m' ∈ Fin (suc n) ] (fin2nat m' ≡ m) 
fin-embed _ _ le-0 = zero , refl
fin-embed (suc m') (suc n') (le-SS leq) with (fin-embed m' n' leq)
... | pred , eq = suc pred , cong suc eq

-- If m : Fin (n + 1) and m != n then m + 1 ≤ n  
fin-le : (n : ℕ) → (m : Fin (suc n)) → ¬ (fin2nat m ≡ n) → (fin2nat (suc m) ≤ n)
fin-le zero zero 0≢0 = case⊥ (0≢0 refl)
fin-le (suc n) zero 0≢n' = le-SS le-0
fin-le (suc n) (suc m) m'≢n' =
  le-SS (fin-le n m (λ m≡n → m'≢n' (cong suc m≡n)))

-- Given a finite natural m such that m != max,
-- return a natural one larger, with a proof that it's one larger.
fin-suc : {n : ℕ} → (m : Fin (suc n))
        → ¬ (fin2nat m ≡ n)
        → Σ[ sm ∈ Fin (suc n) ] (fin2nat sm ≡ suc (fin2nat m)) 
fin-suc {n} m n'≢m' =
  fin-embed (fin2nat (suc m)) n 
            (fin-le n m n'≢m')

-- Compute the successor divSpec
step : (m n : ℕ) → DivSpec m n → DivSpec (suc m) n
step m n record { div = d ; rem = r ; eq = e } with (fin2nat r ≡? n )
... | yes r≡n = record
      { div = suc d
      ; rem = zero
      ; eq = cong suc (trans e (cong (λ z → z + d * suc n) r≡n))
      }
... | no r≢n = let (r' , eq) = fin-suc {n} r r≢n in record
      { div = d
      ; rem = r'
      ; eq = trans (cong suc e)
                   (cong (λ x → x + d * suc n) (sym eq))
      }

-- Recurse on m
_÷_ : (m n : ℕ) → DivSpec m n
zero ÷ n = record
    { div = 0
    ; rem = zero
    ; eq = refl
    }
suc m ÷ n = step m n (m ÷ n)

_mod_ : (m n : ℕ) → ℕ
_mod_ m n = fin2nat (rem (m ÷ n))

_div_ : (m n : ℕ) → ℕ
_div_ m n = div (m ÷ n)
