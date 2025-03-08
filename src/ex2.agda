{- Exercise 02 Proofs,Programs and Types (PPT) -}

open import lib08 public
-- defines products, sums, logical connectives 

{- Part 1 : Logic poker (50%)

Try to prove the following propositions using Agda.

You may use the postulate raa (for classical logic) but you loose points
if you use it uneccessarily (i.e. if the proposition is provable intuitionistically.

If you think a proposition is unprovable (even using raa) then comment it out.

When deriving functions you can add arguments. This is often more
convenient then using λ because it is easier to use pattern matching.

You may also use auxilliary definitions.
-}

postulate
  raa : RAA P -- reductio ad absurdo
  tnd : TND P

{-
Not solvable classically (therefore not solvable intuitionistically either).
(⊥ ⇒ ⊤) ⇒ ¬ ⊥ ⇒ ¬ ⊤ is false as (⊥ ⇒ ⊤) is ⊤, ¬ ⊥ is ⊤, and ¬ ⊤ is ⊥, but it doesn't hold that ⊤ ⇒ (⊤ ⇒ ⊥).
By way of contradiciton, assume such a p1 exists, then
  p1 (λ _ → tt) (λ x → x) tt
must be of type bottom, a contradiciton so no such p1 exists.
-}
-- p1 : (P ⇒ Q) ⇒ ¬ P ⇒ ¬ Q
-- p1 = {!!}

p2 : (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
p2 pq nq = λ p → nq (pq p)

{- This is classically valid, but not intuitionistically valid.
For any P, let Q = P. then we can always construct a term with type P ⇒ P as the identity,
but that would mean p3 (λ x → x) : ¬ P ∨ P which is the excluded middle. Since we get the excluded middle for every P, it must not generally have a type with introducing an extra axiom/assumption. -}
-- pq : P → Q
-- raa : ((P → ⊥) → ⊥) → P
p3 : TND P → (P ⇒ Q) ⇒ ¬ P ∨ Q
p3 (inj₁ p) pq = inj₂(pq p)
p3 (inj₂ np) pq = inj₁ np

-- Classically valid, but not intuitionistically valid.
-- p4 : RAA Q → ¬ P ∨ Q ⇒ (P ⇒ Q)
-- p4 raa (inj₁ np) p =  raa (λ nq → (np p))
-- p4 raa (inj₂ q) p = q

p4 : ¬ P ∨ Q ⇒ (P ⇒ Q)
p4 (inj₁ np) p = case⊥ (np p)
p4 (inj₂ q) p = q


-- (((P → ⊥) → ⊥) → P) → (((P → (P → ⊥)) , ((P → ⊥) → P)) → ⊥)
-- p5 : RAA P → ¬ (P ⇔ ¬ P)
-- p5 nnp→p (pnp , npp) =
--   let p = (nnp→p (λ np → pnp (npp np) (npp np)))
--   in pnp p p
   
p5 : ¬ (P ⇔ ¬ P)
p5 {P = P} (pnp , npp) =
  let np : ¬ P
      np = λ p →  pnp p p
      p : P
      p = npp np
  in np p
  
-- Not classically valid, because,
-- ¬ (⊤ ∨ ¬ ⊤) = ¬ ⊤ = ⊥
-- p6 : ¬ (P ∨ ¬ P)
-- p6 = {!!}

-- (((P → ⊥) → ⊥) → ⊥) → (P → ⊥)
p7 :  ¬ (¬ (¬ P)) ⇒ ¬ P
p7 nnnp p = nnnp (λ np → np p)

-- NOTE: Possible with just one of TND P or RAA (((P ⇒ Q) ⇒ P) ⇒ P)

-- Possible with fewer postulates. See note below.
p8 : TND P → RAA (P ⇒ Q) → RAA Q → ((P ⇒ Q) ⇒ P) ⇒ P
p8 (inj₁ p) _ _ _ = p
p8 (inj₂ np) raa₁ raa₂ pqp =
  pqp (raa₁ (λ npq → npq ( λ p → raa₂ (λ nq → np p))))

-- We find a term, raa⇒ below of type RAA Q → RAA (P → Q). However I'm assuming
-- that I can't use it or recreate a term of that type, otherwise a term p8' exists, as defined below:
p8' : TND P → RAA Q → ((P ⇒ Q) ⇒ P) ⇒ P
p8' tnd raa =
  let raa⇒ nnq→q = λ nnp→q p → nnq→q (λ nq → nq ((case⊥ ((nnp→q (λ p→q → nq (p→q p)))) )))
  in
  p8 tnd (raa⇒ raa) raa


{- Part 2 : Negative translation (50%)
            (section 3.4. of the lecture notes) -}

raa∧ : RAA P → RAA Q → RAA (P ∧ Q)

raa⇒ : RAA Q → RAA (P ⇒ Q)
raa¬ : RAA (¬ P)
raa∨ᶜ : RAA (P ∨ᶜ ¬ P)

{- and derive excluded middle -}

tndᶜ : P ∨ᶜ ¬ P

{- and the standard combinators for disjunction
   (we need to assume that goal satisfies RAA) -}

inj₁ᶜ : P → P ∨ᶜ Q
inj₂ᶜ : Q → P ∨ᶜ Q
caseᶜ : RAA R → (P → R) → (Q → R) → P ∨ᶜ Q → R

{- We can also show that all the other operations
   preserve RAA -}

{- Hence we can define a classical proposition as one
   that satisfies RAA and translate any classical proof. -}

{- Complete the proofs! You should not use classical logic (raa) here!-}

raa∧ nnp→p nnq→q =
  (λ nnp∧q → nnp→p (λ np → nnp∧q (λ (p , q) → np p)) ,
             nnq→q (λ nq → nnp∧q (λ (p , q) → nq q)))
raa⇒ nnq→q = λ nnp→q p → nnq→q (λ nq → nq (case⊥ (nnp→q (λ p→q → nq (p→q p)))))
-- We've already found a term of exactly this type, so just use that.
raa¬ = p7
raa∨ᶜ = λ nnp∨q → λ (np , nnp) → nnp np

inj₁ᶜ = λ p → λ (np , nq) → np p
inj₂ᶜ = λ q → λ (np , nq) → nq q

caseᶜ nnr→r p→r q→r p∨q =
  nnr→r λ nr → p∨q ((λ p → nr (p→r p)),
                    (λ q → nr (q→r q)))

tndᶜ = λ (np , nnp) → nnp np
