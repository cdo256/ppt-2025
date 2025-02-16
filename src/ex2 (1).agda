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


p1 : (P ⇒ Q) ⇒ ¬ P ⇒ ¬ Q
p1 = {!!}

p2 : (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
p2 = {!!}

p3 : (P ⇒ Q) ⇒ ¬ P ∨ Q
p3 = {!!}

p4 : ¬ P ∨ Q ⇒ (P ⇒ Q)
p4 = {!!}

p5 : ¬ (P ⇔ ¬ P)
p5 = {!!}

p6 : ¬ (P ∨ ¬ P)
p6 = {!!}

p7 :  ¬ (¬ (¬ P)) ⇒ ¬ P
p7 = {!!}

p8 : ((P ⇒ Q) ⇒ P) ⇒ P
p8 = {!!}


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

raa∧ = {!!}
raa⇒ = {!!}
raa¬ = {!!}
raa∨ᶜ = {!!}

inj₁ᶜ = {!!}
inj₂ᶜ = {!!}

caseᶜ = {!!}

tndᶜ = {!!}
