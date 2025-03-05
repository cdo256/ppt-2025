{- Lecture 06 COMP4074 -}

open import lib05

{-
Propositions as types

to every proposition we associate
a type of evidence
Prop = Set (Type) , 1st approximation
proofs = programs
intuitionistic logic

classical : every proposition is either true
or false, Prop = Bool
P,Q : Bool
P ∧ Q = P && Q
P : ℕ → Bool
∀ x : ℕ, P x : Bool
-}

Prop = Set

infix 3 _∧_
_∧_ : Prop → Prop → Prop
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : Prop → Prop → Prop
P ∨ Q = P ⊎ Q

infix 1 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

infix 0 _⇔_
_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

True : Prop
True = ⊤

False : Prop
False = ⊥

¬_ : Prop → Prop
¬ P = P ⇒ False

variable P Q R : Prop

taut-0 : P ⇒ P
taut-0 p = p

fav-equiv : P ∧ (Q ∨ R) ⇔ P ∧ Q ∨ P ∧ R
proj₁ fav-equiv (p , inj₁ q) = inj₁ (p , q)
proj₁ fav-equiv (p , inj₂ r) = inj₂ (p , r)
proj₂ fav-equiv (inj₁ (p , q)) = p , (inj₁ q)
proj₂ fav-equiv (inj₂ (p , r)) = p , (inj₂ r)

not-an-iso : P ⇔ P ∨ P
proj₁ not-an-iso p = inj₁ p
proj₂ not-an-iso (inj₁ p) = p
proj₂ not-an-iso (inj₂ p) = p
-- proj₁ non-an-iso (proj₂ not-an-iso (inj₂ p)) = inj₁ p

dm1 : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
proj₁ dm1 npq = (λ p → npq (inj₁ p)) , λ q → npq (inj₂ q)
proj₂ dm1 (np , nq) (inj₁ p) = np p
proj₂ dm1 (np , nq) (inj₂ q) = nq q

dm2 : ¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q
proj₁ dm2 npnq = inj₁ (λ p → npnq (p , {!!}))
proj₂ dm2 (inj₁ np) (p , q) = np p
proj₂ dm2 (inj₂ nq) (p , q) = nq q
