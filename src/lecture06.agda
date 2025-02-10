
-- propositions are sets of types ??


Prop = Sets

_∧_ : Prop → Prop → Prop
P ∧ Q = { }0

_∨_ : Prop → Prop → Prop
P ∨ Q = { }1

_⇒_ : Prop → Prop → Prop
P ⇒ Q = { }2

_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) × (Q ⇒ P)

True : Prop
True = ⊤

False : Prop
False = ⊥

¬_ : Prop → Prop
¬_ P = P ⇒ False

-- variable P Q R : Prop
-- 
-- taut-0 : P => P
-- taut-0 p = p
-- 
-- fav-equiv : P ∧ (Q ∨ R) ⇔ P ∧ Q ∨ (P∧ R)
-- proj_1 fav-equiv (p , inj_1 q) = inj_1 (p , q)
-- proj_1 fav-equiv (p , inj_2 q) = inj_2 (p , r)
-- proj_2 fav-equiv (inj_1 (p , q)) = (p , (inj_1 q))
-- proj_2 fav-equiv (inj_2 (p , q)) = (p , (inj_2 q))
-- 
-- Direct inverse therefore isomorphism
-- 
-- not-an-iso : P ⇔ P ∨ P
-- proj_1 not-an-iso p = inj_1 p
-- proj_2 not-an-iso inj_1 p = p
-- proj_2 not-an-iso inj_2 p = p
-- 
-- dm1 : ¬(P ∨ Q) ⇔ (¬ P ∨ ¬q)
-- proj_1 dm1 npq = (λ p -> npq (inj_1 p)) , λ q -> npq (proj_2)
-- proj_2 dm1 (np , nq) (inj_1 p) = np p
-- proj_2 dm1 (np , nq) (inj_2 q) = np q
-- , λ q -> npq (proj_2)
-- 
-- j-- Intuistinistic system, so can't prove the forward direction.
-- -- Types ∏
-- 
-- dm2 : ¬ (P ∧ Q) ⇔ (¬ P ∨ ¬ q)
-- prj_1 dm2 npq =
