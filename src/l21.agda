open import lib21

{-
sort : List N -> List N
Sorted : List N -> List N -> Prop
Perm : List N -> List N -> Set--
-}

eqN : N -> N -> Bool
eqN zero zero = true
eqN zero (suc n) = false
eqN (suc m) zero = false
eqN (suc m) (suc n) = eqN m n

variable l m n : N

eqNok : m == n iff eqN m n == true

-- decidable vs decided
data Dec (A : Set) : Set where
 yes : A -> Dec A
 no : ¬ A -> Dec A

no-conf : ¬ (zero == suc n)
no-conf ()

injSuc : suc m = suc n -> m = n
injSuc refl = refl

_==?_ : (m n : N) -> Dec (m == n)
zero ==? zero = yes refl
zero ==? suc n = no no-conf
suc m ==? zero = no (\ p -> no-conf (sym p))
suc m == suc n with m ==? n
... | yes p = yes (conj suc p)
... | no np = no (\ mn -> np injSuc)

-- Decidable halts
-- Decidable doesn't always halt
--
-- Curch's thesis = All N -> N are computable.
-- (Church thesis) => ¬EM
-- CT => All functions are computable 
-- EM => all propositions are decidable
--
-- _==_ {A = N -> Bool} -- not decidable as requires infinite checking to validate.
-- Requires CT to prove it is undecidable.
