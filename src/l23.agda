open import lib22

-- |- 0 \le n
-- m \le n |- s(m) \le s(n)
--

data _\le_ : N -> N -> Set where
 le-0 : 0 \le n
 le-SS : m \le n -> suc m \le suc n

-- p q : m \le n -> p \== q , isProp
-- so they are oismorphic

le13 : 1 \le 3
le13 = le-SS le-0

refl\le : (m : N) -> m \le m
relf\le zero = le-0
relf\le (suc m) = le-SS (refl\le m)

trans\le : (l m n : N) -> l \le m -> m \le n -> l \le n
trans l m n le-0 mn = le-0
trans (suc l) (suc m) (suc n) (le-SS lm') (le-SS mn') = le-ss (trans l m n lm' mn')

antisym\le : m \le n \to n \le m \to m \== n
antisym\le le-0 le-0 = relf
antisym\le (le-SS mn nm) = cong (antisym\le mn nm)

leb : N -> N -> Bool
leb 0 n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

leSS-inv : suc m \le suc n -> m \le n
leSS-inv (le-SS mn) = mn

_\le?_ : (m n : N) -> Dec (m \le n)
0 \le? n = yes le-0
(suc m) \le? zero = no (\ ()) 
(suc m) \le? (suc n) with m \le? n
... | yes mn = yes (le-SS mn)
... | no ¬mn = no (\ mn' -> (¬mn (leSS-inv ¬mn)))

data _\le'_ : N -> N -> Set where
 le-refl : n \le n
 le-S : m \le n -> m \le suc n

le'-0 : 0 \le' n
le'-0 {0} = le'-refl
le'-0 {suc n} = le'-S (le'-0 {n = n}) 

le'-SS : m \le' n -> (suc m) \le' (suc n) 
le'-SS le'-refl = le'-refl
le'-SS (le'-S mn) = le'-S (le'-SS mn)

le-S : m \le n -> m \le suc n
le-S le-0 = le-0
le-S (le-SS mn) = 

leq : \le \~= \le' 
\phi leq le-0 = \phi leq le 

isProp\le : (p q : m \le n) -> p \== q
isProp\le le-0 le-0 = refl
isProp\le (le-SS p) (le-SS q) = cong le-SS (isProp\le p q) 

-- only 'reasonable' equality on sets is isomorphism (since we can't talk about elements)
--
--

-- Simplex category is created by combining le-0, le-SS, and le-S into on type:
-- m \le' n = \Delta i (suc m) (suc n)

