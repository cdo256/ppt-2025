{- Lecture 10 COMP4074 -}

open import lib10 public

-- Ackermann with It

acks : ℕ → ℕ → ℕ → ℕ
acks zero     m n        = suc n
acks (suc l)  m zero     = m
acks (suc l)  m (suc n)  = acks l m (acks (suc l) m n)

ack-it : ℕ → ℕ → ℕ → ℕ
ack-it = It {M = ℕ → ℕ → ℕ} (λ m n → suc n)
            λ acks-l m → It m (λ acks-skl-m-n → acks-l m acks-skl-m-n)

-- System with RR and higher order functions (typed λ calculus)
-- is called System T. Goedel?

-- datatypes (inductive types)
-- List
-- Trees : Expression trees, rose trees
-- Ordinals

infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A -- \::  

l123 : List ℕ
l123 = 1 ∷ 2 ∷ 3 ∷ []  -- [1,2,3]

_++_ : List A → List A → List A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

-- ℕ = List ⊤, + = ++

ItList : M → (A → M → M) → List A → M
ItList m-nil m-cons [] = m-nil
ItList m-nil m-cons (a ∷ as) = m-cons a (ItList m-nil m-cons as)
-- fold

_++i_ : List A → List A → List A
_++i_ = ItList (λ bs → bs) (λ a as++ bs → a ∷ as++ bs)

data Expr : Set where
  const : ℕ → Expr
  _[+]_ : Expr → Expr → Expr
  _[*]_ : Expr → Expr → Expr

-- 2 * (3 + 1)
e0 : Expr
e0 = (const 2) [*] ((const 3) [+] (const 1)) 

eval : Expr → ℕ
eval (const x) = x
eval (e [+] f) = eval e + eval f
eval (e [*] f) = eval e * eval f

ItTree : (ℕ → M) → (M → M → M) → (M → M → M) → Expr → M
ItTree m-c m-+ m-* (const n) = m-c n
ItTree m-c m-+ m-* (e [+] f) =
  m-+ (ItTree m-c m-+ m-* e) (ItTree m-c m-+ m-* f)
ItTree m-c m-+ m-* (e [*] f) = 
  m-* (ItTree m-c m-+ m-* e) (ItTree m-c m-+ m-* f)

eval-i :  Expr → ℕ
eval-i = ItTree (λ x → x) _+_ _*_ 
-- λ e-e e-f → e-e + e-f
-- = λ e-e e-f → _+_ e-e e-f
-- = _+_

data RT : Set where
  node : List RT → RT

myRose : RT
myRose = node (node []
              ∷ node (node              ∷ node (node [] ∷ node [] ∷ []) ∷ [])

              ∷ node (node [] ∷ node [] ∷ []) ∷ [])

              ∷ node (node [] ∷ node [] ∷ []) ∷ [])

 [] ∷ [])
              ∷ node (node [] ∷ node [] ∷ []) ∷ [])

count : RT → ℕ
count = {!!}

sum : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

count'' : RT → ℕ
map-count'' : List RT → List ℕ
count'' (node ts) = 1 + sum (map-count'' ts)
map-count'' [] = []
map-count'' (t ∷ ts) = count'' t ∷ map-count'' ts

{-# TERMINATING #-}

{-
RT = μ List
F : Set → Set
Functor F : (A : Cat) → (B : Cat)
st for any x → y in A
F(x) → F(y) is in B
(and commutitivity is preserved.)
-}
-- Generalized inductive type
-- Initial Algebra of a functor F
data μ F : Set where
        con : F (μ F) → μ F
mapF : (A → B) → (F A → F B)
mapF id = id
mapF (f ∘ g) = mapF f ∘ mapF g

It-μF : (F M → M) → μ F → M
It-μF f (con x) = f (map (It-μF x))

ℕ = μ Maybe
-- Maybe X = 1 ⊎ X

It : M → (M → M) → ℕ → M
It-μ Maybe : (Maybe M → M) → ℕ → M


