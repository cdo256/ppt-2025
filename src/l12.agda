module l12 where
-- open import lib11
-- open import Data.List

x = 4 :: 3 :: []


data List_ : (A : Set) → Set where
  [] : List A
  _::_ : A → List A → List A

infixr :: 50

-- data RT : Set where
--   node : List RT → RT
-- 
-- myRose : RT
-- myRose = node (node []
--              :: node (node [] :: [])
--              :: node (node [] :: node [] :: []) :: [])
-- 
-- count : RT → ℕ
-- count (node []) = 1
-- count (node (t :: ts)) = count t + count (node ts)
-- 
-- sum :
