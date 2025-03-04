{-# OPTIONS --guardedness #-}
{- Exercise 04 Proofs,Programs and Types (PPT) -}

open import lib14
{- Exercise 04 

Part 1 - 40%
Part 2 - 40%
Part 3 - 20%

General advice: Don't try to be efficient! 

And don't try Part 3, unless you are bonkers.
-}

{- Part 1 : treesort -}

{- We define the type of trees with labels on the nodes -}

data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

{- here is an example tree -}
t : Tree ℕ
t = node (node leaf 1 (node leaf 2 leaf)) 5 leaf

{- Define a function tree2list which collects all the leaves from left to right in a list.-}

tree2list : Tree A → List A
tree2list leaf = []
tree2list (node t₁ x t₂) = (tree2list t₁) ++ (x ∷ (tree2list t₂))

{- Here is a simple unit test -}
t1 : List ℕ
t1 = tree2list t
{- 1 ∷ 2 ∷ 5 ∷ [] -}

{- We are going to produce sorted trees. 
   A sorted tree is one where for every node the leaves on the left have smaller values
   and the leaves on the right have larger values.

I give you a comparison function on ℕ -}

_<=?_ : ℕ → ℕ → Bool
zero <=? m = true
suc n <=? zero = false
suc n <=? suc m = n <=? m

{- Write a function that transforms a list of natural number into a sorted tree. -}


list2tree : List ℕ → Tree ℕ
list2tree [] = leaf
list2tree (x ∷ xs) = insert x (list2tree xs)
  where
    insert : ℕ → Tree ℕ → Tree ℕ
    insert n leaf = node leaf n leaf
    insert n (node t₁ m t₂) with (n <=? m)
    ... | false = node t₁ m (insert n t₂)
    ... | true = node (insert n t₁) m t₂

{- Hint: it may be a good idea to write a function
         insert : ℕ → Tree ℕ → Tree ℕ
    that inserts one value into a sorted tree maintaining its sortedness. -}

{- Here is a unit test for list2tree -}
l : List ℕ
l = 10 ∷ 2 ∷ 1 ∷ 5 ∷ []

t2 = list2tree l
{- node (node leaf 1 (node leaf 2 leaf)) 5 (node leaf 10 leaf) -}

{- Using the previous function it is now easy to define treesort
   a function that sorts lists. -}

treesort : List ℕ → List ℕ
treesort xs = tree2list (list2tree xs)

{- Here is a unit test for treesort. -}
t4 = treesort l
{- 1 ∷ 2 ∷ 5 ∷ 10 ∷ [] -}


{- Part 2 : treesort with folds

Iterators are also called folds (this actually comes form the operation for lists). 
The goal of this section is to reimplement the functions from the previous section 
using only folds for lists and trees which are defined below.
The functions should NOT use pattern matching on lists or trees or any recursion!
You are allowed to use pattern matching for other types. If in doubt ask on moodle.

If the original function is called x then the function with folds only is called x-f.
Hence implement the functions of part 1 using only fold and no pattern matching or
recursion.
-}

foldList : M → (A → M → M) → List A → M
foldList mnil mcons [] = mnil
foldList mnil mcons (x ∷ xs) = mcons x (foldList mnil mcons xs)

foldTree : M → (M → A → M → M) → Tree A → M
foldTree mleaf mnode leaf = mleaf
foldTree mleaf mnode (node l x r) =
         mnode (foldTree mleaf mnode l) x (foldTree mleaf mnode r)

tree2list-i : Tree A → List A
tree2list-i = foldTree [] (λ xs y zs → xs ++ (y ∷ zs))

{- Here is a simple unit test -}
t1-i : List ℕ
t1-i = tree2list-i t
{- 1 ∷ 2 ∷ 5 ∷ [] -}

{- Write a function that transforms a list of natural number into a sorted tree. -}

list2tree-i : List ℕ → Tree ℕ
list2tree-i = foldList leaf insert
  where
    doInsert : ℕ → (Tree ℕ × Tree ℕ) → ℕ → (Tree ℕ × Tree ℕ) → (Tree ℕ × Tree ℕ)
    doInsert n (t₁ , t₁') m (t₂ , t₂') with (n <=? m)
    ... | false = (node t₁ m t₂ , node t₁ m t₂') -- insert right
    ... | true  = (node t₁ m t₂ , node t₁' m t₂)
    insert : ℕ → Tree ℕ → Tree ℕ
    insert n t = proj₂ (foldTree (leaf , node leaf n leaf) (doInsert n) t)

{- Hint: it may be a good idea to write a function 
         insert : ℕ → Tree ℕ → Tree ℕ
    that inserts one value into a sorted tree maintaining its sortedness. -}

t2-i = list2tree-i l
{- node (node leaf 1 (node leaf 2 leaf)) 5 (node leaf 10 leaf) -}

{- Using the previous function it is now easy to define treesort
   a function that sorts lists. -}

treesort-i : List ℕ → List ℕ
treesort-i xs = tree2list-i (list2tree-i xs)

{- Here is a unit test for treesort. -}
t4-i = treesort-i l
{- 1 ∷ 2 ∷ 5 ∷ 10 ∷ [] -}


{- Part 3 

Conatural numbers. 

Health warning: Don't try this exercise unless you feel very clever.
You will get upto 80/100 without it, anyway. 

-}


{- Now your task is to define multiplication _*∞_ for conatural numbers.

This is harder then it sounds. Why? Because to check termination of corecursive programs 
agda needs to make sure that if you want to find out a finite amout of information about
the result of the function it only needs a finite amount of information about its inputs. 
Such a function is called productive. And agda isn't very clever in figuring this out, it
has to be obvious from the program (similar as structural recursion has to be obviously 
structural. 

If you need more hints, ask on moodle.
-}


-- _*∞1_ :  ℕ∞ → ℕ∞ → ℕ∞
-- pred∞ (m *∞1 n) with pred∞ m
-- ... | nothing = nothing
-- ... | just x with pred∞ n
-- ...          | nothing = nothing
-- ...          | just y = just (y +∞ (x *∞1 n))

-- _*∞2_ :  ℕ∞ → ℕ∞ → ℕ∞
-- pred∞ (m *∞2 n) with pred∞ m
-- ... | nothing = nothing
-- ... | just x with pred∞ n
-- ...          | nothing = nothing
-- ...          | just y = just ((y +∞ x) +∞ (x *∞2 y))

_*∞3_ :  ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m *∞3 n) with (pred∞ m , pred∞ n)
... | nothing , nothing = nothing
... | nothing , just _ = nothing
... | just m' , nothing = nothing
... | just m' , just n' = just ((n' +∞ m') +∞ (m' *∞3 n'))

ℕ⊎∞ = Maybe ℕ

data ℕ≤ (n : ℕ∞) : Set  where
  coinductive
  constructor suc_
  field
    limit : ℕ≤ → ℕ∞

ℕ∞≤ : (n : ℕ⊎∞) → (ℕ∞ × )

_*∞4_ :  ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m *∞4 n) with pred∞ m
... |  nothing = nothing
... |  just m' = just (pred∞ (m' *∞4 n))


_*∞_ : ℕ∞ → ℕ∞ → ℕ∞
_*∞_ = _*∞3_



x0 = ℕ∞→ℕ! (ℕ→ℕ∞ 0 *∞ ℕ→ℕ∞ 6)
x1 = ℕ∞→ℕ! (ℕ→ℕ∞ 3 *∞ ℕ→ℕ∞ 0)
x2 = ℕ∞→ℕ! (ℕ→ℕ∞ 5 *∞ ℕ→ℕ∞ 1)
x3 = ℕ∞→ℕ! (ℕ→ℕ∞ 1 *∞ ℕ→ℕ∞ 1)

{- My unit-test -}
x3*5 = ℕ∞→ℕ! (ℕ→ℕ∞ 3 *∞ ℕ→ℕ∞ 5)
{- 15 -}

