{- Exercise 3 Proofs,Programs and Types (PPT) -}

open import lib10

{- Part 1 : Recursion via patterns

Define the following functions using pattern matching and structural
recursion on the natural numbers.  -}

-- Define a function even that determines whether its input is even.
even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

-- tests:
-- even 3 = false
-- even 6 = true

-- Define a function sum that sums the numbers from 0 unil n-1
sum : ℕ → ℕ
sum zero = zero
sum (suc n) = n + (sum n)

-- tests
-- sum 2 = 1
-- sum 3 = 3
-- sum 10 = 45

-- Define a function max that calculates the maximum of 2 numbers
max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = 1 + max n m

-- tests
-- max 2 3 = 3
-- max 10 1 = 10

-- Define a function fib which calculates the nth item of the
-- Fibonacci sequence: 1,1,2,3,5,8,13
-- (each number is the sum of the two previous ones).
fib : ℕ → ℕ
fib k = fib' k 0 1
  where
    fib' : ℕ → ℕ → ℕ → ℕ
    fib' (suc k) n m = fib' k m (n + m)
    fib' zero n m = m

-- tests
-- fib 0 = 1
-- fib 6 = 13

-- natural less than or equal
infix 50 _≤_
_≤_ : ℕ → ℕ → Bool
zero ≤ n = true
(suc m) ≤ zero = false
(suc m) ≤ (suc n) = m ≤ n

-- boolean and
infix 30 _and_
_and_ : Bool → Bool → Bool
true and true = true
_ and _ = false

-- Define a function eq that determines wether two numbers
-- are equal.
eq : ℕ → ℕ → Bool
eq n m = n ≤ m and m ≤ n

-- tests
-- eq 4 3 = false
-- eq 6 6 = true

-- remdiv n m = (n % (suc m), n / (suc m))
remdiv : ℕ → ℕ → (ℕ × ℕ)
remdiv n q = iterate n (0 , 0)
  where
    iterate : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
    iterate zero (r , d) = (r , d)
    iterate (suc n) (r , d) =
      if eq r q
      then iterate n (0 , suc d)
      else iterate n (suc r , d)

-- Define a function rem such that rem m n returns the remainder
-- when dividing m by suc n (this way we avoid division by 0).
rem : ℕ → ℕ → ℕ
rem n m = proj₁ (remdiv n m)

-- tests
-- rem 5 1 = 1
-- rem 11 2 = 2

-- Define a function div such that div m n returns the result
-- of dividing m by suc n (ignoring the remainder)
div : ℕ → ℕ → ℕ
div n m = proj₂ (remdiv n m)

-- tests
-- div 5 1 = 2
-- div 11 2 = 3


{- Part 2 : Iterator and recursor

Define all the functions of part 1 but this time only use the 
iterator It and/or the recursor RR (defined in lib10).

Naming convention if the function in part 1 is called f then call it 
f-i if you only use the iterator, but f-r if you use the recusor (and possibly the iterator. 

Test the functions with at least the same test cases.
  -}

-- Define a function even that determines whether its input is even.
not : Bool → Bool
not true = false
not false = true

even-i : ℕ → Bool
even-i = It true not

-- tests:
-- even 3 = false
-- even 6 = true

-- Define a function sum that sums the numbers from 0 unil n-1
sum-r : ℕ → ℕ
sum-r = RR zero (_+_)

-- tests
-- sum 2 = 1
-- sum 3 = 3
-- sum 10 = 45

infix 50 _≤-i_
_≤-i_ : ℕ → ℕ → Bool
_≤-i_ n m = eq zero (It n pred' m)
  where
    pred' : ℕ → ℕ
    pred' (suc m) = m
    pred' zero = zero

-- Define a function max that calculates the maximum of 2 numbers
max-i : ℕ → ℕ → ℕ
max-i n m = if n ≤-i m then m else n

-- tests
-- max 2 3 = 3
-- max 10 1 = 10

-- Define a function fib which calculates the nth item of the
-- Fibonacci sequence: 1,1,2,3,5,8,13
-- (each number is the sum of the two previous ones).
fib-i : ℕ → ℕ
fib-i n = proj₂ (It (0 , 1) (λ (n , m) → (m , (n + m))) n)

-- tests
-- fib 0 = 1
-- fib 6 = 13

-- Define a function eq that determines wether two numbers
-- are equal.
eq-i : ℕ → ℕ → Bool
eq-i n m = n ≤-i m and m ≤-i n

-- tests
-- eq 4 3 = false
-- eq 6 6 = true

-- moddiv n m = (n % (suc m), n / (suc m))
remdiv-i : ℕ → ℕ → (ℕ × ℕ)
remdiv-i n q = It (0 , 0) iterate n
  where
    iterate : (ℕ × ℕ) → (ℕ × ℕ)
    iterate (r , d) =
      if eq r q
      then (0 , suc d)
      else (suc r , d)

-- Define a function rem such that rem m n returns the remainder
-- when dividing m by suc n (this way we avoid division by 0).
rem-i : ℕ → ℕ → ℕ
rem-i n m = proj₁ (remdiv-i n m)

-- tests
-- rem 5 1 = 1
-- rem 11 2 = 2

-- Define a function div such that div m n returns the result
-- of dividing m by suc n (ignoring the remainder)
div-i : ℕ → ℕ → ℕ
div-i n m = proj₂ (remdiv-i n m)

-- tests
-- div 5 1 = 2
-- div 11 2 = 3
