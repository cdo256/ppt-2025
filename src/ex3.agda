{- Exercise 3 Proofs,Programs and Types (PPT) -}

open import lib10

{- Part 1 : Recursion via patterns

Define the following functions using pattern matching and structural
recursion on the natural numbers.  -}

-- Define a function even that determines wether its input is even.
even :  ℕ → Bool
even = {!!}

-- tests:
-- even 3 = false
-- even 6 = true

-- Define a function sum that sums the numbers from 0 unil n-1
sum : ℕ → ℕ
sum = {!!}

-- tests
-- sum 2 = 1
-- sum 10 = 45

-- Define a function max that calculates the maximum of 2 numbers
max : ℕ → ℕ → ℕ
max = {!!}

-- tests
-- max 2 3 = 3
-- max 10 1 = 10

-- Define a function fib which calculates the nth item of the
-- Fibonacci sequence: 1,1,2,3,5,8,13
-- (each number is the sum of the two previous ones).
fib : ℕ → ℕ
fib = {!!}

-- tests
-- fib 0 = 1
-- fib 6 = 13

-- Define a function eq that determines wether two numbers
-- are equal.
eq : ℕ → ℕ → Bool
eq = {!!}

-- tests
-- eq 4 3 = false
-- eq 6 6 = true

-- Define a function rem such that rem m n returns the remainder
-- when dividing m by suc n (this way we avoid division by 0).
rem : ℕ → ℕ → ℕ 
rem = {!!}

-- tests
-- rem 5 1 = 1
-- rem 11 2 = 2

-- Define a function div such that div m n returns the result
-- of dividing m by suc n (ignoring the remainder)
div : ℕ → ℕ → ℕ
div = {!!}
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
