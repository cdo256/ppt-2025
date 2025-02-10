{- Exercise 01 Programs, Proofs and Types (COMP4074) -}

open import Data.Nat -- we are using ℕ for examples.
variable -- we use A B C as variables for Set = Types.
  A B C : Set

{-

1. Checking and reducing λ-terms (40/100)

We are using the following functions:
-}

add3 : ℕ → ℕ
add3 = λ x → x + 3

tw : (A → A) → A → A
tw = λ f n → f (f n)

{- Consider the term
tw tw add3 1

What is its type and what does it evaluate to?


First use agda to find the answers, using
C-c C-d (deduce type)
C-c C-n (normalize term)

However, to get the points you need to show (in a comment) how to
  normalize the term by doing an equational calculation, using only
 
- expansion of definitions
- β-reduction
- arithmetic calculations (e.g. 2 + 1 = 3)

See the lecture files for examples.
-}

{-
Claim1: tw tw add3 1 = 13
i.e. tw tw add3 1 is equivalent to 13 under the following equivalences:
  - alpha conversion
  - beta-equivalence
  - arithmetic in ℕ

Claim3: tw tw add3 1 : ℕ
i.e. the term (tw tw add3 1) has type ℕ

First we will prove the lemma below. This is done as a lemma. Since we are
proving equivalence and not normalizing terms, we don't need to worry about
order of evaluation, so we can use a lemma show that (tw add3) normalizes to a particular value, so we can apply it twice for lemma 2.

Lemma 1: tw add3 = λ x → x + 6
Proof:
  tw add3
 (definition of tw)
= (λ f n → f (f n)) add3
 (beta-reduction)
= (λ n → f (f n))[f := add3]
 (substitution)
= λ n → add3 (add3 n)
 (definition of add3)
= λ n → (λ x → x + 3) ((λ x → x + 3) n)
 (beta-reduction)
= λ n → (λ x → x + 3) ((λ x → x + 3)[x := n])
 (substitution)
= λ n → (λ x → x + 3) (n + 3)
 (beta-reduction)
= λ n → (λ x → x + 3)[x := (n + 3)]
 (substitution)
= λ n → (n + 3) + 3
 (associativity of + in ℕ)
= λ n → n + (3 + 3)
 (arithmetic (3 + 3 = 6))
= λ n → n + 6
 (alpha conversion n -> x)
= λ x → x + 6

Hence the result ∎

Now we can use this result in the following:

Lemma 2: tw tw add3 1 = 13
Proof:
  tw tw add3 1
 (application associates left)
= ((tw tw) add3) 1
 (definition of tw)
= (((λ f n → f (f n)) tw) add3) 1
 (beta-reduction)
= (((λ n → f (f n))[f := tw]) add3) 1
 (substitution)
= ((λ n → tw (tw n)) add3) 1
 (beta-reduction)
= ((tw (tw n))[n := add3]) 1
 (substitution)
= (tw (tw add3)) 1
 (definition of tw)
= ((λ f n → f (f n)) (tw add3)) 1
 (beta-reduction)
= ((λ n → f (f n))[f := (tw add3)]) 1
 (substitution)
= (λ n → (tw add3) ((tw add3) n)) 1
 (beta-reduction)
= ((tw add3) ((tw add3) n))[n := 1]
 (substitution)
= (tw add3) ((tw add3) 1)
 (apply Lemma 1 twice)
= (λ x → x + 6) ((λ x → x + 6) 1)
 (beta-reduction)
= (λ x → x + 6) ((x + 6)[x := 1])
 (substitution)
= (λ x → x + 6) (1 + 6)
 (arithmetic)
= (λ x → x + 6) 7
 (beta-reduction)
= (x + 6)[x := 7]
 (substitution)
= 7 + 6
 (arithmetic)
= 13

Hence the result ∎

Corollary 3: tw tw add3 1 : ℕ
Proof:
We have tw tw add3 1 = 13 and 13 : ℕ
Since the equivalences we used preserve type, we can conclude that tw tw add3 1 : ℕ ∎
-}

{-
2. Constructing functions (40/100)

Derive functions of the given type using only λ and application.
If you think there isn't such a function then comment it out.

You can type in your solution into the "shed", that is {..}.
and then ask agda to type check using C-C C-space.
Inside a shed you can use C-C C-, to see the surrent goal and assumptions (variables) you can use.
You can also type in a function and type C-c C-r to use the function and create new sheds for the arguments.
To type a lambda symbol use \Gl (λ).

Outside a shed C-c C-l (re)loads a file.
For more see the link to the agda manual on moodle.
-}

f1 : (A → B) → (A → A → B)
f1 = λ f a1 a2 → f a1

f2 : (A → A → B) → (A → B)
f2 = λ f a → f a a

f3 : A → ((A → B) → B)
f3 = λ a f → f a

-- f4 : ((A → B) → B) → A
-- f4 = {!!}
-- Not possible in general, because we need to produce an A, but we only have a
-- function that produces a B (which we can't construct an argument for anyway).
-- by way of counter-example, if f4 existed, then we could use it to construct
-- an instance of ⊥ as:
--   Let A = ⊥, B = ⊤.
--   Then the term (f4 (λ f → tt)) would be valid, but would have type ⊥. Which is a contradiction.
-- Therefore no such f4 can exist with this type.

f5 : (A → B) → ((A → C) → C) → ((B → C) → C)
f5 = λ f g h → g (λ x → h (f x))

{-
3. Combinatory Logic (20/100)

Derive a implementations of f1 - f5 using only S, K and show in a
comment how you have come up with your solution.
-}

K : A → B → A
K = λ a b → a

S : (A → B → C) → (A → B) → A → C
S = λ f g x → f x (g x)

I : A → A
I {A} = S K (K {B = A})

{- As an example I derive a combinator version of tw -}

{-
λ f n → f (f n)
= λ f → λ n → f (f n)
= λ f → S (λ n → f) (λ n → f n)
= λ f → S (K f) f
= S (λ f → S (K f) (λ f → f)
= S (S (λ f → S) (λ f → (K f)) I
= S (S (K S) K) I
-}

tw-c : (A → A) → A → A
tw-c = S (S (K S) K) I

{- Now you do the combinator versions of the functions you have defined in the previous section. 
   Again comment out lines which you think are impossible.
-}

{-
  λ f a1 a2 → f a1
 (expanding lambda variables)
= λ f → (λ a1 → (λ a2 → f a1))
 (definition of K)
I am joining some of these steps together for brevity:
= λ f → (λ a1 → K (f a1))
 (definition of K)
= λ f → (λ a1 → K (f a1))
 (eta conversion)
= λ f → (λ a1 → ((λ a1 → K) a1) (f a1))
 (definition of S)
= λ f → (S (λ a1 → K) f)
 (definition of K)
= λ f → (S (K K) f)
 (parentheses)
= λ f → ((S (K K)) f)
 (eta converison)
= S (K K)
-}

f1-c : (A → B) → (A → A → B)
f1-c = S (K K)

{-
  λ f a → f a a
 (expand lambda variables)
= λ f → (λ a → (f a) a)
 (defintion of I)
= λ f → (λ a → (f a) (I a))
 (defintion of S)
= λ f → S f I
 (definition of K)
= λ f → S f (K I f)
 (parentheses)
= λ f → (S f) (K I f)
 (definition of S)
= S S (K I)
-}

f2-c : (A → A → B) → (A → B)
f2-c = S S (K I)

{-
  λ a f → f a
 (expand lambda variables)
= λ a → λ f → f a
 (definition of I)
= λ a → λ f → (I f) a
 (definition of K)
= λ a → λ f → (I f) (K a f)
 (definition of S)
= λ a → (S I) (K a)
 (definition of K)
= λ a → (K (S I) a) (K a)
 (definition of K)
= S (K (S I)) K
-}

f3-c : A → ((A → B) → B)
f3-c = S (K (S I)) K

-- Not possible, see argument above for f4.
-- f4-c : ((A → B) → B) → A
-- f4-c = {!!}

{-
= λ f g h → g (λ x → h (f x))
 (expand lambda variables)
= λ f → λ g → λ h → g (λ x → h (f x))
 (definition of K)
= λ f → λ g → λ h → g (λ x → (K h x) (f x))
 (definition of S)
= λ f → λ g → λ h → g (S (K h) f)
 (definition of K)
= λ f → λ g → λ h → (K g h) (S (K h) f)
 (parenheses)
= λ f → λ g → λ h → (K g h) ((S (K h)) f)
 (beta-equivalence)
= λ f → λ g → λ h → (K g h) ((λ i → (S (K i)) f) h)
 (definition of S)
= λ f → λ g → S (K g) (λ i → (S (K i)) f)
 (beta-equivalence)
= λ f → λ g → S (K g) (λ i → ((λ j → S (K j)) i) f)
 (definition of K)
= λ f → λ g → S (K g) (λ i → ((λ j → S (K j)) i) (K f i))
 (definition of S)
= λ f → λ g → S (K g) (S (λ j → S (K j)) (K f))
 (definition of K)
= λ f → λ g → S (K g) (S (λ j → (K S j) (K j)) (K f))
 (definition of S)
= λ f → λ g → S (K g) (S (S (K S) K) (K f))
 (definition of K)
= λ f → λ g → S (K g) (K (S (S (K S) K) (K f)) g)
 (parentheses)
= λ f → λ g → (S (K g)) (K (S (S (K S) K) (K f)) g)
 (definition of S)
= λ f → λ g → ((K S g) (K g)) (K (S (S (K S) K) (K f)) g)
 (beta-equivalence)
= λ f → λ g → ((λ h → (K S h) (K h)) g) (K (S (S (K S) K) (K f)) g)
 (definition of S)
= λ f → S (λ h → (K S h) (K h)) (K (S (S (K S) K) (K f)))
 (definition of S)
= λ f → S (S (K S) K) (K (S (S (K S) K) (K f)))
 (definition of K)
= λ f → (K S f) (K (S (K S) K) f) (K (S (S (K S) K) (K f)))
 (definition of K)
= λ f → (K S f) (K (S (K S) K) f) (K (S (S (K S) K) (K f)))
 (beta-equivalence)
= λ f → (K S f) (K (S (K S) K) f) ((λ g → K (S (S (K S) K) (K g))) f)
 (parentheses)
= λ f → ((K S f) (K (S (K S) K) f)) ((λ g → K (S (S (K S) K) (K g))) f)
 (beta-equivalence)
= λ f → ((λ g → (K S g) (K (S (K S) K) g)) f) ((λ g → K (S (S (K S) K) (K g))) f)
 (definition of S)
= (λ g → S (K S g) (K (S (K S) K) g)) (λ g → K (S (S (K S) K) (K g)))
 (definition of S)
= S (S (K S) (K (S (K S) K))) (λ g → K (S (S (K S) K) (K g)))
 (definition of K)
= S (S (K S) (K (S (K S) K))) (λ g → (K K g) (S (S (K S) K) (K g)))
 (beta-equivalence)
= S (S (K S) (K (S (K S) K))) (λ g → (K K g) ((λ f → S (S (K S) K) (K f)) g))
 (definition of S)
= S (S (K S) (K (S (K S) K))) (S (K K) (λ f → S (S (K S) K) (K f)))
 (parentheses)
= S (S (K S) (K (S (K S) K))) (S (K K) (λ f → (S (S (K S) K)) (K f)))
 (definition of K)
= S (S (K S) (K (S (K S) K))) (S (K K) (λ f → (K (S (S (K S) K)) f) (K f)))
 (definition of K)
= S (S (K S) (K (S (K S) K))) (S (K K) (S (K (S (S (K S) K))) K))

And we're done.
-}


f5-c : (A → B) → ((A → C) → C) → ((B → C) → C)
f5-c = S (S (K S) (K (S (K S) K))) (S (K K) (S (K (S (S (K S) K))) K))
