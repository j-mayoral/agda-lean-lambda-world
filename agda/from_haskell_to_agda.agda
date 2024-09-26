module agda.from_haskell_to_agda where
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

-- natural numbers
n : ℕ
n = 3

-- arithmetic
n1 = 1 + 2 + 3 + 4 -- 10
n2 = 1 * 2 * 3 * 4 -- 24

-- lists
l : List ℕ
l = 3 ∷ 2 ∷ 1 ∷ []

-- functions
f1 : ℕ → ℕ
f1 n = n + 5

-- lambdas
-- f2 : ℕ → ℕ
f2 = λ n → n + 5  -- type of f2 is inferred from the lambda definition

-- pattern matching
greaterThan2 : ℕ → Bool
greaterThan2 0 = false
greaterThan2 1 = false
greaterThan2 2 = false
greaterThan2 _ = true

sum : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

-- structures

record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B

-- this record already defines
-- Pair.fst : {A B : Set} → Pair A B → A
-- Pair.snd : {A B : Set} → Pair A B → B

p23 : Pair ℕ Bool
p23 = record { fst = 2; snd = true }

p2 = Pair.fst p23

-- inductive data types
data Either (A : Set) (B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

e1 : Either ℕ Bool
e1 = left 2

e2 : Either ℕ Bool
e2 = right true

-- Agda is a total functional programming language: every program must halt
-- without errors, loops or unhandled cases. The following `loop` function is
-- thus forbidden; it may be unsafely allowed with the pragma
-- {-# OPTIONS --no-termination-check #-}

-- loop : {A : Set} → A
-- loop = loop 

-- Agda has to be able to check correctness from a definition, in particular
-- the termination of recursive functions. It has some strategies to 
-- automatically deduce the termination of simple functions.

fact : ℕ → ℕ
fact zero = 1
fact (suc n) = (n + 1) * fact n

-- Agda is not able to check termination for the Ackermann function, whereas
-- Lean is able to.
-- ack : ℕ → ℕ → ℕ
-- ack 0 n = n + 1
-- ack (suc m) 0 = ack m 1
-- ack (suc m) (suc n) = ack m (ack (m + 1) n)

-- -----

-- Useful commands:

-- load
-- c-C + c-L ---> *All Done*

-- evaluation
-- c-C + c-N ---> f1 7 ---> 12

-- infer type
-- c-C + c-D ---> f1 ---> ℕ → ℕ

-- compile
-- c-X + c-C ---> The module was successfully compiled with backend GHCNoMain.
