module agda.arithmetic_propositions where
open import agda.dependent_types

infixl 6  _∸_
infixl 7  _*_

private
  variable
    A : Set

-- -----

+-0 : (m : ℕ) → m + zero ≡ m
+-0 = ?

-- -----

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc = ?

-- -----

+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc = ?

-- -----

-- cong : (f : A → B) {x y} → x ≡ y → f x ≡ f y
-- cong f refl = refl

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- begin ... ≡⟨⟩ ... ≡⟨⟩ ... ≡⟨ xxx ⟩ ... ≡⟨⟩ ... ∎

infix  3 _∎
infixr 2 _≡⟨⟩_ step-≡
infix  1 begin_

begin_ : {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

step-≡ : (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ x y≡z x≡y = trans x≡y y≡z

_∎ : (x : A) → x ≡ x
x ∎ = refl

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

-- -----

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm = ?

-- -----

+-right-comm : (m n p : ℕ) → m + n + p ≡ m + p + n
+-right-comm = ?

-- -----

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

data _∈_ {A : Set} : A → List A → Set where
  here  : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  there : {x y : A} {xs : List A} → y ∈ xs → y ∈ (x ∷ xs)

in1 : "a" ∈ ("a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ [])
in1 = here

in2 : "d" ∈ ("a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ [])
in2 = there (there (there (here)))

data Either (A B : Set) : Set where
  i1 : A → Either A B
  i2 : B → Either A B

ei-++ : {a : A} {xs ys : List A} → Either (a ∈ xs) (a ∈ ys) → a ∈ (xs ++ ys)
ei-++ = ?

++-ei : {a : A} {xs ys : List A} → a ∈ (xs ++ ys) → Either (a ∈ xs) (a ∈ ys)
++-ei = ?

-- -----

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- -----

*-1 : (m : ℕ) → (suc zero) * m ≡ m
*-1 = ?

-- -----

*-0 : (m : ℕ) → m * zero ≡ zero
*-0 = ?

-- -----

*-suc : (m n : ℕ) → m * (suc n) ≡ m * n + m
*-suc = ?

-- -----

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm = ?