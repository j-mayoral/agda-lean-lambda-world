module agda.solutions.solutions_arithmetic_propositions where
open import agda.dependent_types

infixl 7  _*_

private
  variable
    A : Set

-- -----

+-0 : (m : ℕ) → m + zero ≡ m

-- (zero + zero) ≡ zero
+-0 zero = refl

-- ((suc m) + zero) ≡ suc m
-- (suc (m + zero)) ≡ suc m
+-0 (suc m) = cong suc (+-0 m)

-- -----

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)

-- zero + suc n ≡ suc (zero + n)
--        suc n ≡ suc n
+-suc zero n = refl

-- suc m + suc n ≡ suc (suc m + n)
-- suc (m + suc n) ≡ suc (suc (m + n))
+-suc (suc m) n = cong suc (+-suc m n)

-- -----

+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

-- (zero + n) + p ≡ zero + (n + p)
--          n + p ≡ n + p
+-assoc zero n p = refl 

-- ((suc m) + n) + p ≡ (suc m) + (n + p)
-- (suc (m + n)) + p ≡ suc (m + (n + p))
-- suc ((m + n) + p) ≡ suc (m + (n + p))
+-assoc (suc m) n p = cong suc (+-assoc m n p)

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

+-comm zero n = -- refl
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-0 n) ⟩
    n + zero
  ∎

+-comm (suc m) n = 
  begin
    (suc m) + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + (suc m)
  ∎

-- -----

+-right-comm : (m n p : ℕ) → m + n + p ≡ m + p + n

+-right-comm m n p =
  begin
    (m + n) + p
  ≡⟨ +-assoc m n p ⟩
    m + (n + p)
  ≡⟨ cong (λ { x → m + x }) (+-comm n p) ⟩
    m + (p + n)
  ≡⟨ sym (+-assoc m p n) ⟩
    m + p + n
  ∎

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

ei-++               (i1 here)                 = here
ei-++               (i1 (there a-in-tail-xs)) = there (ei-++ (i1 a-in-tail-xs))
ei-++ {xs = []}     (i2 a-in-ys)              = a-in-ys
ei-++ {xs = x ∷ xs} (i2 a-in-ys)              = there (ei-++ (i2 a-in-ys))

++-ei : {a : A} {xs ys : List A} → a ∈ (xs ++ ys) → Either (a ∈ xs) (a ∈ ys)

++-ei {xs = []}     a-in-ys           = i2 a-in-ys
++-ei {xs = x ∷ xs} here              = i1 here
++-ei {xs = x ∷ xs} (there a-in-tail-xs-or-ys) with (++-ei a-in-tail-xs-or-ys)
...               |  i1 a-in-tail-xs  = i1 (there a-in-tail-xs)
...               |  i2 a-in-ys       = i2 a-in-ys

-- -----

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- -----

*-1 : (m : ℕ) → (suc zero) * m ≡ m
*-1 m = 
  begin
    (suc zero) * m
  ≡⟨⟩
    m + zero * m
  ≡⟨⟩
    m + zero
  ≡⟨ +-0 m ⟩
    m
  ∎

-- -----

*-0 : (m : ℕ) → m * zero ≡ zero
*-0 zero = refl
*-0 (suc m) = 
  begin
    (suc m) * zero
  ≡⟨⟩
    zero + m * zero
  ≡⟨⟩
    m * zero
  ≡⟨ *-0 m ⟩
    zero
  ∎

-- -----

-- The following two functions require an extensive use of `cong`, 
-- which indicates the need for a rewrite operation.
-- Adga has such `rewrite` system, but anyway, it is much more easy in Lean ;-)

*-suc : (m n : ℕ) → m * (suc n) ≡ m * n + m

*-suc zero _ = refl

*-suc (suc m) n = 
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + m * (suc n)
  ≡⟨ +-comm (suc n) (m * (suc n))⟩
    m * (suc n) + (suc n)
  ≡⟨ +-suc (m * (suc n)) n ⟩
    suc (m * (suc n) + n)
  ≡⟨ cong suc (cong (λ { x → x + n }) (*-suc m n)) ⟩
    suc (m * n + m + n)
  ≡⟨ cong suc (+-right-comm (m * n) m n) ⟩
    suc (m * n + n + m)  
  ≡⟨ sym (+-suc (m * n + n) m) ⟩
    m * n + n + suc m  
  ≡⟨ cong (λ { x → x + suc m }) (+-comm (m * n) n) ⟩
    n + m * n + suc m  
  ≡⟨⟩
    (suc m) * n + suc m  
  ∎

-- -----

*-comm : (m n : ℕ) → m * n ≡ n * m

*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-0 n) ⟩
    n * zero
  ∎

*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + m * n
  ≡⟨ +-comm n (m * n) ⟩
    m * n + n
  ≡⟨ cong (λ { x → x + n }) (*-comm m n) ⟩
    n * m + n
  ≡⟨ sym (*-suc n m) ⟩
    n * (suc m)
  ∎