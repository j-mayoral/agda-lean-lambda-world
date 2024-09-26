module agda.dependent_types where
open import Agda.Builtin.String using (String)

-- some help to parse infix operators
infix  4 _≤_
infix  4 _≡_
infixl 6 _+_
infixr 5 _∷_

-- -----

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

t0 : ℕ
t0 = zero

t1 : ℕ
t1 = suc zero

t2 : ℕ
t2 = suc (suc zero)

t3 : ℕ
t3 = suc (suc (suc zero))

-- -----

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

t5 : ℕ
t5 = t2 + t3
-- C-c C-n t5 ---> suc (suc (suc (suc (suc zero))))

-- -----
private
  variable
    A : Set
    B : Set
    n : ℕ

data Vec A : ℕ → Set where
  []  : Vec A zero
  _∷_ : (x : A) (xs : Vec A n) → Vec A (suc n)

v3 : Vec String t3
v3 = "a" ∷ "b" ∷ "c" ∷ []

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc  : (i : Fin n) → Fin (suc n)

f3i1 : Fin t3
f3i1 = suc zero     -- 1 in {0, 1, 2}

lookup : Vec A n → Fin n → A
lookup (a ∷ as) zero = a
lookup (a ∷ as) (suc i) = lookup as i

b : String
b = lookup v3 f3i1  -- "b"

-- -----

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

t2≤3 : t2 ≤ t3
t2≤3 = s≤s (s≤s z≤n)

t3≤5 : t3 ≤ t5
t3≤5 = s≤s (s≤s (s≤s z≤n))

t2+3=5 : t2 + t3 ≡ t5
t2+3=5 = refl

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

t2≤5 : t2 ≤ t5
t2≤5 = ≤-trans t2≤3 t3≤5