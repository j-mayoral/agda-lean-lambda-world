import Mathlib.Tactic

/-!
# Tactics for logic

The `by` keyword enters into tactic mode:

- sorry
- exact: To prove A it is enough to provide an a : A (a proof of A)
- assumption: To prove A it is enough to have an a : A (a proof of A) in your assumptions
- intro: To prove A → B it is enough that given an a : A (a proof of A), build a b: B (a proof of B)
- apply: To prove B assuming A → B it is enough to prove A

- constructor: to prove A ∧ B it is enough to prove A and B
- left: to prove A ∨ B it is enough to prove A
- right: to prove A ∨ B it is enough to prove B
- rcases
-/

variable (A B C : Prop)

-- sorry

example : A → ¬ A := sorry

theorem fermatLastTheorem: ¬ (∃ x y z n : Nat, (n > 2) → x ^ n + y ^ n = z ^ n) := sorry

-- exact
example (a : A) : A := sorry

example (a : A) (f : A → B) : B := sorry

-- assumption
example (a : A) : A := sorry

-- intro
example: A → A := sorry

example: A → (A → B) → B := sorry

-- apply
example (a : A) (f : A → B) : B := sorry

-- `→` is transitive.
-- tactic mode
example : (A → B) → (B → C) → (A → C) := sorry

example : (A → B → C) → (A → B) → (A → C) := sorry

example : A ∧ B → A := sorry

example : A ∧ B → B := sorry

example: A → A ∨ B := sorry

example: B → A ∨ B := sorry

-- ∧ is commutative
-- →
def commlr : A ∧ B → B ∧ A := sorry

def commrl : B ∧ A → A ∧ B := sorry

example : A ∧ B ↔ B ∧ A := sorry

-- Compact way
example : A ∧ B ↔ B ∧ A := sorry

-- ∨ is dist
--tactic
example: A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C := sorry

def elim_tactic: (A → C) → (B → C) → (A ∨ B) → C := sorry

-- ∧ is dist
example: A ∧ B ∧ C ↔ (A ∧ B) ∧ C := sorry

example: A → ¬ ¬ A := sorry

example : ¬ ¬ A → A := by sorry

example: (A → B) → (¬ B → ¬ A) := sorry

example: (¬ B → ¬ A) → (A → B):= sorry


example : (A ∨ ¬ A) := sorry
-- We need to construct some value of type A or ¬ A out of nowhere

/-In Classical logic, there is the notion of contradiction, it means that
if ¬ p → False then p is True. With this, the law of excluded middle is provable
-/

open Classical

--classic
example : (A ∨ ¬ A) := sorry

--classical
example: (¬ B → ¬ A) → (A → B):= sorry

/-
Double negation is also a Classical theorem that is not provable in
intuitionistic logic
¬ ¬ A ↔ A
-----
¬ ¬ A → A (not intuitionistic)
A → ¬ ¬ A (intuitionistic)
-/

example : ¬ ¬ A → A := sorry

example : A → ¬ ¬ A := sorry

/-
In fact, it is equivalent th law of excludded middle and double negation
-/

def dnLEM : ∀ p : Prop, ¬ ¬ (p ∨ ¬ p) := sorry

abbrev LEM := ∀ p : Prop, p ∨ ¬ p
abbrev DNE := ∀ p : Prop, ¬ ¬ p → p
example : LEM ↔ DNE := sorry

/-!
# Tactics for First Order Logic (and Natural Numbers)
- rfl: something is equal to itself x = x
- rw : you can always replace an x by an y if x = y
- simp: applies rules marked by @simp
- induction: Principle of induction
- repeat: repeat the application of a tactic over a resulting goal
-/

-- refl
example: 1 = 1 := sorry

example (x : Nat) : x = x := sorry

-- lean works with α, β, η, etc... conversions (reduce)
example: 3 = 1 + 2 := sorry

-- = is reflexive
example: (x = x) := sorry

-- rw
-- = is transitive
example: (x = y) → (y = z) → (x = z) := sorry

-- nth rw allows us to use rw in a concrete position
example: 2*x + 2 = 2 * (x + 1) := sorry

-- = is symmetric
example: (x = y) → (y = x) := sorry

-- if x = y, then, for any property p, if x satisfies p then y does.
lemma eq_congr (p : Nat → Prop): x = y → p x = p y := sorry


-- simp
example : (x = y + 1) → (y = z + 2) → (x = z + 3) := sorry

-- induction:
lemma zero_comm: 0 + x = x + 0 := sorry


lemma add_associative0 (x y z : Nat): x + y + z = x + (y + z) := sorry

-- recursion
lemma add_associative1 (x y z : Nat): x + y + z = x + (y + z) := sorry

-- induction
lemma add_commutative0 (x y : Nat) : x + y = y + x := sorry

-- recursion
lemma add_commutative1 (x y : Nat) : x + y = y + x := sorry

-- let's play

def sum_until: Nat → Nat := sorry

-- #eval sum_until 3 -- 3 + 2 + 1 = 6
-- #eval sum_until 4 -- 4 + 3 + 2 + 1 = 10
-- #eval sum_until 5 -- 5 + 4 + 3 + 2 + 1 = 15

theorem sum_first_natural_numbers: ∀ n : Nat, 2 * (sum_until n) = n * (n + 1) := sorry

-- ring tactic is awesome

theorem sum_first_natural_numbers_ring: ∀ n : Nat, 2 * (sum_until n) = n * (n + 1) := sorry

-- -------------------------------
example: (p q : Type → Prop) →
         (∀ x: Type, (p x) ∧ (q x)) →
         ((∀ x : Type, p x) ∧ (∀ x : Type, q x)) := sorry

example: ¬ ¬ (p ∨ ¬ p) := sorry

example: (p → q) → (¬ q → ¬ p) := sorry

example: ¬ ¬ ((¬ q → ¬ p) → (p → q)) := sorry

example: (¬ p ∨ q) → (p → q) := sorry

example: ¬ ¬ ((p → q) → (¬ p ∨ q)) := sorry

example : ∃ n : Nat, n + 1 = 1 := sorry

example : ∃ n : Nat, (n < 5 ∧ n > 3) := sorry

-- use Nat.mul_zero, Nat.mul_add
lemma times_zero: (n : Nat) → n * 0 = 0 * n := sorry

-- use times_zero Nat.add_mul Nat.mul_add
lemma times_one : (n : Nat) → n * 1 = 1 * n := sorry

-- use Nat.add_mul Nat.mul_add Nat.mul_one times_zero times_one
lemma times_comm : (n m : Nat) → (n * m = m * n) := sorry
