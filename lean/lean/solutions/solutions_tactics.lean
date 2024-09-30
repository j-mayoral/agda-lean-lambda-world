import Mathlib.Tactic

/-!
# Tactics for logic

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

example : A → ¬ A := by sorry

theorem fermatLastTheorem: ¬ (∃ x y z n : Nat, (n > 2) → x ^ n + y ^ n = z ^ n) := sorry

-- exact
example (a : A) : A := by
  exact a

example (a : A) (f : A → B) : B := by
  exact f a

-- assumption
example (a : A) : A := by
  assumption

-- intro
example: A → A := by
  intro a
  assumption

example: A → (A → B) → B :=  by
  intro a f
  exact f a

-- apply
example (a : A) (f : A → B) : B := by
  apply f
  assumption

-- `→` is transitive.
-- tactic mode
example : (A → B) → (B → C) → (A → C) := by
  intro h h1 h2
  apply h1
  apply h
  assumption

example : (A → B → C) → (A → B) → (A → C) := by
  intro h h1 h2
  apply h
  . assumption
  . apply h1
    assumption

example : A ∧ B → A := by
intro hab
exact hab.left

example : A ∧ B → B := by
intro hab
exact hab.right

example: A → A ∨ B := by
intro ha
left
assumption

example: B → A ∨ B := by
intro ha
right
assumption

-- ∧ is commutative
-- →
def commlr : A ∧ B → B ∧ A := by
  intro hab
  rcases hab with ⟨ha, hb⟩
  . constructor
    . assumption
    . assumption

def commrl : B ∧ A → A ∧ B := by
  intro hab
  rcases hab with ⟨hb, ha⟩
  . constructor
    . assumption
    . assumption

example : A ∧ B ↔ B ∧ A := by
  apply Iff.intro
  . intro hab
    apply commlr
    assumption
  . intro hab
    apply commrl
    assumption

-- Compact way
example : A ∧ B ↔ B ∧ A := by
  apply Iff.intro <;>
  . intro h
    rcases h with ⟨ha, hb⟩
    . constructor <;> assumption

-- ∨ is dist
--tactic
example: A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C := by
  apply Iff.intro
  . intro h
    rcases h with (ha | (hb | hc))
    . left
      left
      assumption
    . left
      right
      assumption
    . right
      assumption
  . intro h
    rcases h with ((ha | hb) | hc)
    . left
      assumption
    . right
      left
      assumption
    . right
      right
      assumption

def elim_tactic: (A → C) → (B → C) → (A ∨ B) → C :=
by
  intro h1 h2 h3
  rcases h3 with (ha | hb)
  . apply h1
    assumption
  . apply h2
    assumption

-- ∧ is dist
example: A ∧ B ∧ C ↔ (A ∧ B) ∧ C := by
  apply Iff.intro
  . intro h
    rcases h with  ⟨ha, ⟨hb, hc⟩⟩
    . constructor
      . constructor
        . assumption
        . assumption
      . assumption
  . intro h
    rcases h with ⟨⟨ha, hb⟩, hc⟩
    . constructor
      . assumption
      . constructor
        . assumption
        . assumption

example: A → ¬ ¬ A := by
  intro ha
  intro hn
  apply hn
  assumption

example : ¬ ¬ A → A := by sorry

example: (A → B) → (¬ B → ¬ A) := by
intro h h1 h2
apply h1
apply h
assumption

example: (¬ B → ¬ A) → (A → B):= sorry


example : (A ∨ ¬ A) := sorry
-- We need to construct some value of type A or ¬ A out of nowhere

/-In Classical logic, there is the notion of contradiction, it means that
if ¬ p → False then p is True. With this, the law of excluded middle is provable
-/

open Classical
example : (A ∨ ¬ A) := by
  apply byContradiction -- This is classical
  intro h
  have h1 : ¬ A := by
    intro h3
    apply h (Or.inl h3)
  apply h
  apply Or.inr
  assumption

example: (¬ B → ¬ A) → (A → B):= by
intro h h1
apply byContradiction -- this is classical
intro h2
apply h h2
assumption

/-
Double negation is also a Classical theorem that is not provable in
intuitionistic logic
¬ ¬ A ↔ A
-----
¬ ¬ A → A (not intuitionistic)
A → ¬ ¬ A (intuitionistic)
-/

example : ¬ ¬ A → A := by
  intro h
  rw [Not] at h -- at this point we get the byContradiction axiom
  apply byContradiction
  assumption

example : A → ¬ ¬ A :=
  fun (h : A) =>
    fun (h2 : A → False) => h2 h

/-
In fact, it is equivalent th law of excludded middle and double negation
-/

def dnLEM : ¬ ¬ (P ∨ ¬ P) := by
  intro h
  apply h
  right
  intro h2
  apply h
  left
  assumption

abbrev LEM := ∀ P : Prop, P ∨ ¬ P
abbrev DNE := ∀ P : Prop, ¬ ¬ P → P
example : LEM ↔ DNE := by
  apply Iff.intro
  . rw [LEM, DNE]
    intro h2 h3 h4
    have h5 : h3 ∨ ¬ h3 := h2 h3
    rcases h5 with (h6 | nh6)
    . assumption
    . apply False.elim
      apply h4 nh6
  . rw [LEM, DNE]
    intro h h2
    apply h
    apply dnLEM


/-!
# Tactics for First Order Logic (and Natural Numbers)
- rfl: something is equal to itself x = x
- rw : you can always replace an x by an y if x = y
- simp: applies rules marked by @simp
- induction: Principle of induction
- repeat: repeat the application of a tactic over a resulting goal
-/

-- refl
example: 1 = 1 :=
by
  rfl

example (x : Nat) : x = x :=
by
  rfl
example: 3 = 1 + 2 :=
by
  rfl -- lean works with α, β, η, etc... conversions

-- = is reflexive
example: (x = x) := by
  rfl

-- rw
-- = is transitive
example: (x = y) → (y = z) → (x = z) := by
  intro h1 h2
  rw [h2] at h1
  assumption

-- nth rw allows us to use rw in a concrete position
example: 2*x + 2 = 2 * (x + 1) := by
  --rw [← Nat.mul_one 2]
  nth_rw 2 [← Nat.mul_one 2]
  rw [← Nat.mul_add 2 x 1]

-- = is symmetric
example: (x = y) → (y = x) := by
  intro h1
  rw [← h1]

-- = is a Functor XD
lemma eq_congr (p : Nat → Prop): x = y → p x = p y :=
by
  intro p1
  rw [p1]


-- simp
example : (x = y + 1) → (y = z + 2) → (x = z + 3) := by
  intro h1
  intro h2
  simp [h1]
  assumption

-- induction:
lemma zero_comm: 0 + x = x + 0 := by
  induction x with
  | zero => rfl
  | succ x ih => rw [Nat.add_succ, ih]


lemma add_associative0 (x y z : Nat): x + y + z = x + (y + z) := by
  induction z with
  | zero => rw [Nat.add_zero, Nat.add_zero y]
  | succ z0 ih =>
    repeat rw [Nat.add_succ, ih]
    repeat rw [Nat.add_succ]

-- recursion
lemma add_associative1 (x y z : Nat): x + y + z = x + (y + z) := by
  match x, y, z with
  | x, y , 0  => rw [Nat.add_zero, Nat.add_zero]
  | x, y, Nat.succ z0 =>
    rw [Nat.add_succ, add_associative1 x y z0]
    repeat rw [Nat.add_succ]

-- induction
lemma add_commutative0 (x y : Nat) : x + y = y + x := by
  induction y with
  | zero => rw [zero_comm]
  | succ y0 ih =>
    repeat rw [Nat.add_succ, Nat.add_zero, ih, Nat.succ_add]

-- recursion
lemma add_commutative1 (x y : Nat) : x + y = y + x := by
  match y with
  | 0 => rw [zero_comm]
  | y0 + 1 =>
    repeat rw [Nat.add_succ, add_commutative1 x y0, Nat.succ_add]

-- let's play

def sum_until: Nat → Nat
| 0 => 0
| n + 1 => Nat.succ n + sum_until n

#eval sum_until 3 -- 3 + 2 + 1 = 6
#eval sum_until 4 -- 4 + 3 + 2 + 1 = 10
#eval sum_until 5 -- 5 + 4 + 3 + 2 + 1 = 15

theorem sum_first_natural_numbers: ∀ n : Nat, 2 * (sum_until n) = n * (n + 1) :=
  by
    intro n
    induction n with
      | zero => simp [sum_until]
      | succ n ih =>
       simp [sum_until]
       simp [Nat.mul_add]
       simp [ih]
       simp [Nat.mul_comm (n + 1)]
       simp [Nat.add_assoc (n * (n + 1))]
       simp [← Nat.mul_two (n + 1)]
       simp [Nat.add_comm (n * (n + 1))]
       nth_rw 2 [← Nat.mul_one 2]
       simp [Nat.add_mul]
       simp [Nat.mul_comm]

-- ring tactic is awesome

theorem sum_first_natural_numbers_ring: ∀ n : Nat, 2 * (sum_until n) = n * (n + 1) :=
  by
    intro n
    induction n with
      | zero => simp [sum_until]
      | succ n ih =>
       simp [sum_until, Nat.mul_add, ih]
       ring


example : ∃ n : Nat, n + 1 = 1 := by use 0

example : ∃ n : Nat, (n < 5 ∧ n > 3) := by exists 4


-- use Nat.mul_zero, Nat.mul_add
lemma times_zero: (n : Nat) → n * 0 = 0 * n := by
  intro n
  induction n with
    | zero => rfl
    | succ n0 ih =>
      rw [Nat.mul_zero]
      rw [Nat.mul_add]
      rw [← ih]
      rw [Nat.mul_zero]

-- use times_zero Nat.add_mul Nat.mul_add
lemma times_one : (n : Nat) → n * 1 = 1 * n := by
  intro n
  induction n with
    | zero => exact times_zero 1
    | succ n0 ih => rw [Nat.add_mul, Nat.mul_add, ih]

-- use Nat.add_mul Nat.mul_add Nat.mul_one times_zero times_one
lemma times_comm : (n m : Nat) → (n * m = m * n) := by
  intro m n
  induction n with
    | zero => exact times_zero m
    | succ n0 ih =>
      rw [Nat.mul_add]
      rw [ih]
      rw [Nat.add_mul]
      rw [Nat.mul_one]
      rw [Nat.one_mul]

example: (p q : Type → Prop) →
         (∀ x: Type, (p x) ∧ (q x)) →
         ((∀ x : Type, p x) ∧ (∀ x : Type, q x)) := by
  intro p q fand
  constructor
  . intro x
    exact (fand x).left
  . intro x
    exact (fand x).right

example: ¬ ¬ (p ∨ ¬ p) := by
  intro  nh
  have np : ¬p := by
    intro p0
    apply nh
    left
    assumption
  apply nh
  right
  assumption


example: (p → q) → (¬ q → ¬ p) := by
  intro f nq p0
  apply nq
  apply f
  assumption

example: ¬ ¬ ((¬ q → ¬ p) → (p → q)) := by
  intro f
  apply f
  intro f0
  intro p0
  have s0 : ¬q := by
    intro q0
    apply f
    exact fun _ _ => q0
  exact False.elim ((f0 s0) p0)

example: (¬ p ∨ q) → (p → q) := by
  intro h0
  intro p0
  rcases h0 with (h1 | nh1)
  . apply False.elim
    exact h1 p0
  . assumption

example: ¬ ¬ ((p → q) → (¬ p ∨ q)) := by
  intro f
  have h0 : (¬ p ∨ q) := by
    left
    intro p0
    have h01 : (p → q) → (¬ p ∨ q) := by
      intro pq
      right
      apply pq
      assumption
    exact f h01
  exact f (fun _ => h0)
