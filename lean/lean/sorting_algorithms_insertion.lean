import Mathlib.Order.Basic
import Mathlib.Tactic

variable
  [LE α]
  [decLe : (a b : α) → Decidable (a ≤ b)]

/- sort definition -/

def insertInList (x : α) (xs : List α): List α :=
  match xs with
  | [] => [x]
  | y :: ys => if (x ≤ y) then x :: y :: ys else y :: insertInList x ys

#eval insertInList 2 [1, 4, 3] -- [1, 2, 4, 3]

def insertionSort (xs : List α) : List α :=
  match xs with
  | [] => []
  | y :: ys => insertInList y (insertionSort ys)

#eval insertionSort [2, 3, 4, 1] -- [1, 2, 3, 4]

-- BONUS: define functions
-- `isPermutation (xs : List α) (ys : List α): Bool`
-- `isOrdered (xs : List α): Bool`
-- and prove formally that `insertionSort` is a proper sorting algorithm.

/- complexity definition -/

def insertInListTime (x : α) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => if (x ≤ y) then 1 else 1 + insertInListTime x ys

def insertionSortTime (xs : List α): Nat :=
match xs with
  | [] => 0
  | y :: ys => insertInListTime y (insertionSort ys) + insertionSortTime ys

#eval insertionSortTime [1, 2, 3, 4, 5] --  4 = check consecutives
#eval insertionSortTime [5, 4, 3, 2, 1] -- 10 = compare every pair

/- bound proof -/

-- inserting an element makes the increases length by 1
lemma insertLength1 (x : α) (xs : List α) :
    (insertInList x xs).length = xs.length + 1 := by
  induction xs with
  | nil => trivial
  | cons y ys ih =>
    cases decLe x y with
    | isTrue h => simp [insertInList, h]
    | isFalse h => simp [insertInList, h, ih]

-- sorting preserves length
lemma insertionSortLength (xs : List α) :
    (insertionSort xs).length = xs.length := by
  induction xs with
  | nil => trivial
  | cons x xs ih => simp [insertionSort, insertLength1, ih]

-- inserting in a list of n elements takes no more than n comparisons
lemma insertInListBound (x : α) (xs : List α) :
    insertInListTime x xs ≤ (xs.length) := by
  induction xs with
  | nil => trivial
  | cons y ys ih =>
    cases decLe x y with
    | isTrue h =>
      simp [insertInListTime, h]
    | isFalse h =>
      simp [insertInListTime, h, Nat.add_comm, ih]

-- Our complexity bound: quadratic time [n * (n-1) / 2]
-- BONUS: prove that this bound is strict, i.e. for each n,
-- some list of length n reaches an equality.
theorem insertionSortBound (xs : List α) :
    2 * insertionSortTime xs + xs.length ≤ xs.length * xs.length := by
  induction xs with
  | nil => trivial
  | cons y ys ih =>
    rw [insertionSortTime]
    rw [List.length]
    have h1 := Nat.add_le_add
      (Nat.mul_le_mul_left 2 (insertInListBound y (insertionSort ys)))
      ih
    rw [insertionSortLength] at h1
    have h2 := Nat.add_le_add (Nat.le_refl 1) h1
    ring_nf at h2
    ring_nf
    assumption
