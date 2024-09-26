import Mathlib.Order.Basic
import Mathlib.Tactic

variable
  {α β : Type} -- β for lemmas not requiring ordering
  [LE α]
  [decLe : (a b : α) → Decidable (a ≤ b)]

/- merge and split -/

-- merge of two ordered lists
def merge (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs, y :: ys =>
    match decLe x y  with
    | isTrue  _ => x :: merge xs (y :: ys)
    | isFalse _ => y :: merge (x :: xs) ys

#eval merge [1, 3, 5] [2, 4, 6] -- [1, 2, 3, 4, 5, 6]

-- split a list in halves - it disorders elements!
def splitList (xs : List α) : (List α × List α) :=
  match xs with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

#eval splitList [1, 2, 3, 4, 5, 6] -- ([1, 3, 5], [2, 4, 6])

/- split lemmas -/

-- four technical lemmas about the length of splitList halves

lemma splitHalves (xs : List β) (h : xs.length = 2*m) :
    (splitList xs).1.length = m ∧ (splitList xs).2.length = m := by
  cases m with
  | zero => match xs with
    | [] => trivial
  | succ n => match xs with
    | x :: y :: zs =>
      simp [List.length, mul_add] at h
      apply splitHalves zs at h
      simp [splitList, List.length]
      assumption

lemma splitPreservesTotalLength (xs : List β) :
    (splitList xs).1.length + (splitList xs).2.length = xs.length := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    simp_arith [splitList, ih]
    rw [add_comm]
    assumption

lemma splitListLE (xs : List β) :
    (splitList xs).1.length ≤ xs.length ∧
    (splitList xs).2.length ≤ xs.length := by
  induction xs with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
    case right => apply Nat.le_succ_of_le; assumption

theorem splitListLT (xs : List β) (_ : xs.length ≥ 2) :
    (splitList xs).1.length < xs.length ∧
    (splitList xs).2.length < xs.length := by
  match xs with
  | x :: y :: zs =>
    simp_arith [splitList]
    apply splitListLE

/- sort definition -/

-- definition of mergeSort, with termination
def mergeSort (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let a := (splitList xs).1
    let b := (splitList xs).2
    have h1 := Nat.ge_of_not_lt h
    have : a.length < xs.length := by exact (splitListLT xs h1).1
    have : b.length < xs.length := by exact (splitListLT xs h1).2
    merge (mergeSort a) (mergeSort b)
    termination_by xs.length

/- merge lemmas -/

lemma mergePreservesLength (xs : List α) (ys : List α):
    (merge xs ys).length = xs.length + ys.length := by
  match xs, ys with
  | [], _ => simp [merge]
  | x :: xs, [] => simp [merge]
  | x :: xs, y :: ys =>
    match h : decLe x y with
    | isTrue _ =>
      have h1 := mergePreservesLength xs (y :: ys)
      simp [List.length] at h1
      simp_arith [merge, h, h1]
    | isFalse _ =>
      have h1 := mergePreservesLength (x :: xs) ys
      simp [List.length] at h1
      simp_arith [merge, h, h1]

lemma mergeSortPreservesLength (xs : List α):
    (mergeSort xs).length = xs.length := by
  match Nat.decLt xs.length 2 with
    | isTrue p =>
      match xs with
      | [] => simp [mergeSort]
      | [x] => simp [mergeSort]
    | isFalse p =>
      have := splitListLT xs (Nat.ge_of_not_lt p)
      rw [mergeSort]
      simp [p, mergePreservesLength]
      rw [mergeSortPreservesLength (splitList xs).1]
      rw [mergeSortPreservesLength (splitList xs).2]
      exact splitPreservesTotalLength xs
  termination_by xs.length

/- complexity definition -/

def mergeTime (xs ys : List α) : Nat :=
  match xs, ys with
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if (x ≤ y)
    then 1 + mergeTime xs (y :: ys)
    else 1 + mergeTime (x :: xs) ys

def mergeSortTime (xs : List α) : Nat :=
  if h : xs.length < 2 then 0
  else
    let a := (splitList xs).1
    let b := (splitList xs).2
    have h1 := Nat.ge_of_not_lt h
    have : a.length < xs.length := by exact (splitListLT xs h1).1
    have : b.length < xs.length := by exact (splitListLT xs h1).2
    (mergeTime (mergeSort a) (mergeSort b))
    + (mergeSortTime a)
    + (mergeSortTime b)
  termination_by xs.length

#eval mergeSortTime [1, 2, 3, 4, 5, 6, 7, 8] -- 17

/- bound proof -/

lemma mergeBound (xs ys: List α) :
    mergeTime xs ys ≤ xs.length + ys.length := by
  match xs, ys with
    | [], _ => simp [mergeTime]
    | a :: as, [] => simp [mergeTime]
    | a :: as, b :: bs =>
      match decLe a b with
      | isTrue p =>
        have ih := mergeBound as (b :: bs)
        simp_arith [List.length] at ih
        simp_arith [p, mergeTime, ih]
      | isFalse p =>
        have ih := mergeBound (a :: as) bs
        simp_arith [List.length] at ih
        simp_arith [p, mergeTime, ih]

-- Our complexity bound: logarithmic time [n * log2(n)]
-- It is not strict: the strict bound for merge is `xs.length + ys.length - 1`
-- for a pair of non-empty lists,
-- and the strict bound for mergeSort is `(m - 1) * 2 ^ m + 1`,
-- but the calculations get more involved.
-- Surprisingly enough, the equality is reached in ordered lists,
-- due to the mixing of splitList.
theorem mergeSortBound (xs : List α) (m : Nat) (p : xs.length = 2 ^ m):
    mergeSortTime xs ≤ m * 2 ^ m := by
  cases m with
  | zero =>
    simp [p, mergeSortTime]
  | succ m =>
    simp_arith [Nat.pow_add] at p
    have hl : ¬ xs.length < 2 := by
      simp [p, Nat.pow_add]
    rw [mergeSortTime]
    simp [hl]

    let a := (splitList xs).1 ; have ha  : a  = (splitList xs).1 := rfl
    let b := (splitList xs).2 ; have hb  : b  = (splitList xs).2 := rfl
    let sa := mergeSort a     ; have hsa : sa = mergeSort a      := rfl
    let sb := mergeSort b     ; have hsb : sb = mergeSort b      := rfl

    rw [← ha,← hb,← hsa,← hsb]

    have h1 : a.length = 2 ^ m := by rw [(splitHalves xs p).1]
    have h2 : b.length = 2 ^ m := by rw [(splitHalves xs p).2]
    have h3 : sa.length = 2 ^ m := by simp [sa, h1, mergeSortPreservesLength]
    have h4 : sb.length = 2 ^ m := by simp [sb, h2, mergeSortPreservesLength]

    have i1 := mergeBound sa sb
    have i2 := mergeSortBound a m h1
    have i3 := mergeSortBound b m h2

    have hh := Nat.add_le_add i1 (Nat.add_le_add i2 i3)

    simp_arith [h3,h4] at hh
    simp_arith [Nat.pow_add]
    ring_nf at *
    assumption
