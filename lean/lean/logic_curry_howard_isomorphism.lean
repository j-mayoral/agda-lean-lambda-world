
variable (A B C : Prop)

/-!
# Curry Howard Correspondence

Propositional Logic         Lambda Calculus
-------------------         ---------------
Propositions                Types
Proposition P => Q          P → Q (functions)
Proof of P                  Well typed program with a term of type P
Proposition P is provable   Type P is inhabited

## Ingredients

### Notation

 Lean uses the following notation for logic connectives:
 - `→` ("implies" -- get it by typing `\r` or `→`)
 - `¬` ("not" -- type `\not` or `\n`)
 - `∧` ("and" -- type `\and` or `\an`)
 - `↔` ("if and only if" -- type `\iff` or `\lr`)
 - `∨` ("or" -- type `\or` or `\v`

### Propositions

The game
  - Propositions
  - Rules to create new ones (Conjunction, Disjunction, Negation, Implication)

#### Implication : functions in

Recall that Lean's convention is that `P → Q → R` means `P → (Q → R)` (that is,
implication is right-associative)
-/

-- `→` is transitive.
example : (A → B) → (B → C) → (A → C) := sorry

example : (A → B → C) → (A → B) → (A → C) := sorry


/-!
#### Conjunction: And in Lean (∧):

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-/

example : A ∧ B → A := sorry

-- ∧ is commutative
example : A ∧ B ↔ B ∧ A := sorry

-- ∧ is associative
example: A ∧ B ∧ C ↔ (A ∧ B) ∧ C := sorry

-- ∧ is distributive
-- →
def assocR(A B C : Prop): A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := sorry
-- ←
def assocL(A B C : Prop): (A ∧ B) ∨ (A ∧ C) → A ∧ (B ∨ C) := sorry

example: (A ∧ B) ∨ (A ∧ C) ↔ A ∧ (B ∨ C) := sorry

/-!
#### Disjunction: Or in Lean (∨) :

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

-- Or elimination
example : (A → C) → (B → C) → (A ∨ B) → C := sorry

-- ∨ is commutative
example : A ∨ B ↔ B ∨ A := sorry

-- ∨ is associative
example: A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C := sorry

/-!
#### Negation: Not in Lean (¬) :

def Not (a : Prop) : Prop := a → False
-/

example : False → A := False.elim

/-
Law of excluded middel (A ∨ ¬A)

This law is not provable using the basic definions of ∨, ∧, ¬, → because
the model of logic that arise from functional programming is intuitionist, that
means that if you want to proof something you need to provide a construction (an implementations)
of the corresponding type
-/
example : (A ∨ ¬ A) := sorry
-- We need to construct some value of type A or ¬ A out of nowhere

/-In Classical logic, there is the notion of contradicction, it means that
if ¬ p → False then p is True. With this, the law of excluded middle is provable
-/

open Classical

-- classical
example : (A ∨ ¬ A) := sorry

/-
Double negation is also a Classical theorem that is not provable in
intuitionistic logic
¬ ¬ A ↔ A
-----
¬ ¬ A → A (not intuitionistic)
A → ¬ ¬ A (intuitionistic)
-/

-- classical
example : ¬ ¬ A → A := sorry

example : A → ¬ ¬ A := sorry

/-
In fact, it is equivalent the law of excludded middle and double negation
-/

def dnLEM : ∀ p : Prop, ¬ ¬ (p ∨ ¬ p) := sorry

abbrev LEM := ∀ p : Prop, p ∨ ¬ p
abbrev DNE := ∀ p : Prop, ¬ ¬ p → p
example : LEM ↔ DNE := sorry

/-Moving to predicates

First Order Logic           Lambda Calculus
-------------------         ---------------
Predicates                  Dependent Types
∀ x ∈ S, P(s)               (x : S) → P (s) (dependent function application)
∃ x ∈ S, P(s)               (a, P(a)) (dependent pair)
proof of P(x)               well typed program with a term of type P(x)
Proposition P is provable   Type P(x) is inhabited
for value x
-/

example : ∀ x : Nat, x + 1 ≠ 0 := sorry

example : ∃ x : Nat, x + 1 = 1 := sorry

example : ∀ x : Nat, x = x := fun h => Eq.refl h

-- Principle of induction as a recursive function
def ind : (P : Nat → Prop) →
          (P 0)            →
          ((n: Nat) → P n → P (n + 1)) →
          -- --------------------------
          ∀ n : Nat , P n :=
  fun p p0 f n0 => match n0 with
  | 0 => p0
  | n00 + 1 =>
    let ih : p n00 := ind p p0 f n00
    f n00 ih

-- The hell of not using tactics
def plus_zero: ∀ x : Nat, x + 0 = 0 + x :=
  let p := fun z => z + 0 = 0 + z
  let p0:  p 0 := Eq.refl 0
  let f : ((n: Nat) → p n → p (n + 1)) :=
    fun x0 ih =>
    Eq.trans (
      Eq.trans (
        Eq.trans (
          Eq.trans (
            Eq.trans (Nat.succ_eq_add_one x0)
                     (Nat.add_zero x0.succ))
                     (congrArg Nat.succ (Eq.symm (Nat.add_zero x0))))
                     (congrArg Nat.succ ih))
                     (Nat.succ_eq_add_one (0 + x0)))
                     (Nat.add_assoc 0 x0 1)
  ind p p0 f

  -- The calc framework allows us to simplify the Eq.trans by some syntactic sugar.
  -- Even with this, the forward process is counter intuitive
  def plus_zero_calc: ∀ x : Nat, x + 0 = 0 + x :=
  let p := fun z => z + 0 = 0 + z
  let p0:  p 0 := Eq.refl 0
  let f : ((n: Nat) → p n → p (n + 1)) :=
    fun x0 ih =>
      calc
      x0 + 1 + 0 = x0.succ + 0 := Nat.succ_eq_add_one x0
      _= x0.succ := Nat.add_zero x0.succ
      _= (x0 + 0).succ := congrArg Nat.succ (Eq.symm (Nat.add_zero x0))
      _= (0 + x0).succ := congrArg Nat.succ ih
      _= (0 + x0) + 1 := Nat.succ_eq_add_one (0 + x0)
      _= 0 + (x0 + 1) := Nat.add_assoc 0 x0 1
  ind p p0 f

example: (p q : Type → Prop) →
           (∀ x: Type, (p x) ∧ (q x)) →
           ((∀ x : Type, p x) ∧ (∀ x : Type, q x)) := sorry

example: (p → q) → (¬ q → ¬ p) := sorry

example: ¬ ¬ ((¬ q → ¬ p) → (p → q)) := sorry

example: (¬ p ∨ q) → (p → q) := sorry

example: ¬ ¬ ((p → q) → (¬ p ∨ q)) := sorry
