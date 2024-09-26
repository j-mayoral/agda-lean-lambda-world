
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
example : (A → B) → (B → C) → (A → C) :=
  fun f1 => fun f2 => fun a => f2 (f1 a)

example : (A → B → C) → (A → B) → (A → C) :=
  fun f1 => fun f2 => fun p =>
    let h := f1 p;
    let h2 := f2 p;
    h h2


/-!
#### Conjunction: And in Lean (∧):

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-/

example : A ∧ B → A := fun (h : A ∧ B) => h.left

-- ∧ is commutative
example : A ∧ B ↔ B ∧ A :=
  Iff.intro
    (fun (h : A ∧ B) => And.intro h.right h.left)
    (fun (h : B ∧ A) => And.intro h.right h.left)

-- ∧ is associative
example: A ∧ B ∧ C ↔ (A ∧ B) ∧ C :=
  Iff.intro
  (fun h: A ∧ B ∧ C => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
  (fun h: (A ∧ B) ∧ C => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)

-- ∧ is distributive
-- →
def assocR(A B C : Prop): A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
  fun (h1 : A ∧ (B ∨ C)) =>
    match h1.right with
    | Or.inl h2 => Or.inl (And.intro h1.left h2)
    | Or.inr h2 => Or.inr (And.intro h1.left h2)

-- ←
def assocL(A B C : Prop): (A ∧ B) ∨ (A ∧ C) → A ∧ (B ∨ C) :=
  fun (h1 : (A ∧ B) ∨ (A ∧ C)) =>
    match h1 with
    | Or.inl h2 => And.intro h2.left (Or.inl h2.right)
    | Or.inr h2 => And.intro h2.left (Or.inr h2.right)

example: (A ∧ B) ∨ (A ∧ C) ↔ A ∧ (B ∨ C) :=
  Iff.intro (assocL A B C) (assocR A B C)

/-!
#### Disjunction: Or in Lean (∨) :

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

example : (A → C) → (B → C) → (A ∨ B) → C :=
  fun (h1 : A → C) =>
  fun (h2 : B → C) =>
  fun (h3 : A ∨ B) =>
    match h3 with
    | Or.inl a => h1 a
    | Or.inr b => h2 b

-- ∨ is commutative
example : A ∨ B ↔ B ∨ A :=
  Iff.intro
    (fun h : A ∨ B  =>
      match h with
      | Or.inl a => Or.inr a
      | Or.inr b => Or.inl b)
    (fun h : B ∨ A  =>
      match h with
      | Or.inl a => Or.inr a
      | Or.inr b => Or.inl b)

-- ∨ is associative
example: A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C :=
  Iff.intro
    (fun h : A ∨ (B ∨ C) =>
      match h with
      | Or.inl a => Or.inl (Or.inl a)
      | Or.inr bc =>
        match bc with
        | Or.inl b => Or.inl (Or.inr b)
        | Or.inr c => Or.inr c)
    (fun h : (A ∨ B) ∨ C =>
      match h with
      | Or.inl ab =>
        match ab with
        | Or.inl a => Or.inl a
        | Or.inr b => Or.inr (Or.inl b)
      | Or.inr c => Or.inr (Or.inr c))

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

example : (A ∨ ¬ A) :=
  have h : ¬ (A ∨ ¬A) → False :=
    fun (h1 : A ∨ ¬A → False) =>
      have h2 : ¬ A :=
        fun (h3 : A) => h1 (Or.inl h3)
      h1 (Or.inr h2)
  byContradiction h --this is classical

/-
Double negation is also a Classical theorem that is not provable in
intuitionistic logic
¬ ¬ A ↔ A
-----
¬ ¬ A → A (not intuitionistic)
A → ¬ ¬ A (intuitionistic)
-/

example : ¬ ¬ A → A :=
  fun (h : ¬ ¬ A) => byContradiction h -- classic

example : A → ¬ ¬ A :=
  fun (h : A) =>
    fun (h2 : A → False) => h2 h

/-
In fact, it is equivalent th law of excludded middle and double negation
-/
def dnLEM: ∀ p : Prop, ¬ ¬ (p ∨ ¬ p) :=
    fun p n1 =>
      let l1 : ¬ p := fun n2 => n1 (Or.inl n2)
      n1 (Or.inr l1)

abbrev LEM := ∀ p : Prop, p ∨ ¬ p
abbrev DNE := ∀ p : Prop, ¬ ¬ p → p
example : LEM ↔ DNE :=
  Iff.intro
  (fun h p hp =>
    let lemp : p ∨ ¬ p := h p
    match lemp with
    | Or.inl il => il
    | Or.inr ir =>
      False.elim (hp ir))
  (fun h p =>
    h (p ∨ ¬ p) (dnLEM p))

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

example : ∃ x : Nat, x + 1 = 1 :=
  let x := 0;
  let p : x + 1 = 1 := Eq.refl 1 -- we will see in tactic mode how this works
  Exists.intro x p

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
         ((∀ x : Type, p x) ∧ (∀ x : Type, q x)) :=
  fun _ _ s => And.intro (fun x0 => (s x0).left) (fun x0 => (s x0).right)

example: (p → q) → (¬ q → ¬ p) :=
  fun f q0 p0 => q0 (f p0)

example: ¬ ¬ ((¬ q → ¬ p) → (p → q)) :=
  fun ni =>
    let p0 : (¬ q → ¬ p) → (p → q) := fun f0 p0 =>
      let nq : ¬ q := fun q0 => ni (fun _ _ => q0)
      False.elim ((f0 nq) p0)
    ni p0

example: (¬ p ∨ q) → (p → q) :=
  fun h0 => match h0 with
    | Or.inl h => fun p0 => False.elim (h p0)
    | Or.inr h => fun _ => h

example: ¬ ¬ ((p → q) → (¬ p ∨ q)) :=
  fun h =>
    let npq :  ¬p ∨ q :=
      Or.inl (fun p0 => h (fun f =>Or.inr (f p0)))
    h fun _ => npq
