
/-!
# Lean ingredients

## Expressions
-/

-- use #eval to get the value of a given expression
#eval 2 -- 2
#eval 2 + 3 -- 5
#eval [1, 2, 3] ++ [4] -- [1, 2, 3, 4]

-- `fun` is a lambda abstraction
#eval (fun x => x + 3) 5 -- 8

/-!
## Types

Each expression has an associated type. To get the Type of an expression
we can ask with #check
-/
#check 2 -- Nat
#check [2] -- List Nat
#check [[2]] -- List List Nat

#check 2 = 3 -- Prop

#check fun x : Nat => x + 3 -- Nat → Nat


/-!
## Universes

Lean works with Type universes defined inductively. Each type has a type
and there are rules to preserve some 'coherence' and avoid paradoxical
behaviours.
-/

#check Nat -- Type
#check List Nat -- Type
#check Type -- Type 1

#check Type 1 → Type 1 -- Type 2

#check Prop -- Type

#check (α : Type 1) → (P : (Type 1 →  Prop)) →  P α  -- Prop


/-! ## Function definition -/

def plus2 (x : Nat): Nat := x + 2

def plus2Curry: Nat → Nat := fun x => x + 2

-- pattern matching
def greaterThan2 : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | _ => true

def sum (xs : List Nat) :=
  match xs with
  | [] => 0
  | x :: xs => x + sum xs


/-! ## Types and type constructors -/

-- structures are like records
structure Pair (α β : Type) where
  intro :: -- constructor
  one : α
  two : β

def pair1 : Pair Nat Bool := Pair.intro 1 false

-- inductive allows several constructors
inductive MyNat where
  | myZero : MyNat
  | mySucc : MyNat → MyNat

inductive MyList (α : Type) where
  | MyNil : MyList α
  | MyCons : α → MyList α → MyList α


/-! ## Dependent types and functions -/

inductive MyFin: Nat → Type where
  | myZ : MyFin 0
  | mySucc : MyFin n → MyFin (n + 1)

def toNat : MyFin n → Nat := fun _ => n

def twoTypes: Nat → Type
  | 0 => Bool
  | _ => String

def toFin (x : Nat) : MyFin x :=
  match x with
  | 0 => MyFin.myZ
  | x0 + 1 =>  MyFin.mySucc (toFin x0)

-- Vectors: List of fixed length
inductive V (α : Type) : Nat → Type where
  | nil : V α 0
  | cons : α → V α n → V α (n + 1)
open V

def append {α : Type} (l1 : V α n) (l2: V α m): V α (n + m) :=
match l2 with
  | nil => l1
  | cons a l2s => cons a (append l1 l2s)

def length (_: V α n) : Nat := n

/-!
## Recursion (a total programming language)

Lean, as Agda, is a total functional programming language. This means that every
program must halt, for it to properly emulate logic deductions. Lean allows us
to use arbitrary recursion and create arbitrary loops by using the `unsafe`
keyword.
-/

-- with unsafe, we can built a value of any single type, and, as we will see
-- in the CH correspondance, this means that any proposition is provable
unsafe
def loop : A := loop

-- this kind of definition is dangerous, as we can proof anything
unsafe
def contradiction : 0 = 1 := loop

-- Without this keyword, Lean is not turing complete, because every program
-- must halt (and the compiler should understand that it halts).

/-!
The way Lean regulates recursion is by using structural recursion. This means
that the compiler looks at every recursive call and checks if the argument of
the inductive type has a 'smaller' structure than the original argument.
-/

-- Lean knows that this program always halts because of the nature of Nat:
-- every call reduces one constructor of Nat.
def fact (n : Nat) :=  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fact n

#eval fact 7  -- 5040

-- ackermann function
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

#eval ack 3 2 -- 29

/-!
## #eval and #reduce

Once and expression is well-typed, you can #eval it without taking care of the
structure nor the typing of the expression. Everything is translated into
bytecode with types erased to ensure best performance.

#reduce simplifies an expression based on some kernel rules, but keeps all the
typing and structure in the process. It is less performant than #eval but may
handle non-computable expressions.
-/

#eval fact 7    -- 5040
#reduce fact 7  -- 5040

#eval fact 700
-- #reduce fact 700 -- maximum recursion depth

def f := fun (x : Nat) => fun (y : Nat) => x + y

-- #eval f 6 -- failed to be synthesized
#reduce f 6 -- normal form
