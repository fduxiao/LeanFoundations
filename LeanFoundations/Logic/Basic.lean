/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

-/

/-!
# Functional Programming in Lean

This chapter introduces the basics of functional programming in Lean.
The main differences from Coq are:

1. Syntax:
   - Lean uses `inductive` instead of `Inductive`
   - Lean uses `def` instead of `Definition`
   - Lean uses `|` for pattern matching instead of Coq's `|`
   - Lean uses `.constructor` syntax for constructors (e.g., `.zero` instead of `O`)
   - Lean uses `=>` instead of `⇒` for pattern matching
   - Lean uses `:=` instead of `:=` for definitions
   - Lean uses `by` instead of `Proof.` for proofs

2. Type system:
   - Lean has a more powerful type system with type classes
   - Lean's type checker can automatically prove many simple theorems
   - Lean uses `deriving Repr` for pretty printing
   - Lean has better type inference
   - Lean supports type classes and instances
   - Lean has a more modern module system

3. Tactics:
   - Lean uses `by` instead of Coq's `Proof.`
   - Lean has different tactics (e.g., `rw` instead of `rewrite`)
   - Lean's proof automation is more powerful
   - Lean uses `rfl` instead of `reflexivity`
   - Lean has `simp` for simplification
   - Lean has `cases` and `induction` for case analysis
   - Lean has `exact` and `apply` for applying lemmas

4. Notation:
   - Lean uses different notation for constructors and pattern matching
   - Lean has different syntax for type annotations
   - Lean uses different syntax for theorem declarations
   - Lean uses different syntax for quantifiers
   - Lean has different syntax for implications
   - Lean uses different syntax for equality

5. Proof Style:
   - Lean proofs are often more concise
   - Lean has better proof automation
   - Lean's type checker can prove more things automatically
   - Lean has better support for proof by calculation
   - Lean has better support for proof by induction
-/

/-!
## Enumerated Types

In Lean, we can define enumerated types using the `inductive` keyword, similar to Coq's `Inductive`.
The main difference is that Lean uses `|` for constructors instead of Coq's `|`.

Key differences:
1. Constructor syntax: Lean uses `.constructor` instead of just the constructor name
2. Pattern matching: Lean uses `=>` instead of `⇒`
3. Type declarations: Lean uses `:` instead of `:`
4. Module system: Lean has a different module system
-/

inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

/-!
## Functions on Enumerated Types

In Lean, we define functions using `def` instead of Coq's `Definition`.
Pattern matching syntax is similar but uses `|` instead of `|`.

Key differences:
1. Function definition: Lean uses `def` instead of `Definition`
2. Pattern matching: Lean uses `=>` instead of `⇒`
3. Constructor syntax: Lean uses `.constructor` instead of just the constructor name
4. Type annotations: Lean uses `:` instead of `:`
-/

def nextWorkingDay (d : Day) : Day :=
  match d with
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .monday
  | .saturday => .monday
  | .sunday => .monday

/-!
## Booleans

In Lean, booleans are built-in, but we can define our own for learning purposes.
The syntax is similar to Coq but with Lean's conventions.

Key differences:
1. Constructor syntax: Lean uses `.true` instead of `true`
2. Pattern matching: Lean uses `=>` instead of `⇒`
3. Type annotations: Lean uses `:` instead of `:`
4. Function definition: Lean uses `def` instead of `Definition`
-/

inductive MyBool where
  | true
  | false
deriving Repr

def negb (b : MyBool) : MyBool :=
  match b with
  | .true => .false
  | .false => .true

def andb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | .true => b2
  | .false => .false

def orb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | .true => .true
  | .false => b2

/-!
## Natural Numbers

In Lean, natural numbers are built-in, but we can define our own for learning.
The main difference from Coq is that Lean uses `Nat` instead of `nat` and has different syntax for constructors.

Key differences:
1. Constructor names: Lean uses `zero` and `succ` instead of `O` and `S`
2. Constructor syntax: Lean uses `.zero` instead of `O`
3. Pattern matching: Lean uses `=>` instead of `⇒`
4. Type annotations: Lean uses `:` instead of `:`
5. Function definition: Lean uses `def` instead of `Definition`
-/

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
deriving Repr

def pred (n : MyNat) : MyNat :=
  match n with
  | .zero => .zero
  | .succ n' => n'

def plus (n m : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n' => .succ (plus n' m)

def mult (n m : MyNat) : MyNat :=
  match n with
  | .zero => .zero
  | .succ n' => plus m (mult n' m)

/-!
## Proofs

In Lean, proofs are written using tactics similar to Coq, but with different syntax.
The main differences are:
1. Lean uses `by` instead of Coq's `Proof.`
2. Lean has different tactic names and syntax
3. Lean's proof automation is more powerful

Common proof techniques in Lean:
1. `cases`: For case analysis
2. `induction`: For inductive proofs
3. `rw`: For rewriting using equalities
4. `simp`: For simplification
5. `exact`: For applying lemmas
6. `apply`: For applying lemmas with unification
7. `rfl`: For reflexivity
8. `sorry`: For admitting a proof (temporarily)

Key differences in proof style:
1. Lean proofs are often more concise
2. Lean has better proof automation
3. Lean's type checker can prove more things automatically
4. Lean has better support for proof by calculation
5. Lean has better support for proof by induction
-/

/-!
Note: In Lean, many simple proofs can be done automatically by the type checker.
For educational purposes, we show the explicit proofs here.
-/

theorem plus_zero_n (n : MyNat) : plus .zero n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [plus]

theorem plus_succ_n (n m : MyNat) : plus (.succ n) m = .succ (plus n m) := by
  induction n with
  | zero =>
    rw [plus]
    rfl
  | succ n' ih =>
    rw [plus]

/-!
## Exercises

The following exercises are translated from Software Foundations.
Try to solve them yourself! Each exercise is marked with its difficulty level.

Tips for solving exercises:
1. Start by understanding the type of the function/theorem
2. Use pattern matching for function definitions
3. Use induction for proofs about natural numbers
4. Use case analysis for proofs about booleans
5. Use rewriting for proofs about equality
6. Use simplification for proofs about arithmetic
-/

/-!
### Exercise: 1 star, standard (nandb)
Define the function nandb (negated-and) that returns true if either or both of its inputs are false.

Hint: You can use pattern matching on both arguments at once using a comma.
-/

def nandb (b1 b2 : MyBool) : MyBool := sorry

/-!
### Exercise: 1 star, standard (andb3)
Define the function andb3 that returns true when all of its inputs are true, and false otherwise.

Hint: You can use pattern matching on all three arguments at once.
-/

def andb3 (b1 b2 b3 : MyBool) : MyBool := sorry

/-!
### Exercise: 1 star, standard (factorial)
Recall the standard mathematical factorial function:
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)
Translate this into Lean.

Hint: You'll need to use pattern matching and recursion.
-/

def factorial (n : MyNat) : MyNat := sorry

/-!
### Exercise: 1 star, standard (ltb)
Define the ltb function that tests natural numbers for less-than, yielding a boolean.

Hint: You can use pattern matching on both arguments at once.
-/

def ltb (n m : MyNat) : MyBool := sorry

/-!
### Exercise: 1 star, standard (identity_fn_applied_twice)
Prove the following theorem about boolean functions.

Hint: You'll need to use case analysis on the boolean argument.
-/

theorem identity_fn_applied_twice :
  ∀ (f : MyBool → MyBool),
  (∀ (x : MyBool), f x = x) →
  ∀ (b : MyBool), f (f b) = b := by
  sorry

/-!
### Exercise: 1 star, standard (negation_fn_applied_twice)
State and prove a theorem negation_fn_applied_twice similar to the previous one but where the second hypothesis says that the function f has the property that f x = negb x.

Hint: This is similar to the previous exercise, but you'll need to use the negb function.
-/

theorem negation_fn_applied_twice :
  ∀ (f : MyBool → MyBool),
  (∀ (x : MyBool), f x = negb x) →
  ∀ (b : MyBool), f (f b) = b := by
  sorry

/-!
### Exercise: 3 stars, standard (andb_eq_orb)
Prove the following theorem.

Hint: You'll need to use case analysis on both boolean arguments.
-/

theorem andb_eq_orb :
  ∀ (b c : MyBool),
  (andb b c = orb b c) →
  b = c := by
  sorry

/-!
### Exercise: 3 stars, standard (binary)
We can generalize our unary representation of natural numbers to the more efficient binary representation by treating a binary number as a sequence of constructors B0 and B1 (representing 0s and 1s), terminated by a Z.

Hint: You'll need to use pattern matching and recursion.
-/

inductive Bin where
  | Z
  | B0 (n : Bin)
  | B1 (n : Bin)
deriving Repr

def incr (b : Bin) : Bin :=
  match b with
  | .Z => .B1 .Z
  | .B0 b' => .B1 b'
  | .B1 b' => .B0 (incr b')

def bin_to_nat (b : Bin) : MyNat :=
  match b with
  | .Z => .zero
  | .B0 b' => plus (bin_to_nat b') (bin_to_nat b')
  | .B1 b' => MyNat.succ (plus (bin_to_nat b') (bin_to_nat b'))

/-!
### Exercise: 2 stars, standard (plus_comm)
Prove that addition is commutative.

Hint: You'll need to use induction on one of the arguments.
-/

theorem plus_comm (n m : MyNat) : plus n m = plus m n := by
  sorry

/-!
### Exercise: 2 stars, standard (plus_assoc)
Prove that addition is associative.

Hint: You'll need to use induction on one of the arguments.
-/

theorem plus_assoc (n m p : MyNat) : plus (plus n m) p = plus n (plus m p) := by
  sorry

/-!
### Exercise: 2 stars, standard (mult_comm)
Prove that multiplication is commutative.

Hint: You'll need to use induction and the plus_comm theorem.
-/

theorem mult_comm (n m : MyNat) : mult n m = mult m n := by
  sorry

/-!
## Testing Your Solutions

Each exercise comes with test cases that you can use to verify your solutions.
For example, for the nandb function:

Example test_nandb1: (nandb .true .false) = .true := by
  sorry

Example test_nandb2: (nandb .false .false) = .true := by
  sorry

Example test_nandb3: (nandb .false .true) = .true := by
  sorry

Example test_nandb4: (nandb .true .true) = .false := by
  sorry

Try to prove these test cases after implementing the functions!

Tips for testing:
1. Start with simple cases
2. Test edge cases
3. Test with different combinations of inputs
4. Use the test cases to guide your implementation
5. Make sure your implementation matches the test cases
-/
