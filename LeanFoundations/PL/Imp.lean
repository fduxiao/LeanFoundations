/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Simple Imperative Programs" chapter from
Software Foundations (Logical Foundations).
-/

import LeanFoundations.PL.Maps

/-!
# Simple Imperative Programs

In this chapter, we take a more serious look at how to use Lean to study other things.
Our case study is a *simple imperative programming language* called Imp.

Here is a familiar mathematical function written in Imp:

```
     Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end
```

This chapter looks at how to define the *syntax* and *semantics* of Imp; the chapters that
follow develop a theory of *program equivalence* and introduce *Hoare Logic*, a widely used
logic for reasoning about imperative programs.

## Arithmetic and Boolean Expressions

We'll present Imp in three parts: first a core language of *arithmetic and boolean expressions*,
then an extension with *variables*, and finally a language of *commands* with assignment,
conditionals, sequencing, and loops.

### Syntax

Module for a simple expression language.
-/

-- We'll use String for identifiers to avoid conflicts with Maps
abbrev Identifier : Type := String

-- Arithmetic expressions
inductive AExp : Type where
  | ANum (n : Nat) : AExp
  | AId (x : Identifier) : AExp
  | APlus (a1 a2 : AExp) : AExp
  | AMinus (a1 a2 : AExp) : AExp
  | AMult (a1 a2 : AExp) : AExp

-- Boolean expressions
inductive BExp : Type where
  | BTrue : BExp
  | BFalse : BExp
  | BEq (a1 a2 : AExp) : BExp
  | BLe (a1 a2 : AExp) : BExp
  | BNot (b : BExp) : BExp
  | BAnd (b1 b2 : BExp) : BExp

/-!
Let's look at a couple of examples of translating from informal syntax to abstract syntax trees.
-/

-- Example: The arithmetic expression `1 + 2 * 3`
def example_aexp : AExp := AExp.APlus (AExp.ANum 1) (AExp.AMult (AExp.ANum 2) (AExp.ANum 3))

-- Example: The boolean expression `true && ~(X ≤ Y)`
def example_bexp : BExp := BExp.BAnd BExp.BTrue (BExp.BNot (BExp.BLe (AExp.AId "X") (AExp.AId "Y")))

/-!
### Evaluation

*Evaluating* an arithmetic expression produces a number.
-/

def State : Type := total_map Nat

def aeval (st : State) : AExp → Nat
  | AExp.ANum n => n
  | AExp.AId x => st x
  | AExp.APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AExp.AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AExp.AMult a1 a2 => (aeval st a1) * (aeval st a2)

/-!
We use the notation `{ !-> 0 }` for the empty state, which maps all identifiers to `0`.
-/

def empty_st : State := { !-> 0 }

/-!
Now we can evaluate arithmetic expressions in the empty state:
-/

example : aeval empty_st example_aexp = 7 := by rfl

/-!
Similarly, evaluating a boolean expression in a state yields a boolean.
-/

def beval (st : State) : BExp → Bool
  | BExp.BTrue => true
  | BExp.BFalse => false
  | BExp.BEq a1 a2 => (aeval st a1) == (aeval st a2)
  | BExp.BLe a1 a2 => (aeval st a1) ≤ (aeval st a2)
  | BExp.BNot b1 => !(beval st b1)
  | BExp.BAnd b1 b2 => (beval st b1) && (beval st b2)

/-!
### Optimization

We haven't defined very much yet, but we can already get some mileage out of the definitions.
Suppose we define a function that takes an arithmetic expression and slightly simplifies it,
changing every occurrence of `0 + e` (i.e., `APlus (ANum 0) e`) into just `e`.
-/

def optimize_0plus : AExp → AExp
  | AExp.ANum n => AExp.ANum n
  | AExp.AId x => AExp.AId x
  | AExp.APlus (AExp.ANum 0) e2 => optimize_0plus e2
  | AExp.APlus e1 e2 => AExp.APlus (optimize_0plus e1) (optimize_0plus e2)
  | AExp.AMinus e1 e2 => AExp.AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AExp.AMult e1 e2 => AExp.AMult (optimize_0plus e1) (optimize_0plus e2)

/-!
To make sure our optimization is doing the right thing we can test it on some examples and see
if the output looks OK.
-/

example : optimize_0plus (AExp.APlus (AExp.ANum 0) (AExp.APlus (AExp.ANum 3) (AExp.ANum 1)))
        = AExp.APlus (AExp.ANum 3) (AExp.ANum 1) := by rfl

/-!
But if we want to be sure the optimization is correct -- i.e., that evaluating an optimized
expression gives the same result as the original -- we should prove it.
-/

theorem optimize_0plus_sound : ∀ a : AExp, aeval empty_st (optimize_0plus a) = aeval empty_st a := by
  sorry

/-!
### Exercise: 3 stars, standard (optimize_0plus_b_sound)

Since the `optimize_0plus` transformation doesn't touch boolean expressions, its soundness is
trivial. But suppose for a moment that we wanted to extend the optimization to boolean expressions,
what would it look like?
-/

-- Exercise: Define an optimization for boolean expressions
def optimize_0plus_b : BExp → BExp
  | BExp.BTrue => BExp.BTrue
  | BExp.BFalse => BExp.BFalse
  | BExp.BEq a1 a2 => BExp.BEq (optimize_0plus a1) (optimize_0plus a2)
  | BExp.BLe a1 a2 => BExp.BLe (optimize_0plus a1) (optimize_0plus a2)
  | BExp.BNot b => BExp.BNot (optimize_0plus_b b)
  | BExp.BAnd BExp.BTrue b2 => optimize_0plus_b b2  -- true && b = b
  | BExp.BAnd b1 b2 => BExp.BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)

-- Exercise: Prove soundness
theorem optimize_0plus_b_sound : ∀ b : BExp, beval empty_st (optimize_0plus_b b) = beval empty_st b := by
  sorry

/-!
## Evaluation as a Relation

We have presented `aeval` and `beval` as functions defined by pattern matching. Another way to
think about evaluation -- one that we will see is often more flexible -- is as a *relation*
between expressions, states, and their values. This leads naturally to Lean inductive definitions.

Here's the relational definition of arithmetic expression evaluation:
-/

inductive aevalR : AExp → State → Nat → Prop where
  | E_ANum (n : Nat) (st : State) :
      aevalR (AExp.ANum n) st n
  | E_AId (x : Identifier) (st : State) :
      aevalR (AExp.AId x) st (st x)
  | E_APlus (e1 e2 : AExp) (n1 n2 : Nat) (st : State) :
      aevalR e1 st n1 →
      aevalR e2 st n2 →
      aevalR (AExp.APlus e1 e2) st (n1 + n2)
  | E_AMinus (e1 e2 : AExp) (n1 n2 : Nat) (st : State) :
      aevalR e1 st n1 →
      aevalR e2 st n2 →
      aevalR (AExp.AMinus e1 e2) st (n1 - n2)
  | E_AMult (e1 e2 : AExp) (n1 n2 : Nat) (st : State) :
      aevalR e1 st n1 →
      aevalR e2 st n2 →
      aevalR (AExp.AMult e1 e2) st (n1 * n2)

/-!
Here's a simple example:
-/

example : aevalR (AExp.APlus (AExp.ANum 3) (AExp.ANum 5)) empty_st 8 := by
  sorry

/-!
### Exercise: 3 stars, standard (aeval_iff_aevalR)

Prove that the relational and functional definitions of evaluation agree:
-/

theorem aeval_iff_aevalR : ∀ a st n, aevalR a st n ↔ aeval st a = n := by
  intro a st n
  constructor
  · -- aevalR a st n → aeval st a = n
    intro H
    induction H with
    | E_ANum => rfl
    | E_AId => rfl
    | E_APlus e1 e2 n1 n2 st H1 H2 ih1 ih2 =>
      simp [aeval, ih1, ih2]
    | E_AMinus e1 e2 n1 n2 st H1 H2 ih1 ih2 =>
      simp [aeval, ih1, ih2]
    | E_AMult e1 e2 n1 n2 st H1 H2 ih1 ih2 =>
      simp [aeval, ih1, ih2]
  · -- aeval st a = n → aevalR a st n
    intro H
    induction a generalizing n with
    | ANum n' =>
      simp [aeval] at H
      rw [← H]
      apply aevalR.E_ANum
    | AId x =>
      simp [aeval] at H
      rw [← H]
      apply aevalR.E_AId
    | APlus a1 a2 ih1 ih2 =>
      simp [aeval] at H
      rw [← H]
      apply aevalR.E_APlus
      · apply ih1; rfl
      · apply ih2; rfl
    | AMinus a1 a2 ih1 ih2 =>
      simp [aeval] at H
      rw [← H]
      apply aevalR.E_AMinus
      · apply ih1; rfl
      · apply ih2; rfl
    | AMult a1 a2 ih1 ih2 =>
      simp [aeval] at H
      rw [← H]
      apply aevalR.E_AMult
      · apply ih1; rfl
      · apply ih2; rfl

/-!
## Commands

Now we're ready to define the syntax and semantics of Imp *commands* (or *statements*).

### Syntax

Here is the formal definition of the abstract syntax of commands:
-/

inductive Com : Type where
  | CSkip : Com
  | CAss (x : Identifier) (a : AExp) : Com
  | CSeq (c1 c2 : Com) : Com
  | CIf (b : BExp) (c1 c2 : Com) : Com
  | CWhile (b : BExp) (c : Com) : Com

/-!
Let's define some helper functions to make writing commands more convenient:
-/

def skip : Com := Com.CSkip
def assign (x : Identifier) (a : AExp) : Com := Com.CAss x a
def seq (c1 c2 : Com) : Com := Com.CSeq c1 c2
def ifthenelse (b : BExp) (c1 c2 : Com) : Com := Com.CIf b c1 c2
def whiledo (b : BExp) (c : Com) : Com := Com.CWhile b c

/-!
For example, here is the factorial function again, written as a formal definition:
-/

def fact_in_lean : Com :=
  seq (assign "Z" (AExp.AId "X"))
  (seq (assign "Y" (AExp.ANum 1))
  (whiledo (BExp.BNot (BExp.BEq (AExp.AId "Z") (AExp.ANum 0)))
    (seq (assign "Y" (AExp.AMult (AExp.AId "Y") (AExp.AId "Z")))
         (assign "Z" (AExp.AMinus (AExp.AId "Z") (AExp.ANum 1))))))

/-!
### More Examples

Assignment:
-/

def plus2 : Com := assign "X" (AExp.APlus (AExp.AId "X") (AExp.ANum 2))

def XtimesYinZ : Com := assign "Z" (AExp.AMult (AExp.AId "X") (AExp.AId "Y"))

def subtract_slowly_body : Com :=
  seq (assign "Z" (AExp.AMinus (AExp.AId "Z") (AExp.ANum 1)))
      (assign "X" (AExp.AMinus (AExp.AId "X") (AExp.ANum 1)))

def subtract_slowly : Com :=
  whiledo (BExp.BNot (BExp.BEq (AExp.AId "X") (AExp.ANum 0)))
          subtract_slowly_body

def subtract_3_from_5_slowly : Com :=
  seq (assign "X" (AExp.ANum 3))
  (seq (assign "Z" (AExp.ANum 5))
       subtract_slowly)

/-!
### An infinite loop:
-/

def loop : Com := whiledo BExp.BTrue skip

/-!
## Evaluating Commands

Next we need to define what it means to evaluate an Imp command. The fact that `WHILE` loops
don't necessarily terminate makes defining evaluation tricky...

### Evaluation as a Relation

Here's a better way: define `ceval` as a *relation* rather than a function -- i.e., define it
in `Prop` instead of `Type`, parameterized by the command to be evaluated, the initial state,
and the final state.
-/

inductive ceval : Com → State → State → Prop where
  | E_Skip (st : State) :
      ceval Com.CSkip st st
  | E_Ass (st : State) (a1 : AExp) (n : Nat) (x : Identifier) :
      aeval st a1 = n →
      ceval (Com.CAss x a1) st (x !-> n ; st)
  | E_Seq (c1 c2 : Com) (st st' st'' : State) :
      ceval c1 st st' →
      ceval c2 st' st'' →
      ceval (Com.CSeq c1 c2) st st''
  | E_IfTrue (st st' : State) (b : BExp) (c1 c2 : Com) :
      beval st b = true →
      ceval c1 st st' →
      ceval (Com.CIf b c1 c2) st st'
  | E_IfFalse (st st' : State) (b : BExp) (c1 c2 : Com) :
      beval st b = false →
      ceval c2 st st' →
      ceval (Com.CIf b c1 c2) st st'
  | E_WhileFalse (b : BExp) (c : Com) (st : State) :
      beval st b = false →
      ceval (Com.CWhile b c) st st
  | E_WhileTrue (st st' st'' : State) (b : BExp) (c : Com) :
      beval st b = true →
      ceval c st st' →
      ceval (Com.CWhile b c) st' st'' →
      ceval (Com.CWhile b c) st st''

/-!
The cost of defining evaluation as a relation instead of a function is that we now need to
construct *proofs* that some program evaluates to some result, rather than just letting Lean's
computation mechanism do it for us.
-/

example : ceval (assign "X" (AExp.ANum 5)) empty_st ("X" !-> 5 ; empty_st) := by
  apply ceval.E_Ass
  rfl

/-!
### Exercise: 2 stars, standard (ceval_example1)
-/

example :
  ceval
    (seq (assign "X" (AExp.ANum 2))
         (ifthenelse (BExp.BLe (AExp.AId "X") (AExp.ANum 1))
                     (assign "Y" (AExp.ANum 3))
                     (assign "Z" (AExp.ANum 4))))
    empty_st
    ("Z" !-> 4 ; "X" !-> 2 ; empty_st) := by
  apply ceval.E_Seq
  · apply ceval.E_Ass; rfl
  · apply ceval.E_IfFalse
    · simp [beval, aeval, empty_st, t_update]
    · apply ceval.E_Ass; rfl

/-!
### Exercise: 2 stars, standard (ceval_example2)
-/

example :
  ceval
    (seq (assign "X" (AExp.ANum 0))
    (seq (assign "Y" (AExp.ANum 1))
         (assign "Z" (AExp.ANum 1))))
    empty_st
    ("Z" !-> 1 ; "Y" !-> 1 ; "X" !-> 0 ; empty_st) := by
  apply ceval.E_Seq
  · apply ceval.E_Ass; rfl
  · apply ceval.E_Seq
    · apply ceval.E_Ass; rfl
    · apply ceval.E_Ass; rfl

/-!
### Exercise: 3 stars, standard (pup_to_n)

Write an Imp program that sums the numbers from `1` to `X` (inclusive: `1 + 2 + ... + X`)
in the variable `Y`. Prove that your program executes correctly for `X = 2`.
-/

def pup_to_2 : Com :=
  seq (assign "Y" (AExp.ANum 0))
  (seq (assign "Z" (AExp.ANum 1))
  (whiledo (BExp.BLe (AExp.AId "Z") (AExp.AId "X"))
    (seq (assign "Y" (AExp.APlus (AExp.AId "Y") (AExp.AId "Z")))
         (assign "Z" (AExp.APlus (AExp.AId "Z") (AExp.ANum 1))))))

theorem pup_to_2_ceval :
  ceval pup_to_2 ("X" !-> 2 ; empty_st) ("Y" !-> 3 ; "Z" !-> 3 ; "X" !-> 2 ; empty_st) := by
  sorry

/-!
## Determinism of Evaluation

Changing from a computational to a relational definition of evaluation is a good move because
it allows us to escape from the artificial requirement that evaluation should be a total function.
But it also raises a question: is the second definition of evaluation really a partial function?
Or is it possible that, beginning from the same state `st`, we could evaluate some command `c`
in different ways to reach two different output states `st'` and `st''`?

In fact, this cannot happen: `ceval` *is* a partial function. Here is the proof:
-/

theorem ceval_deterministic : ∀ c st st1 st2,
  ceval c st st1 →
  ceval c st st2 →
  st1 = st2 := by
  sorry
