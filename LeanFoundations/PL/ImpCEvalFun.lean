/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Evaluation Function for Imp" chapter from
Software Foundations (Logical Foundations).
-/

import LeanFoundations.PL.ImpParser

/-!
# Evaluation Function for Imp

We saw in the Imp chapter how a naive approach to defining a function representing evaluation
for Imp runs into difficulties. There, we adopted the solution of defining evaluation as a
*relation* rather than a *function*. But functions have some advantages over relations: for
instance, we can *run* a function to compute the behavior of a program, while we can only
*reason* about a relation.

It turns out that, with a bit more work, we *can* define evaluation as a function. The key
insight is that we can make the function *partial* by having it return an `Option` type,
where `none` represents non-termination and `some st` represents termination in state `st`.

## A Broken Evaluator

Here's an attempt at defining an evaluation function for commands, based on the evaluation
relation we saw previously. This doesn't work because of termination issues with while loops:

```lean
def ceval_step_broken (st : State) : Com → Option State
  | Com.CSkip => some st
  | Com.CAss x a => some (x !-> (aeval st a) ; st)
  | Com.CSeq c1 c2 =>
    match ceval_step_broken st c1 with
    | none => none
    | some st' => ceval_step_broken st' c2
  | Com.CIf b c1 c2 =>
    if beval st b
    then ceval_step_broken st c1
    else ceval_step_broken st c2
  | Com.CWhile b c =>
    if beval st b
    then match ceval_step_broken st c with
         | none => none
         | some st' => ceval_step_broken st' (Com.CWhile b c)  -- Problem!
    else some st
```

The problem is that in the `CWhile` case, we make a recursive call to `ceval_step_broken` on
the same `CWhile` command. Lean's termination checker rejects this definition because the
recursive call is not on a structurally smaller argument.

## A Step-Indexed Evaluator

The solution is to use a *step-indexed* evaluator. The idea is to add an extra numeric argument
that decreases with each step of evaluation. When this number reaches zero, we give up and
return `none`, indicating that the evaluation didn't complete within the given number of steps.
-/

def ceval_step (fuel : Nat) (st : State) : Com → Option State
  | Com.CSkip => some st
  | Com.CAss x a => some (x !-> (aeval st a) ; st)
  | Com.CSeq c1 c2 =>
    match ceval_step fuel st c1 with
    | none => none
    | some st' => ceval_step fuel st' c2
  | Com.CIf b c1 c2 =>
    if beval st b
    then ceval_step fuel st c1
    else ceval_step fuel st c2
  | Com.CWhile b c =>
    match fuel with
    | 0 => none  -- Out of fuel
    | fuel' + 1 =>
      if beval st b
      then match ceval_step fuel' st c with
           | none => none
           | some st' => ceval_step fuel' st' (Com.CWhile b c)
      else some st

/-!
### Exercise: 2 stars, standard (ceval_step_example1)

Before we prove the correctness of the step-indexed evaluator, let's make sure it works on
a simple example.
-/

example : ceval_step 10 empty_st (assign "X" (AExp.ANum 2)) = some ("X" !-> 2 ; empty_st) := by
  sorry

/-!
### Exercise: 2 stars, standard (ceval_step_example2)

Let's try a sequence:
-/

example : ceval_step 10 empty_st
  (seq (assign "X" (AExp.ANum 1)) (assign "Y" (AExp.ANum 2)))
  = some ("Y" !-> 2 ; "X" !-> 1 ; empty_st) := by
  sorry

/-!
### Exercise: 3 stars, standard (ceval_step_example3)

Let's try a conditional:
-/

example : ceval_step 10 empty_st
  (ifthenelse (BExp.BEq (AExp.ANum 1) (AExp.ANum 1))
              (assign "X" (AExp.ANum 1))
              (assign "X" (AExp.ANum 2)))
  = some ("X" !-> 1 ; empty_st) := by
  sorry

/-!
### Exercise: 4 stars, standard (ceval_step_example4)

Now let's try a while loop. This one should terminate:
-/

def test_while : Com :=
  seq (assign "X" (AExp.ANum 3))
  (whiledo (BExp.BNot (BExp.BEq (AExp.AId "X") (AExp.ANum 0)))
           (assign "X" (AExp.AMinus (AExp.AId "X") (AExp.ANum 1))))

example : ceval_step 10 empty_st test_while = some ("X" !-> 0 ; empty_st) := by
  sorry

/-!
### Exercise: 3 stars, standard (ceval_step_example5)

What about a while loop that doesn't terminate? If we give it enough fuel, it should run for
a while. If we don't give it enough fuel, it should return `none`.
-/

def infinite_loop : Com := whiledo BExp.BTrue skip

example : ceval_step 5 empty_st infinite_loop = none := by
  sorry

/-!
## Relational vs. Step-Indexed Evaluation

As for arithmetic and boolean expressions, we'd hope that the two alternative definitions of
evaluation would agree on those programs that terminate. We'll now investigate this.

### Exercise: 3 stars, standard (ceval_step_more)

The `ceval_step` function is *monotonic* in the sense that, if `ceval_step i st c = some st'`,
then `ceval_step (i + j) st c = some st'` for any `j`.
-/

theorem ceval_step_more : ∀ i j c st st',
  ceval_step i st c = some st' →
  ceval_step (i + j) st c = some st' := by
  sorry

/-!
### Exercise: 4 stars, standard (ceval__ceval_step)

The following theorem shows that the relational and step-indexed definitions of evaluation
are equivalent for terminating programs.
-/

theorem ceval__ceval_step : ∀ c st st',
  ceval c st st' →
  ∃ i, ceval_step i st c = some st' := by
  sorry

/-!
### Exercise: 4 stars, standard (ceval_step__ceval)

For the converse direction, we need to be a bit careful. We can't prove that if
`ceval_step i st c = some st'` then `ceval c st st'`, because `i` might be too small for
`c` to terminate. But we can prove that if `ceval_step` returns `some st'` for *some* number
of steps `i`, then the relational evaluation succeeds.
-/

theorem ceval_step__ceval : ∀ i c st st',
  ceval_step i st c = some st' →
  ceval c st st' := by
  sorry

/-!
### Exercise: 4 stars, standard (ceval_step_complete)

The step-indexed evaluator is *complete* in the sense that if a program terminates according
to the relational semantics, then the step-indexed evaluator will find a result for some
sufficiently large step count.
-/

theorem ceval_step_complete : ∀ c st st',
  ceval c st st' →
  ∃ i, ceval_step i st c = some st' := by
  exact ceval__ceval_step

/-!
## Determinism of Evaluation Again

Using the functional evaluator, we can give a shorter proof that the evaluation relation is
deterministic.
-/

theorem ceval_deterministic' : ∀ c st st1 st2,
  ceval c st st1 →
  ceval c st st2 →
  st1 = st2 := by
  sorry

/-!
## Reasoning About Imp Programs

We can use either the relational or the functional definition of evaluation to reason about
Imp programs. The functional definition is often more convenient for *computing* the behavior
of programs, while the relational definition can be more convenient for *proving* things about
programs.

### Exercise: 3 stars, standard (plus2_spec)

Here's a specification of a program that adds 2 to the value of `X`:
-/

theorem plus2_spec : ∀ st n,
  st "X" = n →
  ceval plus2 st ("X" !-> (n + 2) ; st) := by
  intro st n H
  unfold plus2
  apply ceval.E_Ass
  simp [aeval, H]

/-!
### Exercise: 3 stars, standard (XtimesYinZ_spec)

Here's a specification of a program that multiplies the values of `X` and `Y` and stores
the result in `Z`:
-/

theorem XtimesYinZ_spec : ∀ st x y,
  st "X" = x →
  st "Y" = y →
  ceval XtimesYinZ st ("Z" !-> (x * y) ; st) := by
  intro st x y Hx Hy
  unfold XtimesYinZ
  apply ceval.E_Ass
  simp [aeval, Hx, Hy]

/-!
### Exercise: 3 stars, standard (loop_never_stops)

Here's a proof that our infinite loop never terminates:
-/

theorem loop_never_stops : ∀ st st',
  ¬ ceval loop st st' := by
  sorry

/-!
## Evaluation as a Lean Function

Our step-indexed evaluator is written as a Lean function, which means we can actually *run*
it to compute the behavior of Imp programs.

### Exercise: 2 stars, standard (factorial_in_lean)

Let's define the factorial program and test it:
-/

def factorial_program : Com :=
  seq (assign "Y" (AExp.ANum 1))
  (whiledo (BExp.BNot (BExp.BEq (AExp.AId "X") (AExp.ANum 0)))
    (seq (assign "Y" (AExp.AMult (AExp.AId "Y") (AExp.AId "X")))
         (assign "X" (AExp.AMinus (AExp.AId "X") (AExp.ANum 1)))))

-- Test factorial of 3
example : ceval_step 100 ("X" !-> 3 ; empty_st) factorial_program
        = some ("Y" !-> 6 ; "X" !-> 0 ; empty_st) := by
  sorry

/-!
## Additional Exercises

### Exercise: 4 stars, advanced (break_imp)

Imperative languages usually include a `break` or similar statement for interrupting the
execution of loops. In this exercise we consider how to add `break` to Imp. First, we need
to enrich the language of commands with an additional case.
-/

inductive ComBreak : Type where
  | CSkip : ComBreak
  | CBreak : ComBreak  -- New: break statement
  | CAss (x : Identifier) (a : AExp) : ComBreak
  | CSeq (c1 c2 : ComBreak) : ComBreak
  | CIf (b : BExp) (c1 c2 : ComBreak) : ComBreak
  | CWhile (b : BExp) (c : ComBreak) : ComBreak

/-!
Next, we need to define the behavior of `break`. One way of expressing this behavior is to
add another parameter to the evaluation relation that specifies whether evaluation of a
command executes a `break` statement:
-/

inductive Result : Type where
  | SContinue (st : State) : Result  -- Normal termination
  | SBreak (st : State) : Result     -- Terminated by break

inductive cevalBreak : ComBreak → State → Result → Prop where
  | E_Skip (st : State) :
      cevalBreak ComBreak.CSkip st (Result.SContinue st)
  | E_Break (st : State) :
      cevalBreak ComBreak.CBreak st (Result.SBreak st)
  | E_Ass (st : State) (a1 : AExp) (n : Nat) (x : Identifier) :
      aeval st a1 = n →
      cevalBreak (ComBreak.CAss x a1) st (Result.SContinue (x !-> n ; st))
  | E_SeqContinue (c1 c2 : ComBreak) (st st' st'' : State) :
      cevalBreak c1 st (Result.SContinue st') →
      cevalBreak c2 st' (Result.SContinue st'') →
      cevalBreak (ComBreak.CSeq c1 c2) st (Result.SContinue st'')
  | E_SeqBreak (c1 c2 : ComBreak) (st st' : State) :
      cevalBreak c1 st (Result.SBreak st') →
      cevalBreak (ComBreak.CSeq c1 c2) st (Result.SBreak st')
  | E_IfTrue (st st' : State) (b : BExp) (c1 c2 : ComBreak) :
      beval st b = true →
      cevalBreak c1 st (Result.SContinue st') →
      cevalBreak (ComBreak.CIf b c1 c2) st (Result.SContinue st')
  | E_IfFalse (st st' : State) (b : BExp) (c1 c2 : ComBreak) :
      beval st b = false →
      cevalBreak c2 st (Result.SContinue st') →
      cevalBreak (ComBreak.CIf b c1 c2) st (Result.SContinue st')
  | E_WhileFalse (b : BExp) (c : ComBreak) (st : State) :
      beval st b = false →
      cevalBreak (ComBreak.CWhile b c) st (Result.SContinue st)
  | E_WhileTrue (st st' st'' : State) (b : BExp) (c : ComBreak) :
      beval st b = true →
      cevalBreak c st (Result.SContinue st') →
      cevalBreak (ComBreak.CWhile b c) st' (Result.SContinue st'') →
      cevalBreak (ComBreak.CWhile b c) st (Result.SContinue st'')
  | E_WhileBreak (st st' : State) (b : BExp) (c : ComBreak) :
      beval st b = true →
      cevalBreak c st (Result.SBreak st') →
      cevalBreak (ComBreak.CWhile b c) st (Result.SContinue st')

/-!
### Exercise: 3 stars, advanced (break_ignore)

Prove the following theorem:
-/

theorem break_ignore : ∀ c st st' s,
  cevalBreak c st (Result.SContinue st') →
  cevalBreak (ComBreak.CSeq c (ComBreak.CAss s (AExp.ANum 1))) st (Result.SContinue (s !-> 1 ; st')) := by
  sorry

/-!
### Exercise: 4 stars, advanced (while_break_true)

Prove the following theorem:
-/

theorem while_break_true : ∀ b c st st',
  cevalBreak (ComBreak.CWhile b c) st (Result.SContinue st') →
  beval st' b = false := by
  sorry
