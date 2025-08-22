/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Relations" chapter from
Software Foundations (Logical Foundations).
-/

import LeanFoundations.Logic.IndPrinciples

/-!
# Relations

A binary *relation* on a set `X` is a family of propositions parameterized by two elements of `X`
-- i.e., a proposition about pairs of elements of `X`.

## Relations as Propositions

One way to think of a relation is as a *property* of pairs. For instance, we've seen the
relation `le` on numbers.
-/

#check le

/-!
The relation `le` gives us a family of propositions: for any two numbers `n` and `m`, we have
the proposition `n ≤' m`, which may or may not be provable.

## Basic Properties of Relations

As anyone knows who has taken an undergraduate discrete math course, there is a lot to be said
about relations in general, including ways of classifying relations (as reflexive, transitive,
etc.), theorems that can be proved generically about certain classes of relations, constructions
that build one relation from another, etc.

### Partial Functions

A relation `R` on a set `X` is a *partial function* if, for every `x`, there is at most one `y`
such that `R x y` -- i.e., `R x y1` and `R x y2` together imply `y1 = y2`.
-/

def partial_function_rel {X : Type} (R : X → X → Prop) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

/-!
For example, the `next_nat` relation is a partial function.
-/

inductive next_nat : Nat → Nat → Prop where
  | nn (n : Nat) : next_nat n (n + 1)

theorem next_nat_partial_function : partial_function_rel next_nat := by
  intro x y1 y2 H1 H2
  cases H1 with
  | nn =>
    cases H2 with
    | nn =>
      -- We have next_nat x (x + 1) and next_nat x (x + 1)
      -- Therefore y1 = y2 = x + 1
      rfl

/-!
However, the `≤` relation on numbers is not a partial function.

### Exercise: 2 stars, standard, optional (le_not_a_partial_function)

Show that the `≤` relation on naturals is not a partial function.
-/

theorem le_not_a_partial_function : ¬ partial_function_rel le := by
  intro H
  -- We'll show that le 0 0 and le 0 1, which would imply 0 = 1 by partial_function
  have H1 : le 0 0 := le.le_refl 0
  have H2 : le 0 1 := le.le_step 0 0 H1
  have : 0 = 1 := H 0 0 1 H1 H2
  -- This is a contradiction
  cases this

/-!
## Reflexive Relations

A relation `R` on a set `X` is *reflexive* if every element of `X` is related to itself.
-/

def reflexive_rel {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a : X, R a a

theorem le_reflexive_rel : reflexive_rel le := by
  intro a
  apply le.le_refl

/-!
## Transitive Relations

A relation `R` is *transitive* if `R a c` holds whenever `R a b` and `R b c` do.
-/

def transitive_rel {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

theorem le_transitive_rel : transitive_rel le := by
  intro a b c Hab Hbc
  induction Hbc with
  | le_refl => exact Hab
  | le_step c' Hbc' ih =>
    apply le.le_step
    exact ih

/-!
## Symmetric and Antisymmetric Relations

A relation `R` is *symmetric* if `R a b` implies `R b a`.
-/

def symmetric_rel {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b : X, R a b → R b a

/-!
### Exercise: 2 stars, standard, optional (le_not_symmetric)

Prove that the `≤` relation on naturals is not symmetric.
-/

theorem le_not_symmetric_rel : ¬ symmetric_rel le := by
  intro H
  have H1 : le 0 1 := le.le_step 0 0 (le.le_refl 0)
  have H2 : le 1 0 := H 0 1 H1
  -- Now we have le 1 0, which means 1 ≤ 0, but this is impossible
  cases H2

/-!
A relation `R` is *antisymmetric* if `R a b` and `R b a` together imply `a = b` -- that is,
if the only "cycles" in `R` are trivial ones.
-/

def antisymmetric_rel {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b : X, R a b → R b a → a = b

/-!
### Exercise: 2 stars, standard, optional (le_antisymmetric)
-/

theorem le_antisymmetric_rel : antisymmetric_rel le := by
  sorry

/-!
## Equivalence Relations

A relation is an *equivalence* if it's reflexive, symmetric, and transitive.
-/

def equivalence_rel {X : Type} (R : X → X → Prop) : Prop :=
  reflexive_rel R ∧ symmetric_rel R ∧ transitive_rel R

/-!
## Partial Orders and Preorders

A relation is a *partial order* when it's reflexive, antisymmetric, and transitive.
-/

def order_rel {X : Type} (R : X → X → Prop) : Prop :=
  reflexive_rel R ∧ antisymmetric_rel R ∧ transitive_rel R

/-!
A *preorder* is almost the same as a partial order, but doesn't require antisymmetry.
-/

def preorder_rel {X : Type} (R : X → X → Prop) : Prop :=
  reflexive_rel R ∧ transitive_rel R

theorem le_order_rel : order_rel le := by
  constructor
  · -- reflexive
    exact le_reflexive_rel
  constructor
  · -- antisymmetric
    exact le_antisymmetric_rel
  · -- transitive
    exact le_transitive_rel

/-!
## Reflexive, Transitive Closure

The *reflexive, transitive closure* of a relation `R` is the smallest relation that contains `R`
and that is both reflexive and transitive. We saw this concept earlier when we looked at the
`clos_refl_trans` relation in the IndProp chapter.

Let's define it again here and explore its properties:
-/

inductive clos_refl_trans_rel {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) : R x y → clos_refl_trans_rel R x y
  | rt_refl (x : X) : clos_refl_trans_rel R x x
  | rt_trans (x y z : X) : clos_refl_trans_rel R x y → clos_refl_trans_rel R y z → clos_refl_trans_rel R x z

/-!
### Exercise: 3 stars, standard, optional (clos_refl_trans_closure)

Use `clos_refl_trans_rel` to prove the following facts about relations.
-/

theorem rsc_R : ∀ (X : Type) (R : X → X → Prop) (x y : X),
  R x y → clos_refl_trans_rel R x y := by
  intro X R x y H
  apply clos_refl_trans_rel.rt_step
  exact H

theorem rsc_trans : ∀ (X : Type) (R : X → X → Prop) (x y z : X),
  clos_refl_trans_rel R x y → clos_refl_trans_rel R y z → clos_refl_trans_rel R x z := by
  intro X R x y z Hxy Hyz
  apply clos_refl_trans_rel.rt_trans
  exact Hxy
  exact Hyz
