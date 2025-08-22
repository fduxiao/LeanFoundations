/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Inductively Defined Propositions"
chapter from Software Foundations (Logical Foundations).
-/

import LeanFoundations.Logic.PropLogic

/-!
# Inductively Defined Propositions

In the Logic chapter, we looked at several ways of writing propositions, including
conjunction, disjunction, and existential quantification.

In this chapter, we bring yet another new tool into the mix: **inductively defined propositions**.

To begin, some examples...

## Example: The Collatz Conjecture

The Collatz Conjecture is a famous open problem in number theory.

Its statement is quite simple. First, we define a function `csf` on numbers, as follows
(where `csf` stands for "Collatz step function"):
-/

def div2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => (div2 n) + 1

def csf (n : Nat) : Nat :=
  if n % 2 = 0 then div2 n else (3 * n) + 1

/-!
Next, we look at what happens when we repeatedly apply `csf` to some given starting number.
For example, `csf 12` is `6`, and `csf 6` is `3`, so by repeatedly applying `csf` we get
the sequence `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.

Similarly, if we start with `19`, we get the longer sequence
`19, 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1`.

Both of these sequences eventually reach `1`. The question posed by Collatz was:
Is the sequence starting from any positive natural number guaranteed to reach `1` eventually?

Formally in Lean, the `Collatz_holds_for` property is inductively defined:
-/

inductive Collatz_holds_for : Nat → Prop where
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : Nat) : n % 2 = 0 →
                         Collatz_holds_for (div2 n) →
                         Collatz_holds_for n
  | Chf_odd (n : Nat) : n % 2 ≠ 0 →
                        Collatz_holds_for ((3 * n) + 1) →
                        Collatz_holds_for n

/-!
For particular numbers, we can now prove that the Collatz sequence reaches `1`:
-/

example : Collatz_holds_for 12 := by
  apply Collatz_holds_for.Chf_even
  · rfl  -- 12 % 2 = 0
  · simp [div2]
    apply Collatz_holds_for.Chf_even
    · rfl  -- 6 % 2 = 0
    · simp [div2]
      apply Collatz_holds_for.Chf_odd
      · simp  -- 3 % 2 ≠ 0
      · simp
        apply Collatz_holds_for.Chf_even
        · rfl  -- 10 % 2 = 0
        · simp [div2]
          apply Collatz_holds_for.Chf_odd
          · simp  -- 5 % 2 ≠ 0
          · simp
            apply Collatz_holds_for.Chf_even
            · rfl  -- 16 % 2 = 0
            · simp [div2]
              apply Collatz_holds_for.Chf_even
              · rfl  -- 8 % 2 = 0
              · simp [div2]
                apply Collatz_holds_for.Chf_even
                · rfl  -- 4 % 2 = 0
                · simp [div2]
                  apply Collatz_holds_for.Chf_even
                  · rfl  -- 2 % 2 = 0
                  · simp [div2]
                    apply Collatz_holds_for.Chf_one

/-!
## Example: Binary relation for comparing numbers

A binary relation on a set `X` has Lean type `X → X → Prop`. This is a family of propositions
parameterized by two elements of `X` -- i.e., a proposition about pairs of elements of `X`.

For example, one familiar binary relation on `Nat` is `LE : Nat → Nat → Prop`, the
less-than-or-equal-to relation, which can be inductively defined by the following two rules:

This corresponds to the following inductive definition in Lean:
-/

inductive le : Nat → Nat → Prop where
  | le_refl (n : Nat) : le n n
  | le_step (n m : Nat) : le n m → le n (m + 1)

-- We can use infix notation for our relation
infix:50 " ≤' " => le

/-!
Let's prove some examples:
-/

example : 3 ≤' 5 := by
  apply le.le_step
  apply le.le_step
  apply le.le_refl

/-!
## Example: Transitive Closure

As another example, the **transitive closure** of a relation `R` is the smallest relation
that contains `R` and that is transitive. In Lean this looks as follows:
-/

inductive clos_trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | t_step (x y : X) :
      R x y →
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y →
      clos_trans R y z →
      clos_trans R x z

/-!
For example, suppose we define a "parent of" relation on a group of people...
-/

inductive Person : Type where
  | Sage | Cleo | Ridley | Moss
deriving DecidableEq

inductive parent_of : Person → Person → Prop where
  | po_SC : parent_of Person.Sage Person.Cleo
  | po_SR : parent_of Person.Sage Person.Ridley
  | po_CM : parent_of Person.Cleo Person.Moss

/-!
The `parent_of` relation is not transitive, but we can define an "ancestor of" relation
as its transitive closure:
-/

def ancestor_of : Person → Person → Prop :=
  clos_trans parent_of

/-!
Here is a proof showing that Sage is an ancestor of Moss:
-/

example : ancestor_of Person.Sage Person.Moss := by
  unfold ancestor_of
  apply clos_trans.t_trans (y := Person.Cleo)
  · apply clos_trans.t_step
    apply parent_of.po_SC
  · apply clos_trans.t_step
    apply parent_of.po_CM

/-!
## Example: Evenness (yet again)

We've already seen two ways of stating a proposition that a number `n` is even: We can say
1. `n % 2 = 0` (using the modulo operation), or
2. `∃ k, n = 2 * k` (using an existential quantifier).

A third possibility, which we'll use as a simple running example here, is to say that a number
is even if we can establish its evenness from the following two rules:

We can translate the informal definition of evenness from above into a formal inductive declaration,
where each "way that a number can be even" corresponds to a separate constructor:
-/

inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat) (H : ev n) : ev (n + 2)

/-!
These evidence constructors can be thought of as "primitive evidence of evenness", and they can
be used just like proven theorems. In particular, we can use Lean's `apply` tactic with the
constructor names to obtain evidence for `ev` of particular numbers...
-/

theorem ev_4 : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_0

/-!
... or we can use function application syntax to combine several constructors:
-/

theorem ev_4' : ev 4 :=
  ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

/-!
In this way, we can also prove theorems that have hypotheses involving `ev`.
-/

theorem ev_plus4 : ∀ n, ev n → ev (4 + n) := by
  intro n Hn
  rw [Nat.add_comm]
  apply ev.ev_SS
  apply ev.ev_SS
  exact Hn

/-!
### Exercise: 1 star, standard (ev_double)
-/

theorem ev_double : ∀ n, ev (2 * n) := by
  intro n
  induction n with
  | zero =>
    simp
    apply ev.ev_0
  | succ n' ih =>
    simp [Nat.mul_succ]
    apply ev.ev_SS
    exact ih

/-!
## Using Evidence in Proofs

Besides constructing evidence that numbers are even, we can also destruct such evidence,
reasoning about how it could have been built.

Defining `ev` with an inductive declaration tells Lean not only that the constructors `ev_0`
and `ev_SS` are valid ways to build evidence that some number is `ev`, but also that these
two constructors are the **only** ways to build evidence that numbers are `ev`.

## Destructing and Inverting Evidence

Suppose we are proving some fact involving a number `n`, and we are given `ev n` as a hypothesis.
We already know how to perform case analysis on `n` using `cases` or `induction`, generating
separate subgoals for the case where `n = 0` and the case where `n = n' + 1` for some `n'`.
But for some proofs we may instead want to analyze the evidence for `ev n` directly.

As a tool for such proofs, we can formalize the intuitive characterization that we gave above
for evidence of `ev n`, using `cases`.
-/

theorem ev_inversion : ∀ (n : Nat),
    ev n →
    (n = 0) ∨ (∃ n', n = n' + 2 ∧ ev n') := by
  intro n E
  cases E with
  | ev_0 =>
    -- E = ev_0 : ev 0
    left
    rfl
  | ev_SS n' E' =>
    -- E = ev_SS n' E' : ev (n' + 2)
    right
    exists n'

/-!
### Exercise: 1 star, standard (le_inversion)

Let's prove a similar inversion lemma for `le`.
-/

theorem le_inversion : ∀ (n m : Nat),
  n ≤' m →
  (n = m) ∨ (∃ m', m = m' + 1 ∧ n ≤' m') := by
  intro n m H
  cases H with
  | le_refl =>
    left
    rfl
  | le_step m' H' =>
    right
    exists m'

/-!
We can use the inversion lemma that we proved above to help structure proofs:
-/

theorem evSS_ev : ∀ n, ev (n + 2) → ev n := by
  intro n E
  have h := ev_inversion (n + 2) E
  cases h with
  | inl h0 =>
    -- n + 2 = 0, which is impossible
    simp at h0
  | inr h1 =>
    obtain ⟨n', ⟨Hnn', E'⟩⟩ := h1
    -- n + 2 = n' + 2, so n = n'
    have : n = n' := by simp at Hnn'; exact Hnn'
    rw [this]
    exact E'

/-!
Lean provides a handy tactic called `cases` that factors out this common pattern, saving us the
trouble of explicitly stating and proving an inversion lemma for every inductive definition we make.

Here, the `cases` tactic can detect (1) that the first case, where `n + 2 = 0`, does not apply
and (2) that the `n'` that appears in the `ev_SS` case must be the same as `n`.
-/

theorem evSS_ev' : ∀ n, ev (n + 2) → ev n := by
  intro n E
  cases E with
  | ev_SS n' E' =>
    -- We are in the E = ev_SS n' E' case now.
    -- Since ev (n + 2) and ev_SS gives us ev (n' + 2), we have n = n'
    exact E'

/-!
The `cases` tactic can apply the principle of explosion to "obviously contradictory" hypotheses
involving inductively defined properties.
-/

theorem one_not_even : ¬ ev 1 := by
  intro H
  cases H

/-!
### Exercise: 1 star, standard (inversion_practice)

Prove the following result using `cases`. (For extra practice, you can also prove it using
the inversion lemma.)
-/

theorem SSSSev__even : ∀ n, ev (n + 4) → ev n := by
  intro n H
  cases H with
  | ev_SS n' H' =>
    cases H' with
    | ev_SS n'' H'' =>
      exact H''

/-!
### Exercise: 1 star, standard (ev5_nonsense)

Prove the following result using `cases`.
-/

theorem ev5_nonsense : ev 5 → 2 + 2 = 9 := by
  intro H
  cases H with
  | ev_SS n' H' =>
    cases H' with
    | ev_SS n'' H'' =>
      cases H''

/-!
## Induction on Evidence

If this story feels familiar, it is no coincidence: We encountered similar problems in the
Induction chapter, when trying to use case analysis to prove results that required induction.
And once again the solution is... induction!

The behavior of induction on evidence is the same as its behavior on data: It causes Lean to
generate one subgoal for each constructor that could have been used to build that evidence,
while providing an induction hypothesis for each recursive occurrence of the property in question.

To prove that a property of `n` holds for all even numbers (i.e., those for which `ev n` holds),
we can use induction on `ev n`. This requires us to prove two things, corresponding to the two
ways in which `ev n` could have been constructed. If it was constructed by `ev_0`, then `n=0`
and the property must hold of `0`. If it was constructed by `ev_SS`, then the evidence of `ev n`
is of the form `ev_SS n' E'`, where `n = n' + 2` and `E'` is evidence for `ev n'`. In this case,
the inductive hypothesis says that the property we are trying to prove holds for `n'`.

### Exercise: 2 stars, standard (ev_sum)
-/

theorem ev_sum : ∀ n m, ev n → ev m → ev (n + m) := by
  intro n m Hn Hm
  induction Hn with
  | ev_0 =>
    simp
    exact Hm
  | ev_SS n' E' IH =>
    -- Goal: ev (n' + 2 + m)
    -- We have IH : ev (n' + m)
    -- We want to show ev ((n' + m) + 2)
    have h : n' + 2 + m = (n' + m) + 2 := by
      rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
    rw [h]
    apply ev.ev_SS
    exact IH

/-!
### Exercise: 3 stars, advanced (ev_ev__ev)

Finding the appropriate thing to do induction on is a bit tricky here:
-/

theorem ev_ev__ev : ∀ n m, ev (n + m) → ev n → ev m := by
  intro n m Hnm Hn
  induction Hn with
  | ev_0 =>
    simp at Hnm
    exact Hnm
  | ev_SS n' E' IH =>
    -- We have ev (n' + 2 + m) and need to show ev m
    -- We can use IH : ev (n' + m) → ev m
    apply IH
    -- Now we need to show ev (n' + m) from ev (n' + 2 + m)
    have h : n' + 2 + m = (n' + m) + 2 := by
      rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
    rw [h] at Hnm
    apply evSS_ev
    exact Hnm

/-!
### Exercise: 3 stars, standard, especially useful (ev_plus_plus)

This exercise can be completed without induction or case analysis. But the proof is somewhat tricky.
-/

theorem ev_plus_plus : ∀ n m p, ev (n + m) → ev (n + p) → ev (m + p) := by
  intro n m p Hnm Hnp
  -- We'll use the fact that ev (n + m) and ev (n + p) implies ev ((n + m) + (n + p))
  -- which equals ev (2*n + m + p), and since ev (2*n), we get ev (m + p)
  have h1 : ev ((n + m) + (n + p)) := ev_sum (n + m) (n + p) Hnm Hnp
  have h2 : (n + m) + (n + p) = (n + n) + (m + p) := by
    rw [← Nat.add_assoc, Nat.add_assoc n m n, Nat.add_comm m n, ← Nat.add_assoc, Nat.add_assoc]
  rw [h2] at h1
  have h3 : ev (n + n) := by
    rw [← Nat.two_mul]
    apply ev_double
  apply ev_ev__ev (n + n) (m + p) h1 h3
