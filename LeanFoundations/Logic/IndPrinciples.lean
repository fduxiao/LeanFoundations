/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Induction Principles" chapter from
Software Foundations (Logical Foundations).
-/

import LeanFoundations.Logic.ProofObjects

/-!
# Induction Principles

With the Curry-Howard correspondence and its realization in Lean in mind, we can now take a
deeper look at induction principles.

## Basics

Every time we declare a new `inductive` datatype, Lean automatically generates an *induction
principle* for this type. The induction principle for a type `t` is called `t.rec`.

To get a better understanding of induction principles, let's look at the one for natural numbers:
-/

#check Nat.rec

/-!
This is a bit hard to parse at first. Let's look at it more carefully:

```lean
Nat.rec : ∀ {motive : Nat → Sort u_1},
  motive 0 →
  (∀ (n : Nat), motive n → motive n.succ) →
  ∀ (t : Nat), motive t
```

This says: Suppose `motive` is a property of natural numbers (i.e., `motive : Nat → Sort u_1`).
To prove that `motive n` holds for all `n`, it suffices to prove:
- `motive 0` (the base case)
- `∀ n, motive n → motive (n + 1)` (the inductive step)

Each of these is the same as the familiar induction principle for naturals that we introduced
informally in the Basics chapter. The only difference is that we're thinking about it more
formally here.

The induction tactic is a straightforward wrapper that, at its core, simply performs `apply t.rec`.

To see this more clearly, let's experiment with using `apply Nat.rec` directly, instead of the
`induction` tactic, to carry out some proofs.
-/

theorem mult_0_r' : ∀ n : Nat, n * 0 = 0 := by
  apply Nat.rec
  · -- Base case: 0 * 0 = 0
    rfl
  · -- Inductive step: ∀ n, n * 0 = 0 → (n + 1) * 0 = 0
    intro n ih
    rw [Nat.succ_mul, ih, Nat.add_zero]

/-!
This `apply` tactic has generated three subgoals:
1. The motive (which Lean figured out from the goal)
2. The base case
3. The inductive step

Compare this with the proof using the `induction` tactic:
-/

theorem mult_0_r'' : ∀ n : Nat, n * 0 = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => rw [Nat.succ_mul, ih, Nat.add_zero]

/-!
## More on the `induction` Tactic

The `induction` tactic is a wrapper around the more basic `apply t.rec`. In addition to
applying the induction principle, it also:

1. Introduces the argument being inducted over into the context
2. Introduces the induction hypotheses into the context with user-chosen names
3. Performs some low-level bookkeeping that makes the proof state easier to work with

### Exercise: 2 stars, standard (plus_assoc_rec)

For example, here's a proof of associativity using `apply Nat.rec`:
-/

theorem plus_assoc_rec : ∀ n m p : Nat, n + (m + p) = (n + m) + p := by
  sorry

/-!
## Induction Principles in `Prop`

Earlier, we looked in detail at the induction principles that Lean generates for inductively
defined *sets*, like `Nat`, `List`, etc. The induction principles for inductively defined
*propositions* like `ev`, `le`, etc. are a bit more subtle. As an example, let's look at the
induction principle for `ev`:
-/

#check ev.rec

/-!
This is saying: Suppose we have some property `motive` of pairs `(n, E)` where `n` is a number
and `E` is evidence that `n` is even. To prove that `motive (n, E)` holds for all such pairs,
it suffices to prove:
- `motive (0, ev_0)`
- For all `n` and evidence `E` that `n` is even, if `motive (n, E)` holds, then
  `motive (n + 2, ev_SS n E)` holds.

This is more flexible than our previous induction principle for `Nat` because it lets us
perform induction not just on `n` (saying "for all `n`") but on the *evidence* that `n` is even.
This leads to a different induction hypothesis: instead of "assuming `P(n)` and trying to prove
`P(n+1)`", we're "assuming `P(n, E)` for evidence `E` of `ev n`, and trying to prove
`P(n+2, ev_SS n E)`".

To prove theorems by induction on evidence, we can use either the `induction` tactic (which
will invoke `ev.rec` under the hood) or apply `ev.rec` directly.

### Exercise: 2 stars, standard (ev_ev_plus_4)

As an example, here's the proof that `ev n → ev (n + 4)` for any `n`:
-/

theorem ev_ev_plus_4 : ∀ n, ev n → ev (n + 4) := by
  sorry

/-!
## More on Induction over Evidence

Let's look at some more examples of induction over evidence. Here's a proof that if `n` is even,
then so is `n - 2`:
-/

theorem ev_minus2 : ∀ n, ev n → ev (n - 2) := by
  intro n E
  induction E with
  | ev_0 =>
    -- n = 0, so n - 2 = 0 - 2 = 0 (by truncated subtraction)
    simp
    apply ev.ev_0
  | ev_SS n' E' ih =>
    -- n = n' + 2, so n - 2 = (n' + 2) - 2 = n'
    -- We have E' : ev n', which is exactly what we need
    simp [Nat.add_sub_cancel]
    exact E'

/-!
### Exercise: 1 star, standard, optional (ev_minus2_n)

Prove the following theorem:
-/

theorem ev_minus2_n : ∀ n, ev n → ∃ k, n = k + k := by
  sorry

/-!
## Induction Principles for Other Datatypes

Similar induction principles are generated for every datatype defined with `inductive`.
For lists, the induction principle is:

```lean
List.rec : ∀ {α : Type u_1} {motive : List α → Sort u_2},
  motive [] →
  (∀ (head : α) (tail : List α), motive tail → motive (head :: tail)) →
  ∀ (t : List α), motive t
```

### Exercise: 1 star, standard, optional (list_induction)

Prove the following theorem using `apply List.rec` instead of `induction`:
-/

theorem app_assoc : ∀ (X : Type) (l1 l2 l3 : List X),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3 := by
  sorry

/-!
### Exercise: 2 stars, standard, optional (tree_induction)

Let's define a simple binary tree datatype and prove a theorem about it using its induction principle:
-/

inductive Tree (X : Type) : Type where
  | leaf : Tree X
  | node : X → Tree X → Tree X → Tree X

/-!
The induction principle for `Tree` is:
-/

#check Tree.rec

/-!
Now let's define a function that counts the number of leaves in a tree:
-/

def count_leaves {X : Type} : Tree X → Nat
  | Tree.leaf => 1
  | Tree.node _ left right => count_leaves left + count_leaves right

/-!
And prove that every tree has at least one leaf:
-/

theorem tree_has_leaf : ∀ (X : Type) (t : Tree X), count_leaves t ≥ 1 := by
  intro X t
  induction t with
  | leaf =>
    simp [count_leaves]
  | node x left right ih_left ih_right =>
    simp [count_leaves]
    omega

/-!
## Induction Principles for Propositions

Induction principles for inductively defined propositions like `ev` are a bit different from
those for datatypes like `Nat`. The most important difference is that the first argument to
`motive` is not just a `Nat`, but a pair of a `Nat` (call it `n`) and evidence that `n` is even.
This reflects the fact that the induction is happening over *evidence* for the proposition `ev n`,
not just over `n` itself.

This difference is important. It means that when we do induction on evidence `E : ev n`, we get
to assume not just that the property holds for smaller numbers, but that it holds for smaller
*evidence* of evenness.

### Exercise: 2 stars, standard (ev_sum)

Here's another example where induction on evidence is useful:
-/

theorem ev_sum_again : ∀ n m, ev n → ev m → ev (n + m) := by
  intro n m En Em
  induction En with
  | ev_0 =>
    simp
    exact Em
  | ev_SS n' En' ih =>
    rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
    apply ev.ev_SS
    exact ih

/-!
## Induction Principles for Other Logical Propositions

Similarly, we can write down induction principles for other inductively defined propositions.
For example, here's the induction principle for `le`:
-/

#check le.rec

/-!
### Exercise: 2 stars, standard, optional (le_trans)

Give an alternative proof of `le_trans` that uses induction on evidence that `m ≤ n` instead
of induction on `n`.
-/

theorem le_trans : ∀ n m o, n ≤' m → m ≤' o → n ≤' o := by
  intro n m o Hnm Hmo
  induction Hmo with
  | le_refl => exact Hnm
  | le_step o' Hmo' ih =>
    apply le.le_step
    exact ih

/-!
## The Logic of Induction Principles

Induction principles are just theorems in Lean. There's nothing magical about them. We could
prove them ourselves if we wanted to (though Lean's automatic generation is much more convenient).

For example, here's a manual proof of the induction principle for `Nat`:
-/

theorem Nat_induction_principle :
  ∀ (P : Nat → Prop),
    P 0 →
    (∀ n, P n → P (n + 1)) →
    ∀ n, P n := by
  intro P H0 Hsucc n
  induction n with
  | zero => exact H0
  | succ n' ih => apply Hsucc; exact ih

/-!
This is essentially the same as `Nat.rec`, just written out explicitly.

### Exercise: 3 stars, advanced (ev_induction_principle_proof)

Can you prove the induction principle for `ev`? Try it:
-/

theorem ev_induction_principle :
  ∀ (P : Nat → Prop),
    P 0 →
    (∀ n, P n → P (n + 2)) →
    ∀ n, ev n → P n := by
  intro P H0 H2 n E
  induction E with
  | ev_0 => exact H0
  | ev_SS n' E' ih => apply H2; exact ih

/-!
### Exercise: 2 stars, standard (ev_sum_using_principle)

Use the alternative induction principle to prove `ev_sum`:
-/

theorem ev_sum_using_principle : ∀ n m, ev n → ev m → ev (n + m) := by
  intro n m En Em
  apply ev_induction_principle (P := fun k => ev (k + m))
  · -- Base case: ev (0 + m)
    simp
    exact Em
  · -- Inductive step: ∀ k, ev (k + m) → ev ((k + 2) + m)
    intro k ih
    rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
    apply ev.ev_SS
    exact ih
  · -- Apply to our specific n
    exact En

/-!
## Strengthening Induction Hypotheses

Sometimes, the obvious induction hypothesis is not strong enough. In such cases, we may need
to prove a more general statement.

### Exercise: 2 stars, standard (double_even)

Prove that `2 * n` is even for all `n`:
-/

theorem double_even : ∀ n, ev (2 * n) := by
  sorry

/-!
### Exercise: 3 stars, standard (induction_principles_exercises)

Try to prove the following theorems using induction on evidence:
-/

-- Exercise: Prove that if n is even, then n can be written as 2*k for some k
theorem ev_double_n : ∀ n, ev n → ∃ k, n = 2 * k := by
  sorry

/-!
## Additional Exercises

The following exercises explore various aspects of induction principles:

### Exercise: 2 stars, standard (custom_induction)

Define your own induction principle for a simple datatype and prove a theorem using it.
-/

-- Exercise: Define a simple datatype for binary numbers
inductive BinNum : Type where
  | zero : BinNum
  | twice : BinNum → BinNum
  | twicePlusOne : BinNum → BinNum

-- Exercise: Define a function to convert BinNum to Nat
def binToNat : BinNum → Nat
  | BinNum.zero => 0
  | BinNum.twice n => 2 * binToNat n
  | BinNum.twicePlusOne n => 2 * binToNat n + 1

-- Exercise: Prove that binToNat always returns a natural number (trivially true, but good practice)
theorem binToNat_is_nat : ∀ b : BinNum, binToNat b ≥ 0 := by
  intro b
  induction b with
  | zero => simp [binToNat]
  | twice b' ih => simp [binToNat]
  | twicePlusOne b' ih => simp [binToNat]

/-!
### Exercise: 3 stars, advanced (strong_induction)

Sometimes we need a stronger form of induction. Research and implement strong induction
(also called complete induction) for natural numbers.
-/

-- This is left as an advanced exercise for the reader
theorem strong_induction :
  ∀ (P : Nat → Prop),
    (∀ n, (∀ k, k < n → P k) → P n) →
    ∀ n, P n := by
  sorry
