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

To formalize this question in Lean, we might try to define a recursive function that
calculates the total number of steps that it takes for such a sequence to reach `1`.

```lean
-- This would be rejected by Lean's termination checker
def reaches1_in (n : Nat) : Nat :=
  if n = 1 then 0
  else 1 + reaches1_in (csf n)
```

You can write this definition in a standard programming language. This definition is,
however, rejected by Lean's termination checker, since the argument to the recursive call,
`csf n`, is not "obviously smaller" than `n`.

Indeed, this isn't just a pointless limitation: functions in Lean are required to be total,
to ensure logical consistency.

Moreover, we can't fix it by devising a more clever termination checker: deciding whether
this particular function is total would be equivalent to settling the Collatz conjecture!

Fortunately, there is another way to do it: We can express the concept "reaches 1 eventually
in the Collatz sequence" as an **inductively defined property** of numbers. Intuitively,
this property is defined by a set of rules:

```
                                    (Chf_one)
                              Collatz_holds_for 1

    n % 2 = 0      Collatz_holds_for (div2 n)     (Chf_even)
    ──────────────────────────────────────────
              Collatz_holds_for n

    n % 2 ≠ 0    Collatz_holds_for ((3 * n) + 1)   (Chf_odd)
    ────────────────────────────────────────────
              Collatz_holds_for n
```

So there are three ways to prove that a number `n` eventually reaches `1` in the Collatz sequence:
1. `n` is `1`;
2. `n` is even and `div2 n` reaches `1`;
3. `n` is odd and `(3 * n) + 1` reaches `1`.

We can prove that a number reaches `1` by constructing a (finite) derivation using these rules.

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
What we've done here is to use Lean's `inductive` definition mechanism to characterize
the property "Collatz holds for..." by stating three different ways in which it can hold:
(1) Collatz holds for `1`, (2) if Collatz holds for `div2 n` and `n` is even then Collatz
holds for `n`, and (3) if Collatz holds for `(3 * n) + 1` and `n` is odd then Collatz
holds for `n`. This Lean definition directly corresponds to the three rules we wrote
informally above.

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
      · simp [csf]
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
The Collatz conjecture then states that the sequence beginning from any positive number reaches `1`:
-/

-- conjecture collatz : ∀ n, n ≠ 0 → Collatz_holds_for n

/-!
If you succeed in proving this conjecture, you've got a bright future as a number theorist!
But don't spend too long on it -- it's been open since 1937.

## Example: Binary relation for comparing numbers

A binary relation on a set `X` has Lean type `X → X → Prop`. This is a family of propositions
parameterized by two elements of `X` -- i.e., a proposition about pairs of elements of `X`.

For example, one familiar binary relation on `Nat` is `LE : Nat → Nat → Prop`, the
less-than-or-equal-to relation, which can be inductively defined by the following two rules:

```
                (le_refl)
                 n ≤ n

    n ≤ m       (le_step)
    ─────────
    n ≤ m + 1
```

These rules say that there are two ways to show that a number is less than or equal to another:
either observe that they are the same number, or, if the second has the form `m + 1`,
give evidence that the first is less than or equal to `m`.

This corresponds to the following inductive definition in Lean:
-/

inductive le : Nat → Nat → Prop where
  | le_refl (n : Nat) : le n n
  | le_step (n m : Nat) : le n m → le n (m + 1)

-- We can use infix notation for our relation
infix:50 " ≤' " => le

/-!
This definition is a bit simpler and more elegant than the Boolean function `Nat.ble` we
might define. As usual, `le` and a boolean version would be equivalent.

Let's prove some examples:
-/

example : 3 ≤' 5 := by
  apply le.le_step
  apply le.le_step
  apply le.le_refl

/-!
## Example: Transitive Closure

As another example, the **transitive closure** of a relation `R` is the smallest relation
that contains `R` and that is transitive. This can be defined by the following two rules:

```
    R x y        (t_step)
    ─────────
    clos_trans R x y

    clos_trans R x y    clos_trans R y z    (t_trans)
    ───────────────────────────────────────
              clos_trans R x z
```

In Lean this looks as follows:
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
In this example, Sage is a parent of both Cleo and Ridley; and Cleo is a parent of Moss.

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
## Example: Reflexive and Transitive Closure

As another example, the **reflexive and transitive closure** of a relation `R` is the smallest
relation that contains `R` and that is reflexive and transitive. This can be defined by the
following three rules (where we added a reflexivity rule to `clos_trans`):

```
    R x y        (rt_step)
    ─────────
    clos_refl_trans R x y

                 (rt_refl)
    clos_refl_trans R x x

    clos_refl_trans R x y    clos_refl_trans R y z    (rt_trans)
    ─────────────────────────────────────────────────
              clos_refl_trans R x z
```
-/

inductive clos_refl_trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) :
      R x y →
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y →
      clos_refl_trans R y z →
      clos_refl_trans R x z

/-!
For instance, this enables an equivalent definition of the Collatz conjecture. First we define
the binary relation corresponding to the Collatz step function `csf`:
-/

def cs (n m : Nat) : Prop := csf n = m

/-!
This Collatz step relation can be used in conjunction with the reflexive and transitive closure
operation to define a Collatz multi-step (`cms`) relation, expressing that a number `n` reaches
another number `m` in zero or more Collatz steps:
-/

def cms (n m : Nat) : Prop := clos_refl_trans cs n m

-- conjecture collatz' : ∀ n, n ≠ 0 → cms n 1

/-!
### Exercise: 1 star, standard, optional (clos_refl_trans_sym)

How would you modify the `clos_refl_trans` definition above so as to define the reflexive,
symmetric, and transitive closure?
-/

-- Exercise: Define the reflexive, symmetric, and transitive closure
inductive clos_refl_sym_trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rst_step (x y : X) : R x y → clos_refl_sym_trans R x y
  | rst_refl (x : X) : clos_refl_sym_trans R x x
  | rst_sym (x y : X) : clos_refl_sym_trans R x y → clos_refl_sym_trans R y x
  | rst_trans (x y z : X) : clos_refl_sym_trans R x y → clos_refl_sym_trans R y z → clos_refl_sym_trans R x z

/-!
## Example: Permutations

The familiar mathematical concept of permutation also has an elegant formulation as an inductive relation.
For simplicity, let's focus on permutations of lists with exactly three elements. We can define them
by the following rules:

```
                        (perm3_swap12)
    Perm3 [a;b;c] [b;a;c]

                        (perm3_swap23)
    Perm3 [a;b;c] [a;c;b]

    Perm3 l1 l2       Perm3 l2 l3    (perm3_trans)
    ───────────────────────────────
           Perm3 l1 l3
```

This definition says:
1. If `l2` can be obtained from `l1` by swapping the first and second elements, then `l2` is a permutation of `l1`.
2. If `l2` can be obtained from `l1` by swapping the second and third elements, then `l2` is a permutation of `l1`.
3. If `l2` is a permutation of `l1` and `l3` is a permutation of `l2`, then `l3` is a permutation of `l1`.

In Lean `Perm3` is given the following inductive definition:
-/

inductive Perm3 {X : Type} : List X → List X → Prop where
  | perm3_swap12 (a b c : X) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l1 l2 l3 : List X) :
      Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3

/-!
### Exercise: 1 star, standard, optional (perm)

According to this definition, is `[1;2;3]` a permutation of itself?

**Answer**: Yes, `[1;2;3]` is a permutation of itself. We can prove this using transitivity:
`[1;2;3]` → `[2;1;3]` (by swap12) → `[1;2;3]` (by swap12 again).
-/

-- We can prove reflexivity for Perm3
example : Perm3 [1, 2, 3] [1, 2, 3] := by
  apply Perm3.perm3_trans (l2 := [2, 1, 3])
  · apply Perm3.perm3_swap12
  · apply Perm3.perm3_swap12

/-!
## Example: Evenness (yet again)

We've already seen two ways of stating a proposition that a number `n` is even: We can say
1. `n % 2 = 0` (using the modulo operation), or
2. `∃ k, n = 2 * k` (using an existential quantifier).

A third possibility, which we'll use as a simple running example here, is to say that a number
is even if we can establish its evenness from the following two rules:

```
        (ev_0)
        ev 0

    ev n    (ev_SS)
    ────────
    ev (n + 2)
```

Intuitively these rules say that:
- The number `0` is even.
- If `n` is even, then `n + 2` is even.

We can translate the informal definition of evenness from above into a formal inductive declaration,
where each "way that a number can be even" corresponds to a separate constructor:
-/

inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat) (H : ev n) : ev (n + 2)

/-!
Such definitions are interestingly different from previous uses of `inductive` for defining
inductive datatypes like `Nat` or `List`. For one thing, we are defining not a `Type` (like `Nat`)
or a function yielding a `Type` (like `List`), but rather a function from `Nat` to `Prop` --
that is, a property of numbers. But what is really new is that, because the `Nat` argument of
`ev` appears to the right of the colon on the first line, it is allowed to take different values
in the types of different constructors: `0` in the type of `ev_0` and `n + 2` in the type of `ev_SS`.
Accordingly, the type of each constructor must be specified explicitly (after a colon), and each
constructor's type must have the form `ev n` for some natural number `n`.

Beyond this syntactic distinction, we can think of the inductive definition of `ev` as defining
a Lean property `ev : Nat → Prop`, together with two "evidence constructors":
-/

#check ev.ev_0
#check ev.ev_SS

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
## Constructing Evidence for Permutations

Similarly we can apply the evidence constructors to obtain evidence of `Perm3 [1;2;3] [3;2;1]`:
-/

-- lemma Perm3_rev : Perm3 [1, 2, 3] [3, 2, 1] := by
--   apply Perm3.perm3_trans (l2 := [2, 3, 1])
--   · apply Perm3.perm3_trans (l2 := [2, 1, 3])
--     · apply Perm3.perm3_swap12
--     · apply Perm3.perm3_swap23
--   · apply Perm3.perm3_swap12

/-!
### Exercise: 1 star, standard (Perm3)
-/

-- lemma Perm3_ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
--   apply Perm3.perm3_trans (l2 := [2, 1, 3])
--   · apply Perm3.perm3_swap12
--   · apply Perm3.perm3_swap23

-- lemma Perm3_refl : ∀ (X : Type) (a b c : X), Perm3 [a, b, c] [a, b, c] := by
--   intro X a b c
--   apply Perm3.perm3_trans (l2 := [b, a, c])
--   · apply Perm3.perm3_swap12
--   · apply Perm3.perm3_swap12

/-!
## Using Evidence in Proofs

Besides constructing evidence that numbers are even, we can also destruct such evidence,
reasoning about how it could have been built.

Defining `ev` with an inductive declaration tells Lean not only that the constructors `ev_0`
and `ev_SS` are valid ways to build evidence that some number is `ev`, but also that these
two constructors are the **only** ways to build evidence that numbers are `ev`.

In other words, if someone gives us evidence `E` for the proposition `ev n`, then we know
that `E` must be one of two things:
- `E = ev_0` and `n = 0`, or
- `E = ev_SS n' E'`, where `n = n' + 2` and `E'` is evidence for `ev n'`.

This suggests that it should be possible to analyze a hypothesis of the form `ev n` much as
we do inductively defined data structures; in particular, it should be possible to argue by
case analysis or by induction on such evidence. Let's look at a few examples to see what this
means in practice.

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
Facts like this are often called "inversion lemmas" because they allow us to "invert" some
given information to reason about all the different ways it could have been derived. Here,
there are two ways to prove `ev n`, and the inversion lemma makes this explicit.

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
Note how the inversion lemma produces two subgoals, which correspond to the two ways of proving `ev`.
The first subgoal is a contradiction that is discharged with `simp`. The second subgoal makes use
of the fact that `n + 2 = n' + 2` implies `n = n'`.

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

Let's try proving that lemma again:
-/

-- lemma ev_Even : ∀ n, ev n → Even n := by
--   intro n E
--   induction E with
--   | ev_0 =>
--     -- E = ev_0
--     exists 0
--     rfl
--   | ev_SS n' E' IH =>
--     -- E = ev_SS n' E', with IH : Even n'
--     obtain ⟨k, Hk⟩ := IH
--     rw [Hk]
--     exists k + 1
--     simp [Nat.mul_add, Nat.add_mul]

/-!
Here, we can see that Lean produced an `IH` that corresponds to `E'`, the single recursive
occurrence of `ev` in its own definition. Since `E'` mentions `n'`, the induction hypothesis
talks about `n'`, as opposed to `n` or some other number.

The equivalence between the second and third definitions of evenness now follows.
-/

-- theorem ev_Even_iff : ∀ n, ev n ↔ Even n := by
--   intro n
--   constructor
--   · -- ->
--     apply ev_Even
--   · -- <-
--     intro ⟨k, Hk⟩
--     rw [Hk]
--     apply ev_double

/-!
As we will see in later chapters, induction on evidence is a recurring technique across many
areas -- in particular for formalizing the semantics of programming languages.

The following exercises provide simpler examples of this technique, to help you familiarize
yourself with it.

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
    rw [Nat.add_assoc n' 2 m]
    rw [Nat.add_comm 2 m]
    rw [← Nat.add_assoc]
    apply ev.ev_SS
    exact IH
