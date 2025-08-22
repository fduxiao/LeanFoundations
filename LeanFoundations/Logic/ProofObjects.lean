/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Proof Objects" chapter from
Software Foundations (Logical Foundations).
-/

import LeanFoundations.Logic.IndProp

/-!
# Proof Objects

> "Algorithms are the computational content of proofs." —Robert Harper

We have seen that Lean has mechanisms both for *programming*, using inductive and recursive
definitions, and for *proving*, using inductive types, recursive functions, tactics, etc.
So far, we have mostly treated these mechanisms as if they were quite separate, and for many
purposes this is a good way to think. But we have also seen hints that Lean's programming and
proving facilities are closely related. For example, the keyword `inductive` is used to declare
both datatypes and propositions, and `→` is used both to describe the type of functions on data
and logical implication. This is not just a syntactic accident! In fact, programs and proofs
in Lean are almost the same thing. In this chapter, we will study this connection more closely.

We have already seen the fundamental idea: provability in Lean is represented by concrete
*evidence*. When we construct a proof of a basic proposition, we are actually building a tree
of evidence, where each node in the tree is an instance of an inference rule, and the children
of each node are the subproofs of the premises of that rule. If the premise is an assumption,
then the corresponding leaf in the evidence tree is the assumption's label.

For example, consider the following simple proof:
-/

example (n : Nat) : n = n := by rfl

/-!
This proof can also be written as:
-/

example (n : Nat) : n = n := Eq.refl n

/-!
In the second version, we have explicitly provided the *proof object* `Eq.refl n` of type `n = n`.

## Proof Scripts vs. Proof Objects

We have been writing proof *scripts*, i.e., sequences of tactics that instruct Lean how to build
up a proof object behind the scenes. Alternatively, we can write out this proof object directly,
without tactics:
-/

theorem plus_1_neq_0_firsttry : ∀ n : Nat, n + 1 ≠ 0 := by
  intro n
  intro H
  cases H

/-!
This is the same as:
-/

theorem plus_1_neq_0_secondtry : ∀ n : Nat, n + 1 ≠ 0 :=
  fun n => fun H => Nat.noConfusion H

/-!
Or even:
-/

theorem plus_1_neq_0_thirdtry : ∀ n : Nat, n + 1 ≠ 0 :=
  fun n H => Nat.noConfusion H

/-!
You can see that proof scripts and proof objects serve the same purpose — they carry out the
construction of evidence for the truth of propositions. Proof scripts are easier to work with
because they give us the power of *tactics*. But proof objects are often more illuminating,
because they make explicit the logical structure of the proof.

## Quantifiers, Implications, Functions

In Lean's computational universe (where data structures and programs live), there are two sorts
of values with arrows in their types: *constructors* introduced by `inductive`ly defined data
types, and *functions*.

Similarly, in Lean's logical universe (where we carry out proofs), there are two ways of giving
evidence for an implication: constructors introduced by `inductive`ly defined propositions,
and... functions!

For example, consider this statement:
-/

#check (∀ n m : Nat, n + m = m + n)

/-!
In principle, we could prove this by providing evidence for each possible pair of naturals,
but this would be impossible to finish — there are infinitely many pairs!

The universal quantifier `∀` (and implication `→`, which is just a special case) is built into
Lean's logic in a fundamental way: what we mean when we say "∀ n : Nat, P n" is that we can
supply a proof of `P n` for any specific choice of `n`. In other words, a proof of `∀ n : Nat, P n`
is a *function* that takes any natural number `n` and returns a proof of `P n`.

In the above statement, for example, `n` and `m` are bound by universal quantifiers, so a proof
would be a function that takes two natural numbers and returns evidence for the corresponding
instance of the equality `n + m = m + n`.
-/

theorem plus_comm : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction n with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n' ih => rw [Nat.succ_add, Nat.add_succ, ih]

/-!
The same proof can be written directly as a function:
-/

theorem plus_comm' : ∀ n m : Nat, n + m = m + n :=
  fun n m => by
    induction n with
    | zero => rw [Nat.zero_add, Nat.add_zero]
    | succ n' ih => rw [Nat.succ_add, Nat.add_succ, ih]

/-!
In general, `P → Q` is just syntactic sugar for `∀ (_ : P), Q`. That is, they mean the same thing:
both describe functions that take evidence for `P` and produce evidence for `Q`.

For example:
-/

theorem plus_1_neq_0 : ∀ n : Nat, n + 1 ≠ 0 :=
  fun n H => Nat.noConfusion H

theorem plus_1_neq_0' (n : Nat) : n + 1 ≠ 0 :=
  fun H => Nat.noConfusion H

/-!
Both have the same meaning: they are functions that take a natural number `n` and a hypothesis
`H` stating that `n + 1 = 0`, and return a proof of `False` (since `n + 1` is never `0`).

## Programming with Tactics vs. Defining Functions

If the idea of "proof objects" is unfamiliar, let me point out that we use proof objects all
the time in informal mathematics. For example, here is a textbook proof that addition is
associative:

*Theorem*: Addition is associative.
*Proof*: By induction on `n`.
- Case `n = 0`: We must show that `0 + (m + p) = (0 + m) + p`. This follows directly from
  the definition of addition.
- Case `n = S n'` where `0 + (m + p) = (0 + m) + p` (this is the induction hypothesis):
  We must show that `(S n') + (m + p) = ((S n') + m) + p`. By the definition of addition,
  this follows from `S (n' + (m + p)) = S ((n' + m) + p)`, which is immediate from the
  induction hypothesis.  ∎

This is essentially the same as the following proof object:
-/

theorem plus_assoc : ∀ n m p : Nat, n + (m + p) = (n + m) + p := by
  intro n m p
  exact (Nat.add_assoc n m p).symm

/-!
Or more directly:
-/

theorem plus_assoc' : ∀ n m p : Nat, n + (m + p) = (n + m) + p :=
  fun n m p => (Nat.add_assoc n m p).symm

/-!
## Logical Connectives as Inductive Types

Inductive definitions are powerful enough to express most of the logical connectives we have
seen so far. Indeed, only universal quantification (with implication as a special case) is
built into Lean; all the others — conjunction, disjunction, negation, existential quantification,
even equality — can be encoded using inductive definitions. Let's see how.

### Conjunction

To prove that `P ∧ Q` holds, we must present evidence for both `P` and `Q`. Thus, it makes
sense to define a proof object for `P ∧ Q` as consisting of a pair of two proofs: one for `P`
and another for `Q`. This leads to the following definition.
-/

namespace MyLogic

inductive And (A B : Prop) : Prop where
  | intro (a : A) (b : B) : And A B

/-!
Notice the similarity with the definition of the `prod` type, given in chapter `Poly`; the only
difference is that `prod` takes `Type` arguments, whereas `And` takes `Prop` arguments.
-/

#print And.intro
#check @And.intro

/-!
This explains the `constructor` tactic: to prove a goal that is a conjunction, apply the single
constructor of the `And` inductive family.

### Exercise: 1 star, standard, optional (proj1)

Here's a theorem that says: if `P ∧ Q` is true, then `P` is true.
-/

theorem proj1 : ∀ P Q : Prop, And P Q → P := by
  intro P Q H
  cases H with
  | intro hp hq => exact hp

/-!
### Exercise: 1 star, standard, optional (proj2)

Similarly, here's a theorem that says: if `P ∧ Q` is true, then `Q` is true.
-/

theorem proj2 : ∀ P Q : Prop, And P Q → Q := by
  intro P Q H
  cases H with
  | intro hp hq => exact hq

/-!
### Exercise: 1 star, standard, optional (and_comm)

Theorem: `P ∧ Q` implies `Q ∧ P`.
-/

theorem and_comm : ∀ P Q : Prop, And P Q → And Q P := by
  intro P Q H
  cases H with
  | intro hp hq => exact And.intro hq hp

/-!
This shows why the `cases` tactic can be used to reason about conjunction: it is defined as
an inductive type with one constructor, and `cases` simply applies the inverse of the constructor.

### Disjunction

The inductive definition of disjunction uses two constructors, one for each side of the disjunct:
-/

inductive Or (A B : Prop) : Prop where
  | inl (a : A) : Or A B
  | inr (b : B) : Or A B

/-!
This explains the behavior of the `left` and `right` tactics: they are simply applications of
the first and second constructors of `Or`. It also explains the behavior of the `cases` tactic
on a disjunctive hypothesis, since the inversion of the constructors generates two subgoals.

### Exercise: 1 star, standard, optional (or_comm)

Theorem: `P ∨ Q` implies `Q ∨ P`.
-/

theorem or_comm : ∀ P Q : Prop, Or P Q → Or Q P := by
  intro P Q H
  cases H with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

/-!
### Existential Quantification

To give evidence for an existential quantifier, we package a *witness* together with a *proof*
that the witness satisfies the property in question.
-/

inductive Ex {A : Type} (P : A → Prop) : Prop where
  | intro (witness : A) (proof : P witness) : Ex P

/-!
This may benefit from a little unpacking. The core definition is for a type former `Ex` that can
be used to build propositions of the form `Ex P`, where `P` itself is a *function* from witness
values in the type `A` to propositions. The `Ex.intro` constructor then offers a way of
constructing evidence for `Ex P`, given a witness value and a proof that the witness satisfies
the property `P`.

The more familiar form `∃ x, P x` desugars to an expression involving `Ex`:
-/

#check (∃ n : Nat, n + n = 4)
#check (Ex (fun n : Nat => n + n = 4))

/-!
Here's how to define the familiar introduction construct for existentials:
-/

theorem some_nat_is_even : ∃ n : Nat, n + n = 4 :=
  ⟨2, rfl⟩

/-!
### Exercise: 1 star, standard, optional (ex_ev_Sn)

Complete the definition of the following proof object:
-/

theorem ex_ev_Sn : ∃ n : Nat, ev (n + 1) := by
  sorry

/-!
### True and False

The inductive definition of the `True` proposition is simple: it is defined as an inductive
type with a single constructor.
-/

inductive True : Prop where
  | intro : True

/-!
It has one constructor (so every proof of `True` is the same, so being given a proof of `True`
is not informative.)

`False` is equally simple — indeed, so simple it may look syntactically wrong at first glance!
-/

inductive False : Prop where

/-!
That is, `False` is an inductive type with *no* constructors — i.e., no way to build evidence
for it.

### Exercise: 1 star, standard, optional (False_ind)

How does the `exfalso` tactic work? It applies the following theorem:
-/

theorem False_ind : ∀ P : Prop, False → P := by
  intro P H
  cases H

/-!
### Equality

Even Lean's equality relation is not built in. It has the following inductive definition.
(Actually, the definition in the Lean standard library is a bit different for technical reasons,
but this is equivalent.)
-/

inductive Eq' {A : Type} (x : A) : A → Prop where
  | refl : Eq' x x

/-!
The way to think about this definition is that, given a set `A`, it defines a *family* of
propositions "`x` is equal to `y`," indexed by pairs of values (`x` and `y`) from `A`. There
is just one way to construct evidence for members of this family: applying the constructor
`refl` to show that every value is equal to itself.

### Exercise: 2 stars, standard, optional (equality__leibniz_equality)

The inductive definition of equality corresponds to *Leibniz equality*: what we mean when we
say "`x` and `y` are equal" is that every property on one side of the equation also holds on
the other side. This is captured by the following theorem:
-/

theorem equality__leibniz_equality : ∀ (X : Type) (x y : X),
  Eq' x y → ∀ P : X → Prop, P x → P y := by
  intro X x y H P Hx
  cases H
  exact Hx

/-!
### Exercise: 2 stars, standard, optional (leibniz_equality__equality)

Show that, in fact, the converse is true:
-/

theorem leibniz_equality__equality : ∀ (X : Type) (x y : X),
  (∀ P : X → Prop, P x → P y) → Eq' x y := by
  intro X x y H
  apply H
  apply Eq'.refl

end MyLogic

/-!
## Inversion, Again

We've seen that tactics like `cases` and `induction` can be applied to evidence for inductively
defined propositions, not just to evidence for inductively defined data. This should make sense,
since both are defined using `inductive`.

The way `cases` works is to identify each constructor that could have been used to build the
evidence and generate a subgoal in which we assume that the evidence was built with that
constructor.

### Exercise: 3 stars, standard (ev_plus_plus)

Here's an exercise that just requires applying existing lemmas. No induction or case analysis
is needed, but some of the rewriting may be tedious.
-/

theorem ev_plus_plus_simple : ∀ n m p, ev (n + m) → ev (n + p) → ev (m + p) := by
  sorry

/-!
## Computational vs. Propositional Types

We have seen that Lean expressions can have types like `Nat`, which classify *computational*
objects, and `Nat → Nat → Nat`, which describe *functions* for computing new objects from old
ones, and `Prop`, which classifies *logical propositions*, and `Nat → Prop`, which describes
*properties* of computational objects.

*Computational types* classify computational objects with the following fundamental property:
there is an effective procedure (an algorithm) to check whether any two objects of the type
are equal or not.

*Propositional types* classify logical propositions, which may or may not be provable. Unlike
computational objects, propositions are not amenable to computation in general. We cannot
simply run an algorithm to check whether a proposition is true or not — this is what proofs
are for.

Many computational types are also inhabited by elements with computational content — e.g.,
the type `Nat` is inhabited by `0`, `1`, `2`, etc. Some propositions are also inhabited by
proofs — e.g., `2 + 2 = 4` is inhabited by `rfl : 2 + 2 = 4`. But some propositions, like
`2 + 2 = 5`, are not inhabited by any proofs.

### Exercise: 2 stars, standard, optional (bogus_subgoal)

Normally, we can use `cases` on the evidence for any inductively defined proposition. This
includes properties like `ev`, `beautiful`, etc., and also properties like `eq` and `False`.
The reason this works is that `cases` can be used to reason about *evidence* for these
properties, not the properties themselves.

However, there is an important exception: for some properties, like `True`, there is no
interesting evidence. In such cases, `cases` still works, but it doesn't generate any
subgoals. Try this to see what happens:
-/

theorem bogus_subgoal : True → False := by
  intro H
  cases H
  -- No subgoals generated!
  sorry

/-!
### Exercise: 1 star, standard, optional (b_times2)

Prove that `b * 2` is even for any `b`.
-/

theorem b_times2 : ∀ b : Nat, ev (b * 2) := by
  intro b
  rw [Nat.mul_comm]
  apply ev_double

/-!
## Additional Exercises

### Exercise: 2 stars, standard, optional (ev_plus_one)

This exercise explores how hypotheses work in Lean.
-/

theorem ev_plus_one : ∀ n, ev (n + 1) → False := by
  intro n H
  cases H with
  | ev_SS n' H' =>
    -- We have ev (n' + 2), but n + 1 = n' + 2 means n = n' + 1
    -- This leads to a contradiction since n + 1 cannot be even
    sorry
