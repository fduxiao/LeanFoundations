/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Inductively Defined Propositions"
chapter from Software Foundations (Logical Foundations).
-/

/-!
# Inductively Defined Propositions
In Lean, not only do we want to define some mathematical objects and write functions (algorithms) on
them, but also want to infer about them. This is to ask how to prove propositions and how to make
meaningful propositions. We have learned how to use logical connectives -- they are one reasonable
way to make meaningful propositions and we know how to prove/use them. But we have to ask, is there any
proposition not made from old propositions by connectives? Since we consider `True` and `False` as
_constant (nullary) connectives_, they are not such an _atomic_ proposition. If you are familiar with
first order logic, those _atomic_ propositions are made by _predicates_. In Lean, we also use predicates
to make those atomic propositions. For example, the equality `=` is one and up to now, it is
the only way that we can make an atomic proposition. We are going to learn how to define those
predicates with inductive types.
-/


/-!
## Propositions from Existing ones by Functions
In the tactic chapter, we learned that a predicate is simply a function whose codomain is `Prop`, which
means we can use functions to represent a predicate. Here, we use the evenness of a natural number as
an example. Recall how we define the evenness of a natural number. We have two reasonable ways to
express the evenness of a number. The first is the `beven` function
-/
def beven: Nat -> Bool
  | 0 => true
  | n + 1 => !(beven n)


def Even1 (n: Nat): Prop := beven n = true

/-!
The second is to use the existential quantifier.
-/
def Even2 (n: Nat): Prop := exists k, n = 2 * k


/-!
Of course, they should be equivalent. One direction is obvious
### Exercise: 2 stars, standard (even2_even1)
-/
theorem even2_even1 (n: Nat):
  Even2 n -> Even1 n
:= by
  unfold Even1 Even2
  rintro ⟨k, H⟩
  rewrite [H]
  -- We have to clear `H` here, or the inductive hypothesis will be too complicated.
  -- Delete it and observe the inductive hypothesis.
  clear H
  induction k  -- try this new syntax
  case zero =>
    rewrite [Nat.mul_zero]
    simp [beven]
  case succ k' IHk' =>
    -- change the goal in order to compute `beven`
    calc beven (2 * (k' + 1))
      _ = beven (2 * k' + 2) := by
        rewrite [Nat.mul_add]
        simp
    sorry


/-!
The other direction is not easy. You may still want to do induction on `n`.
```lean
theorem even1_even2 (n: Nat):
  Even1 n -> Even2 n
:= by
  unfold Even1 Even2
  intros H
  induction n
  case zero =>
    exists 0
  case succ n' IHn' =>
    simp [beven] at H
    admit
```
Here, we are facing the inductive hypothesis problem again. In the `succ` case, the hypothesis
`H` is the `beven (n' + 1) = true`, i.e., some `H: beven n' = False`. However the type of the
inductive hypothesis is `IHn' : beven n' = true → ∃ k, n' = 2 * k`. This means we cannot trigger
the inductive hypothesis.

What is the fix of this? Since the evenness changes at each step of `succ`, `beven n` also changes.
In order to use the inductive hypothesis, we have to prove a proposition both applying to
`beven n = true` and `beven n = false`. Thus, the correct proposition to prove is
`forall n: Nat, (beven n = true -> Even2 n) ∧ (beven n = false -> exists k, n + 1 = 2 * k)`.
-/


theorem even1_and_odd (n: Nat):
  (beven n = true -> Even2 n) ∧ (beven n = false -> exists k, n + 1 = 2 * k)
:= by
  unfold Even2
  induction n with
  | zero =>
    and_intros
    . intros
      exists 0
    . intro contra
      simp [beven] at contra
  | succ n' IHn' =>
    and_intros
    . intro H
      simp [beven] at H
      apply IHn'.right
      exact H
    . intro H
      simp [beven] at H
      -- also try those new tactics
      replace IHn' := IHn'.left
      specialize IHn' H
      obtain ⟨k, E⟩ := IHn'
      exists (k + 1)
      rewrite [E]
      calc 2 * k + 1 + 1


theorem even1_even2 (n: Nat):
  Even1 n -> Even2 n
:= by
  unfold Even1
  apply (even1_and_odd n).left


theorem even1_iff_even2 (n: Nat):
  Even1 n ↔ Even2 n
:= by
  apply Iff.intro
  . apply even1_even2
  . apply even2_even1


/-!
## Turn it into Recursion
Let's take a closer look at `Even1`, which just assigns a proposition to each `n: Nat`.
- When `n = 0`, we assign it `beven 0 = true`, which is `true = true`, i.e., `True`.
- When `n = 1`, we assign it `beven 1 = true`, which is `false = true`, i.e., `False`.
- When `n = 2`, we assign it `beven 2 = true`, which is `true = true`, i.e., `True`.
- When `n = 3`, we assign it `beven 3 = true`, which is `false = true`, i.e., `False`.
- ...

Similarly, `Even2` can be understood in the same way. We can look at the proposition assigned
to each `n: Nat`, and they are just `True` of `False`.

In other words, we recursively defined a function that
- maps `0` to `True`;
- maps `1` to `False`;
- maps `n + 2` to the value on `n`.
-/

def Even3: Nat -> Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even3 n

/-!
And of course, we can prove the same equivalence between them.
-/

theorem even2_even3 (n: Nat):
  Even2 n -> Even3 n
:= by
  unfold Even2
  rintro ⟨k, E⟩
  rewrite [E]
  clear E
  induction k with
  | zero =>
    simp [Even3]  -- True
  | succ n' IHn' =>
    rewrite [Nat.mul_add]
    simp [Even3]
    exact IHn'


/-!
The other direction is the same. We have to do the induction on two facts simultaneously.
-/
theorem even3_and_odd (n: Nat):
  (Even3 n -> Even2 n) ∧ (Even3 (n + 1) -> exists k, n + 1 = 2 * k)
:= by
  unfold Even2
  induction n with
  | zero =>
    and_intros
    . intros
      exists 0
    . intro contra
      simp [Even3] at contra
  | succ n' IHn' =>
    and_intros
    . intro H
      apply IHn'.right H
    . intro H
      simp [Even3] at H
      obtain ⟨k, E⟩ := IHn'.left H
      exists (k + 1)
      -- The rest is some arithmetic truth.
      omega


/-!
We have seen this technique twice. The basic idea is to do the induction both on `n` and `n + 1`.
The reason for this is that we define `Even3` to be `True` or `False` alternatively. If we want to
prove something from `Even3 n` by induction on `n`, we have to make sure that the information about
evenness is captured by some part of the definition.

So, how about focus only on `n + 2` in the inductive case? This is doable, because `Even3 n` is `True`
every two natural numbers. In other words, we only have to focus on the `n = 0` case and the case when
`n = k + 2` for some `k` such that `Even3 k`. We encode this as the following theorem.

> Note here that we use a predicate `pred: Nat -> Prop` as an object, i.e., we prove a theorem that
> is correct _for all_ predicate. In Lean, we not only define functions/theorems from terms to types,
> but also define functions/theorems from _functions from terms to propositions_ to propositions or even
> to _functions from terms to propositions_, with the same syntax as before. Later, we will see the unifying
> theory about this.
-/


theorem even3_ind {pred: Nat -> Prop}
  (zero: pred 0)
  (succ2: forall n, pred n -> pred (n + 2))
:
  forall n, (even: Even3 n) -> pred n
:= by
  have H: forall n, (Even3 n -> pred n) ∧ (Even3 (n + 1) -> pred (n + 1)) := by
    intro n
    induction n with
    | zero =>
      and_intros
      . intros
        exact zero
      . intro contra
        simp [Even3] at contra
    | succ n' IHn' =>
      and_intros
      . intro H
        apply IHn'.right H
      . intro H
        simp [Even3] at H
        apply succ2
        apply IHn'.left
        exact H
  intro n E
  apply (H n).left
  exact E


/-!
Now, the prove is much simpler. Lean will try figuring the predicate as is just an implicit parameter.
-/
theorem even3_even2' (n: Nat):
  (Even3 n -> Even2 n)
:= by
  intro H
  apply even3_ind (even := H) <;> unfold Even2  -- try this new syntax
  case zero =>
    exists 0
  case succ2 =>
    intro n
    rintro ⟨k, E⟩
    exists (k + 1)
    omega


/-!
## Predicates by Inductive Types
Based on our discussion, we can see that to define such an evenness `Even3 n` predicate, we only define
`Even3 0` to be provable and if we know `Even3 n` is provable, then `Even3 (n + 2)` is provable. Lean
allows us to use `inductive` type to collection the information of this. Just like a list, you begin
with the empty list, and you are able to add an element to an existing list to form a new one.
The only difference here is we define it to be an _inductive proposition_ instead of an _inductive type_.
-/

inductive Even : Nat -> Prop where
  | zero : Even 0
  | succ2 (n : Nat): Even n -> Even (n + 2)


/-!
Now, we have a new predicate `Even`, we look at the three rules needed to make a proposition of this `Even`.
- Formation rule: Given an `n: Nat`, `Even n` is a proposition
- Construction rule: You can either use `Even.zero` to prove `Even 0`, or prove `Even (n + 2)` from
  `Even n`, i.e., an _implication_ `Even.succ2: forall (n: Nat), Even n -> Even (n + 2)`.
- Elimination rule: This is a bit complicated, but in general it is the induction on `Even n`.
  We postpone the discussion of this. Let's see some examples about inductive propositions.

Here is an example of `Even 4`. We begin with `Even 0`; then we known `Even 2`; finally we know `Even 4`.
-/

example: Even 4 := by
  apply Even.succ2
  apply Even.succ2
  apply Even.zero


/-!
As we have seen, we know `2 * n` must be even. Still, we do the induction on `n`, which shows that
`Even2` implies `Even`.
-/

theorem ev_double : ∀ n, Even (2 * n) := by
  intro n
  induction n with
  | zero =>
    simp
    apply Even.zero
  | succ n' IH =>
    simp [Nat.mul_succ]
    apply Even.succ2
    exact IH

/-!
> The above proof also reveals another meaning of the inductive proposition. For some `Even2 n`, we must
> be able to find the `k: Nat` such that `n = 2 * k`. Obviously, this `k` is unique, so we can identify
> each `Even2 n` with a `k`. When `k` varies from `t` to `t + 1`, the `n` varies from `2 * t` to `2 * t + 2`,
> which is exactly our `succ2` constructor. So the `Even2 n` is constructed by the following sequence:
> `Even2 0`, `Even2 2`, `Even2 4`, ..., `Even2 n`. This `k` is exactly the number of `succ2` in the
> construction of `Even n`.
-/

/-!
For the direction from `Even` to `Even2`, since we do not know how to make use of a `p: Even n`, we cannot
prove it now. However, to prove something out of `Even2` does not always means an elimination, `succ2` is
one way to prove evenness out of evenness.
-/

theorem ev_plus4 : ∀ n, Even n -> Even (4 + n) := by
  intro n Hn
  rw [Nat.add_comm]
  apply Even.succ2
  apply Even.succ2
  exact Hn


/-!
## Example: Binary relation for comparing numbers

A binary relation on a set `X` is encoded as a function of type `X → X → Prop`. We are going to define the
_less than or equal to_ relation on natural numbers. Algebraically, how do we define it? One
possible one is that `n ≤ m` if and only if `n + k = m` for some `k`.
-/
def le1 (n: Nat) (m: Nat) := exists k, n + k = m

/-!
Let's look at the following typical proof about `le1`. Suppose `n.succ ≤ m.succ`. Let us unfold the
definition of `le1`, i.e. `k + n.succ = m.succ`. We then want to show `n ≤ m`, i.e. `k' + n = m` for some
`k': Nat`. Certainly, you can choose `k' := k` and the rest is just some algebraic facts that can be proved
by `omega`.
-/
theorem le1_succ_inj (n m: Nat):
  le1 n.succ m.succ ->
  le1 n m
:= by
  unfold le1
  rintro ⟨k, E⟩
  exists k
  omega


/-!
You can see from this example that each `le1 n m` is identified with a `k` such that `n + k = m`. Recall the
recursive definition of `n + k` (the recursion is on `k` this time). When `k` is zero, we just get the `n`;
when `k` is `k'.succ`, we first make `n + k'` and take its successor. Thus, we can understand `le1 n m` as a
process like this:
- When `k` is `0`, we get the relation `le1 n n`;
- When `k` is `k' + 1`, we first get a relation `le1 n m` by `m = n + k`. Then, we get a `le1 n (m + 1)`.
  This is to say that we get `le1 n (m + 1)` from `le1 n m`.

In other words, `n ≤ m` is made by the sequence `n ≤ n`, `n ≤ n + 1`, `n ≤ n + 2`, ..., `n ≤ n + k = m`.
We can record this construction process by the following inductive proposition.
-/


inductive le : Nat → Nat → Prop where
  | refl (n : Nat) : le n n
  | step (n m : Nat) : le n m → le n (m + 1)

/-!
For example, the relation `3 ≤ 5` can be `3 + 2 = 5`, which means the following construction.
- we start with `3 ≤ 3`;
- the next step is `3 ≤ 3 + 1 := 4`;
- the next final step is `3 ≤ 4 + 1 := 5`.

To prove it, you just reverse the process.
-/

example : le 3 5 := by
  apply le.step
  apply le.step
  apply le.refl

/-!
As before, we can also define this as a recursive function `le2: Nat -> Nat -> Prop`. To make
`le2 n (m + 1)`, we shall have `le2 n m`, or `n = m + 1`. We encode it in Lean as follows.
-/

def le2: Nat -> Nat -> Prop
  | n, 0 => n = 0
  | n, m + 1 => n = m + 1 ∨ le2 n m


/-!
It's obvious that `le2` implies `le`.
-/

theorem le2_le (n m: Nat):
  le2 n m -> le n m
:= by
  intro H
  induction m generalizing n with
  | zero =>
    simp [le2] at H
    rewrite [H]
    constructor
  | succ m' IH =>
    simp [le2] at H
    cases H with
    | inl H =>
      rewrite [H]
      apply le.refl
    | inr H =>
      apply le.step
      apply IH
      exact H


/-!
For the other direction, since we have not seen how make of use an inductively defined proposition,
we have no idea how to prove it. As noted above, `le` contains exactly the information of `n + k = m`.
We prove `le1` implies `le2` to give some hint on that.
-/


theorem le1_le2 (n m: Nat):
  le1 n m -> le2 n m
:= by
  unfold le1
  rintro ⟨k, E⟩
  induction k generalizing n m with
  | zero => -- this corresponds to the `refl` case
    simp at E
    rewrite [E]
    rcases m with ⟨⟩ | ⟨⟩
    . simp [le2]
    . simp [le2]
  | succ k' IH => -- this corresponds to the `step` case
    rewrite [<-E]
    simp [le2]
    right
    apply IH
    eq_refl


/-!
## Case analysis on Evidence

Finally, we answer how to make use of a inductive proposition, i.e., what is the elimination rule of it.
The rule itself can be written as an implicational form, which will be further discussed in
[this chapter](LeanFoundations.Logic.IndPrinciples.html). Here, we focus on the tactics that can exploit
an inductive defined proposition. An simple way is to do the case analysis on an evidence of such a proposition.

We have two examples now:
- the `Even` predicate,
- and the `le` relation.

In either case, we saw above that they are logically equivalent to some non-inductively defined propositions
(though we have not proved this in Lean). And in either cases, we see some recursive construction process:
- `Even n` is made by `Even 0` and `Even k -> Even (k + 2)`;
- `le n m` is made by `le n n` and `le n t -> le n (t + 1)`.

You can tell that from the constructors. Logically speaking, they shows the following:
- `H: Even n` is either `zero: Even 0 ∧ n = 0` or `succ2 n': Even n' -> Even (n' + 2) ∧ n = n' + 2 ∧ Even n'`.
- `H: le n m` is either `refl: le n n ∧ m = n` or `step m': le n m' -> le n (m' + 1)  ∧ m = m' + 1 ∧ le n m'`.

Lean allows you to use `cases` tactic to _destruct_ an inductively defined proposition. For example,
we can explicitly spell out the `evenness`.
-/

theorem ev_inversion : ∀ (n : Nat),
    Even n →
    (n = 0) ∨ (∃ n', n = n' + 2 ∧ Even n')
:= by
  intro n E
  cases E with  -- we have two cases for `E`
  | zero =>  -- `E` is `Even.zero`, which means `n = 0`.
    -- (0 = 0) ∨ (∃ n', 0 = n' + 2 ∧ Even n')
    left
    eq_refl
  | succ2 n' E' =>  -- `E` is some `succ2 n' E'`, where `n = n' + 2` and `E': Even n'`
    -- (n' + 2 = 0) ∨ (∃ n', n'' + 2 = n'' + 2 ∧ Even n'')
    right
    exists n'

/-!
### Exercise: 1 star, standard (le_inversion)
Prove the same _inversion lemma_ for `le`.
-/

theorem le_inversion : ∀ (n m : Nat),
  le n m →
  (n = m) ∨ (∃ m', m = m' + 1 ∧ le n m')
:= by
  intro n m H
  cases H with
  | refl =>
    sorry
  | step m' H' =>
    sorry

/-!
Lean will remove unnecessary cases for you automatically. For example, in the following, if we have
`Even n + 2`, then we either have `n + 2 = 0` or `n + 2 = n' + 2` for some `n': Nat` and `Even n'`.
It is impossible to have the `n + 2 = 0` case, so we only have to prove for the other cases. You can
use the explicit _inversion lemma_.
-/

theorem evSS_ev : ∀ n, Even (n + 2) → Even n := by
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
Or, you can let Lean do the simplification for you.
-/

theorem evSS_ev' : ∀ n, Even (n + 2) → Even n := by
  intro n E
  cases E with
  | succ2 n' E' =>
    -- This is the only case, and in this cases, n' = n.
    -- You don't have to do the rewrite manually.
    exact E'

/-!
The `cases` tactic will close the goal if no case is possible. For example, `Even 1` is impossible,
because you cannot have `1 = 0` and you cannot have `1 = n' + 2` (and `Even n'`). This is exactly the
application of EFQ.
-/

theorem one_not_even : ¬ Even 1 := by
  intro H
  cases H

/-!
### Exercise: 1 star, standard (SSSSev__even)
-/

theorem SSSSev__even : ∀ n, Even (n + 4) → Even n := by
  intro n H
  cases H with
  | succ2 n' H' =>
    admit

/-!
### Exercise: 1 star, standard (ev5_nonsense)

Prove the following result using `cases`.
-/

theorem ev5_nonsense : Even 5 → 2 + 2 = 9 := by
  intro H
  cases H with
  | succ2 n' H' =>
    admit


/-!
### Implicit Arguments
You can put implicit parameters in a constructor by the `{}` notation as before.
-/
inductive Even': Nat -> Prop where
  | zero: Even' 0
  | succ2 {n: Nat}: Even' n -> Even' (n + 2)


example (n: Nat): Even' (n + 2) -> Even' n := by
  intro E
  cases E with
  | succ2 H =>  -- You don't have to write the n' here.
    exact H


example (n: Nat): Even' (n + 2) -> Even' n := by
  intro E
  cases E with
  | @succ2 n' H =>  -- If you do need it, use `@` to give the names explicitly.
    exact H


/-!
## Induction on Evidence
The real elimination rule is the _induction_ on an evidence of an inductive type.
Recall how we make use of `Even3`:
```lean

def Even3: Nat -> Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even3 n


theorem even3_ind {pred: Nat -> Prop}
  (zero: pred 0)
  (succ2: forall n, pred n -> pred (n + 2))
:
  forall n, (even: Even3 n) -> pred n
```

`even3_ind` states that to make use of some `even: Even3 n`:
- we actually want a function `forall n, Even3 n -> pred n` for some predicate `pred`,
  so for each evidence of `Even3 n`, we just apply this function to get `pred n`;
- and, to get this function, we can prove the two following cases:
  - the base case: `pred 0` is true;
  - the inductive case: for all `n: Nat`, if `pred n` is true, then `pred (n + 2)` is true.

Since `Even` is just the inductive version of `Even3`, we make use of `Even n` in a similar but
a bit more delicate way: the predicate is defined on each `n` and `e: Even n`. This is to say,
to `pred: forall (n : Nat), Even n -> Prop` over all `Even n`,
we prove these two cases:
- the base case: `pred 0 Even.zero` is true;
- the inductive case: for all `n: Nat` and `e: Even n`,
  if `pred n e` is true, then `pred (n + 2)` is true.

In Lean, you just apply the tactic `induction` on some `e: Even n` and you will
get the base case and the inductive case:
-/

theorem ev_sum : ∀ n m, Even n → Even m → Even (n + m) := by
  intro n m Hn Hm
  induction Hn with
  | zero =>  -- This is the base case, we need to show `Even (0 + m)`, which is just `Even m`.
    simp
    exact Hm
  | succ2 n' E' IH =>
    -- Goal: Even (n' + 2 + m)
    -- We have IH : Even (n' + m)
    -- We want to show Even ((n' + m) + 2)
    have h : n' + 2 + m = (n' + m) + 2 := by
      rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
    rw [h]
    apply Even.succ2
    exact IH

/-!
### Exercise: 3 stars, advanced (ev_ev__ev)

Finding the appropriate thing to do induction on is a bit tricky here:
-/

theorem ev_ev__ev : ∀ n m, Even (n + m) → Even n → Even m := by
  intro n m Hnm Hn
  induction Hn with
  | zero =>
    simp at Hnm
    exact Hnm
  | succ2 n' E' IH =>
    -- We have Even (n' + 2 + m) and need to show Even m
    -- We can use IH : Even (n' + m) → Even m
    apply IH
    -- Now we need to show Even (n' + m) from Even (n' + 2 + m)
    have h : n' + 2 + m = (n' + m) + 2 := by
      rw [Nat.add_assoc, Nat.add_comm 2 m, ← Nat.add_assoc]
    rw [h] at Hnm
    apply evSS_ev
    exact Hnm

/-!
### Exercise: 3 stars, standard, especially useful (ev_plus_plus)

This exercise can be completed without induction or case analysis. But the proof is somewhat tricky.
-/

theorem ev_plus_plus : ∀ n m p, Even (n + m) → Even (n + p) → Even (m + p) := by
  intro n m p Hnm Hnp
  -- We'll use the fact that Even (n + m) and Even (n + p) implies Even ((n + m) + (n + p))
  -- which equals Even (2*n + m + p), and since Even (2*n), we get Even (m + p)
  have h1 : Even ((n + m) + (n + p)) := ev_sum (n + m) (n + p) Hnm Hnp
  have h2 : (n + m) + (n + p) = (n + n) + (m + p) := by
    rw [← Nat.add_assoc, Nat.add_assoc n m n, Nat.add_comm m n, ← Nat.add_assoc, Nat.add_assoc]
  rw [h2] at h1
  have h3 : Even (n + n) := by
    rw [← Nat.two_mul]
    apply ev_double
  apply ev_ev__ev (n + n) (m + p) h1 h3
