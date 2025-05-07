/-
Copyright (c) 2025 Xiao Tan and Robert Joseph George. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

! Upstream reference.
-/

import LeanFoundations.Logic.Basic

set_option linter.unusedVariables false

/-!
# Induction

This chapter introduces proof by induction in Lean.
The main differences from Coq are:

1. Import System:
   - Lean uses `import` instead of `Require Export`
   - Lean has a different module system
   - Lean uses `lake` for package management instead of `_CoqProject`

2. Proof Style:
   - Lean uses `by` instead of `Proof.`
   - Lean has different tactic names and syntax
   - Lean's proof automation is more powerful
   - Lean uses `rfl` instead of `reflexivity`
   - Lean uses `rw` instead of `rewrite`

3. Induction:
   - Lean's induction syntax is more concise
   - Lean has better support for induction hypotheses
   - Lean's type checker can automatically prove many simple cases
   - Lean uses `cases` and `induction` for case analysis

4. Assertions:
   - Lean uses `have` instead of `assert`
   - Lean has different syntax for local lemmas
   - Lean's proof automation can handle more cases automatically
-/

/-!
## Proof by Induction

In Lean, we can prove that 0 is a neutral element for + on the left using just reflexivity.
But the proof that it is also a neutral element on the right requires induction.
-/

theorem add_zero_r_firsttry (n : MyNat) : plus n .zero = n := by
  -- Just applying reflexivity doesn't work
  -- since the n in n + 0 is an arbitrary unknown number
  -- so the match in the definition of + can't be simplified
  sorry

/-!
And reasoning by cases using `cases` doesn't get us much further:
the branch where n = 0 goes through fine, but in the branch where n = succ n'
we get stuck in exactly the same way.
-/

theorem add_zero_r_secondtry (n : MyNat) : plus n .zero = n := by
  cases n with
  | zero => rfl  -- so far so good...
  | succ n' =>
    -- ...but here we are stuck again
    sorry

/-!
To prove interesting facts about numbers, lists, and other inductively defined sets,
we often need a more powerful reasoning principle: induction.

Recall the principle of induction over natural numbers:
If P(n) is some proposition involving a natural number n and we want to show
that P holds for all numbers n, we can reason like this:
1. show that P(0) holds;
2. show that, for any n', if P(n') holds, then so does P(succ n');
3. conclude that P(n) holds for all n.

In Lean, the steps are the same: we begin with the goal of proving P(n) for all n
and break it down (by applying the induction tactic) into two separate subgoals:
one where we must show P(0) and another where we must show P(n') → P(succ n').
-/

theorem add_zero_r (n : MyNat) : plus n .zero = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [plus]
    rw [ih]

/-!
Like `cases`, the `induction` tactic takes an `as...` clause that specifies
the names of the variables to be introduced in the subgoals. Since there are
two subgoals, the `as...` clause has two parts, separated by `|`.

In the first subgoal, n is replaced by 0. No new variables are introduced
(so the first part of the `as...` is empty), and the goal becomes 0 = 0 + 0,
which follows by simplification.

In the second subgoal, n is replaced by succ n', and the assumption n' + 0 = n'
is added to the context with the name ih (i.e., the Induction Hypothesis for n').
The goal in this case becomes succ n' = (succ n') + 0, which simplifies to
succ n' = succ (n' + 0), which in turn follows from ih.
-/

def minus (n m : MyNat) : MyNat :=
  match n, m with
  | n, .zero => n
  | .zero, .succ m' => .zero
  | .succ n', .succ m' => minus n' m'

theorem minus_n_n (n : MyNat) : minus n n = .zero := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [minus]
    rw [ih]

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
### Exercise: 2 stars, standard, especially useful (basic_induction)
Prove the following using induction. You might need previously proven results.
-/

theorem mul_zero_r (n : MyNat) : mult n .zero = .zero := by
  sorry

theorem plus_n_Sm (n m : MyNat) : MyNat.succ (plus n m) = plus n (MyNat.succ m) := by
  sorry

theorem add_comm (n m : MyNat) : plus n m = plus m n := by
  sorry

theorem add_assoc (n m p : MyNat) : plus (plus n m) p = plus n (plus m p) := by
  sorry

/-!
### Exercise: 2 stars, standard (double_plus)
Consider the following function, which doubles its argument:
-/

def double (n : MyNat) : MyNat :=
  match n with
  | .zero => .zero
  | .succ n' => .succ (.succ (double n'))

/-!
Use induction to prove this simple fact about double:
-/

theorem double_plus (n : MyNat) : double n = plus n n := by
  sorry

/-!
### Exercise: 2 stars, standard (eqb_refl)
The following theorem relates the computational equality =? on nat with the definitional equality = on bool.
-/

def eqb (n m : MyNat) : MyBool :=
  match n, m with
  | .zero, .zero => .true
  | .zero, .succ m' => .false
  | .succ n', .zero => .false
  | .succ n', .succ m' => eqb n' m'

theorem eqb_refl (n : MyNat) : eqb n n = .true := by
  sorry

/-!
### Exercise: 2 stars, standard, optional (even_S)
One inconvenient aspect of our definition of even n is the recursive call on n - 2.
This makes proofs about even n harder when done by induction on n, since we may need
an induction hypothesis about n - 2. The following lemma gives an alternative
characterization of even (S n) that works better with induction:
-/

def even (n : MyNat) : MyBool :=
  match n with
  | .zero => .true
  | .succ .zero => .false
  | .succ (.succ n') => even n'

theorem even_S (n : MyNat) : even (MyNat.succ n) = negb (even n) := by
  sorry

/-!
## Proofs Within Proofs

In Lean, as in informal mathematics, large proofs are often broken into a sequence
of theorems, with later proofs referring to earlier theorems. But sometimes a proof
will involve some miscellaneous fact that is too trivial and of too little general
interest to bother giving it its own top-level name. In such cases, it is convenient
to be able to simply state and prove the needed "sub-theorem" right at the point
where it is used. The `have` tactic allows us to do this.
-/

theorem mult_0_plus' (n m : MyNat) : mult (plus (plus n .zero) .zero) m = mult n m := by
  have h : plus (plus n .zero) .zero = n := by
    rw [add_comm]
    rw [plus]
    rw [add_comm]
    rfl
  rw [h]

/-!
The `have` tactic introduces two sub-goals. The first is the assertion itself;
by prefixing it with h: we name the assertion h. Note that we surround the proof
of this assertion with curly braces { ... }, both for readability and so that,
when using Lean interactively, we can see more easily when we have finished
this sub-proof. The second goal is the same as the one at the point where we
invoke `have` except that, in the context, we now have the assumption h that
n + 0 + 0 = n. That is, `have` generates one subgoal where we must prove the
asserted fact and a second subgoal where we can use the asserted fact to make
progress on whatever we were trying to prove in the first place.
-/

/-!
### Exercise: 3 stars, standard, especially useful (mul_comm)
Use `have` to help prove add_shuffle3. You don't need to use induction yet.
-/

theorem add_shuffle3 (n m p : MyNat) : plus n (plus m p) = plus m (plus n p) := by
  sorry

/-!
Now prove commutativity of multiplication. You will probably want to look for
(or define and prove) a "helper" theorem to be used in the proof of this one.
Hint: what is n × (1 + k)?
-/

theorem mul_comm (m n : MyNat) : mult m n = mult n m := by
  sorry

/-!
### Exercise: 2 stars, standard, optional (plus_leb_compat_l)
If a hypothesis has the form H: P → a = b, then rewrite H will rewrite a to b
in the goal, and add P as a new subgoal. Use that in the inductive step of this exercise.
-/

def leb (n m : MyNat) : MyBool :=
  match n, m with
  | .zero, _ => .true
  | .succ n', .zero => .false
  | .succ n', .succ m' => leb n' m'

theorem plus_leb_compat_l (n m p : MyNat) :
  leb n m = .true → leb (plus p n) (plus p m) = .true := by
  sorry

/-!
### Exercise: 3 stars, standard, optional (more_exercises)
Take a piece of paper. For each of the following theorems, first think about whether
(a) it can be proved using only simplification and rewriting, (b) it also requires
case analysis (destruct), or (c) it also requires induction. Write down your prediction.
Then fill in the proof.
-/

theorem leb_refl (n : MyNat) : leb n n = .true := by
  sorry

theorem zero_neqb_S (n : MyNat) : eqb .zero (MyNat.succ n) = .false := by
  sorry

theorem andb_false_r (b : MyBool) : andb b .false = .false := by
  sorry

theorem S_neqb_0 (n : MyNat) : eqb (MyNat.succ n) .zero = .false := by
  sorry

theorem mult_1_l (n : MyNat) : mult (MyNat.succ .zero) n = n := by
  sorry

theorem all3_spec (b c : MyBool) :
  orb (andb b c) (orb (negb b) (negb c)) = .true := by
  sorry

theorem mult_plus_distr_r (n m p : MyNat) :
  mult (plus n m) p = plus (mult n p) (mult m p) := by
  sorry

theorem mult_assoc (n m p : MyNat) :
  mult n (mult m p) = mult (mult n m) p := by
  sorry

/-!
### Exercise: 2 stars, standard, optional (add_shuffle3')
The `replace` tactic allows you to specify a particular subterm to rewrite and
what you want it rewritten to: replace (t) with (u) replaces (all copies of)
expression t in the goal by expression u, and generates t = u as an additional
subgoal. This is often useful when a plain rewrite acts on the wrong part of the goal.

Use the `replace` tactic to do a proof of add_shuffle3', just like add_shuffle3
but without needing `have`.
-/

theorem add_shuffle3' (n m p : MyNat) : plus n (plus m p) = plus m (plus n p) := by
  sorry

/-!
## Nat to Bin and Back to Nat
-/

/-!
### Exercise: 3 stars, standard, especially useful (binary_commute)
Prove that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

That is, incrementing a binary number and then converting it to a (unary)
natural number yields the same result as first converting it to a natural
number and then incrementing.
-/

theorem bin_to_nat_pres_incr (b : Bin) :
  bin_to_nat (incr b) = MyNat.succ (bin_to_nat b) := by
  sorry

/-!
### Exercise: 3 stars, standard (nat_bin_nat)
Write a function to convert natural numbers to binary numbers.
-/

def nat_to_bin (n : MyNat) : Bin := sorry

/-!
Prove that, if we start with any nat, convert it to bin, and convert it back,
we get the same nat which we started with.
-/

theorem nat_bin_nat (n : MyNat) : bin_to_nat (nat_to_bin n) = n := by
  sorry

/-!
## Bin to Nat and Back to Bin (Advanced)

The opposite direction -- starting with a bin, converting to nat, then converting
back to bin -- turns out to be problematic. That is, the following theorem does
not hold.
-/

theorem bin_nat_bin_fails (b : Bin) : nat_to_bin (bin_to_nat b) = b := by
  sorry

/-!
### Exercise: 2 stars, advanced (double_bin)
Prove this lemma about double, which we defined earlier in the chapter.
-/

theorem double_incr (n : MyNat) : double (MyNat.succ n) = MyNat.succ (MyNat.succ (double n)) := by
  sorry

/-!
Now define a similar doubling function for bin.
-/

def double_bin (b : Bin) : Bin := sorry

/-!
Check that your function correctly doubles zero.
-/

theorem double_bin_zero : double_bin .Z = .Z := by
  sorry

/-!
Prove this lemma, which corresponds to double_incr.
-/

theorem double_incr_bin (b : Bin) :
  double_bin (incr b) = incr (incr (double_bin b)) := by
  sorry

/-!
### Exercise: 4 stars, advanced (bin_nat_bin)
Define normalize. You will need to keep its definition as simple as possible
for later proofs to go smoothly. Do not use bin_to_nat or nat_to_bin, but do
use double_bin.

Hint: Structure the recursion such that it always reaches the end of the bin
and process each bit only once. Do not try to "look ahead" at future bits.
-/

def normalize (b : Bin) : Bin := sorry

/-!
Finally, prove the main theorem. The inductive cases could be a bit tricky.

Hint: Start by trying to prove the main statement, see where you get stuck,
and see if you can find a lemma -- perhaps requiring its own inductive proof --
that will allow the main proof to make progress. We have one lemma for the B0
case (which also makes use of double_incr_bin) and another for the B1 case.
-/

theorem bin_nat_bin (b : Bin) : nat_to_bin (bin_to_nat b) = normalize b := by
  sorry
