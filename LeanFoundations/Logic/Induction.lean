/-
Copyright (c) 2025 Xiao Tan and Robert Joseph George. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George
-/

import LeanFoundations.Logic.Basic

set_option linter.unusedVariables false -- If you don't want to see the unused variables warning.

/-!
# Induction

In the previous chapter, we learned about basic functional programming in Lean
and how to define simple types and functions. Now we'll learn about one of the
most powerful proof techniques in mathematical reasoning: proof by induction.

Induction allows us to prove properties that hold for all members of an
inductively defined type, such as natural numbers. It's especially useful when
we need to reason about recursive functions, which we defined in the previous
chapter.

Just like mathematical induction that you might have seen in discrete mathematics,
induction in Lean follows a similar pattern:
1. Prove the base case (e.g., the property holds for 0)
2. Prove the inductive step (e.g., if the property holds for n, then it also holds for n+1)
3. Conclude that the property holds for all cases

The main differences from Coq that you'll notice in this chapter are:

1. **Import System**:
   - Lean uses `import` instead of Coq's `Require Export`
   - Lean has a different module system with packages organized in a hierarchical manner
   - Lean uses the `lake` build system for package management instead of Coq's `_CoqProject`

2. **Proof Style**:
   - Lean uses the `by` keyword to begin tactic proofs instead of Coq's `Proof.`
   - Lean tactics have different names and syntax, though many concepts are similar
   - Lean's proof automation is often more powerful than Coq's
   - Lean uses `rfl` as a shorthand for reflexivity instead of Coq's `reflexivity`
   - Lean uses `rw` for rewriting instead of Coq's `rewrite`

3. **Induction**:
   - Lean's induction syntax is more concise and readable
   - Lean provides better support for working with induction hypotheses
   - Lean's type checker can automatically prove many simple cases
   - Lean uses `cases` for simple case analysis and `induction` for full induction

4. **Assertions**:
   - Lean uses `have` instead of Coq's `assert` for introducing local facts
   - Lean has cleaner syntax for local lemmas
   - Lean's proof automation can handle more cases automatically
-/

/-!
## Proof by Induction

Let's start with a simple example. In the previous chapter, we defined addition
for natural numbers using pattern matching and recursion. Now we want to prove
some properties of addition.

One property we might want to prove is that adding 0 to any natural number n
on the right gives the same number n. This is written mathematically as:

    ∀ n : ℕ, n + 0 = n

In Lean, we could try to prove this directly using reflexivity, but it won't work:
-/

theorem add_zero_r_firsttry (n : MyNat) : plus n .zero = n := by
  -- Just applying reflexivity doesn't work here.
  -- The reason is that `n` is an arbitrary unknown number, so Lean can't
  -- directly compute the result of `plus n .zero`. The recursion in the definition
  -- of `plus` requires a concrete value for `n` to unfold properly.
  --
  -- The definition of `plus` from the previous chapter was:
  -- def plus (n m : MyNat) : MyNat :=
  --   match n with
  --   | .zero => m
  --   | .succ n' => .succ (plus n' m)
  --
  -- For Lean to simplify `plus n .zero`, it needs to know whether n is .zero or .succ n'
  -- so it can choose the right branch of the match statement.
  sorry

/-!
We might try to use case analysis with the `cases` tactic, which breaks `n` into
its possible constructors (.zero and .succ n'). Let's see how far that gets us:
-/

theorem add_zero_r_secondtry (n : MyNat) : plus n .zero = n := by
  cases n with
  | zero => rfl  -- For n = 0, we have 0 + 0 = 0, which is true by reflection
  | succ n' =>
    -- For n = succ n', we have (succ n') + 0 = succ n'
    -- By definition of plus, we get succ(n' + 0) = succ n'
    -- This would be true if n' + 0 = n', but we don't know that yet!
    -- We're stuck in a loop: to prove n + 0 = n for successor cases,
    -- we'd need to already know it for the predecessor n'
    sorry

/-!
This is where induction comes in! Induction is precisely the proof technique we
need when we have a goal that depends on a previously established property for a
smaller value.

Recall the principle of induction for natural numbers from mathematics:
If P(n) is some property involving natural numbers, to prove P(n) holds for all n:
1. Prove P(0) holds (base case)
2. Prove that for any n', if P(n') holds, then P(succ n') also holds (inductive step)
3. Conclude that P(n) holds for all natural numbers

In Lean, we apply this principle using the `induction` tactic. Let's see how it works:
-/

theorem add_zero_r (n : MyNat) : plus n .zero = n := by
  induction n with
  | zero =>
    -- Base case: Prove that 0 + 0 = 0
    -- This follows directly from the definition of plus
    rfl
  | succ n' ih =>
    -- Inductive step: Prove that (succ n') + 0 = succ n'
    -- We assume the induction hypothesis (ih): n' + 0 = n'

    -- First, we use the definition of plus:
    -- (succ n') + 0 = succ(n' + 0)
    rw [plus]

    -- Now we have: succ(n' + 0) = succ n'
    -- By our induction hypothesis, n' + 0 = n'
    -- So we can rewrite: succ(n' + 0) to succ(n')
    rw [ih]
    -- And we're done! succ n' = succ n' is reflexively true

/-!
Notice how the `induction` tactic generates two subgoals, corresponding to the
base case and the inductive step:

1. In the base case, `n` is replaced by `.zero`, and we need to prove `.zero + .zero = .zero`.
   This follows directly from the definition of `plus`.

2. In the inductive step, `n` is replaced by `.succ n'`, and we get an induction hypothesis
   `ih: plus n' .zero = n'`. We need to prove `.succ n' + .zero = .succ n'`.

   By the definition of `plus`, we have:
   `.succ n' + .zero = .succ (plus n' .zero)`

   Then, using our induction hypothesis, we can rewrite `plus n' .zero` to `n'`:
   `.succ (plus n' .zero) = .succ n'`

   After rewriting, we have:
   `.succ n' = .succ n'`, which is true by reflexivity.

This pattern of using induction to prove properties about recursive functions is extremely
common and powerful. The induction principle gives us exactly what we need to handle
recursive calls in proofs.
-/

/-!
Let's look at another example. We'll prove that subtracting a number from itself
always results in zero.
-/

def minus (n m : MyNat) : MyNat :=
  match n, m with
  | n, .zero => n           -- n - 0 = n
  | .zero, .succ m' => .zero -- 0 - (m+1) = 0 (can't go below zero)
  | .succ n', .succ m' => minus n' m' -- (n+1) - (m+1) = n - m

theorem minus_n_n (n : MyNat) : minus n n = .zero := by
  induction n with
  | zero =>
    -- Base case: 0 - 0 = 0
    -- By definition of minus, minus 0 0 = 0
    rfl
  | succ n' ih =>
    -- Inductive step: (n'+1) - (n'+1) = 0
    -- We assume ih: n' - n' = 0

    -- By definition of minus:
    -- minus (succ n') (succ n') = minus n' n'
    rw [minus]

    -- Now use the induction hypothesis
    rw [ih]
    -- Done! We've shown that (n'+1) - (n'+1) = 0

/-!
In this proof, the induction principle allows us to handle the recursive structure of the
`minus` function elegantly. The induction hypothesis matches precisely what we need
in the recursive case of `minus`.

## Exercises

Now let's try some exercises that use induction. These exercises are adapted from
the Software Foundations course and will help you practice the concepts we've
covered so far.

Each exercise comes with a difficulty rating (in stars) and a description of the
task. Try to solve them on your own before looking at the solutions!

Tips for solving these exercises:
1. Start by understanding what the theorem is asking you to prove
2. Think about which proof technique is appropriate (induction, case analysis, etc.)
3. If using induction, identify the base case and inductive step
4. Use the tactics we've learned: rfl, rw, cases, induction, etc.
5. Remember that the structure of your proof should follow the recursive structure
   of the functions involved
-/

/-!
### Exercise: 2 stars, standard, especially useful (basic_induction)
Prove the following using induction. You might need previously proven results.
-/

theorem mul_zero_r (n : MyNat) : mult n .zero = .zero := by
  /-
  We need to prove that multiplying any natural number by 0 gives 0.
  This is a good candidate for induction since multiplication is defined recursively.

  Hint: Look at the definition of mult from the basics file:
  def mult (n m : MyNat) : MyNat :=
    match n with
    | .zero => .zero
    | .succ n' => plus m (mult n' m)

  Try to follow the pattern we used in the add_zero_r proof above.
  -/
  sorry

theorem plus_n_Sm (n m : MyNat) : MyNat.succ (plus n m) = plus n (MyNat.succ m) := by
  /-
  This theorem says that S(n + m) = n + S(m).
  In other words, adding 1 to (n + m) is the same as adding 1 to m and then adding n.

  Think about how plus is defined recursively and consider using induction on n.

  Hint: For the inductive step, you'll need to think about how
  S((S n') + m) relates to (S n') + S(m).
  -/
  sorry

theorem add_comm (n m : MyNat) : plus n m = plus m n := by
  /-
  This theorem states that addition is commutative: n + m = m + n.

  This is a more challenging proof that likely requires induction and
  previously proven results like plus_n_Sm.

  Hint: Try induction on n. For the inductive step, you'll need to reason about
  how S(n') + m relates to m + S(n').
  -/
  sorry

theorem add_assoc (n m p : MyNat) : plus (plus n m) p = plus n (plus m p) := by
  /-
  This theorem states that addition is associative: (n + m) + p = n + (m + p).

  This proof also likely requires induction, but should be more straightforward
  than commutativity.

  Hint: Try induction on n and apply the definition of plus.
  -/
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
This function adds n to itself by recursively building up the result.
For example:
- double 0 = 0
- double 1 = 2 (= .succ (.succ .zero))
- double 2 = 4 (= .succ (.succ (.succ (.succ .zero))))

Now, use induction to prove this simple fact about double:
-/

theorem double_plus (n : MyNat) : double n = plus n n := by
  /-
  This theorem states that doubling a number is the same as adding it to itself.

  Think about the recursive structure of the double function and how it relates
  to the definition of plus.

  Hint: Use induction on n. For the inductive step, think about how
  double (S n') relates to (S n') + (S n').
  -/
  sorry

/-!
### Exercise: 2 stars, standard (eqb_refl)
The function `eqb` tests whether two natural numbers are equal,
returning a boolean result. We want to prove that `eqb n n` always
returns `true` for any natural number `n`.
-/

def eqb (n m : MyNat) : MyBool :=
  match n, m with
  | .zero, .zero => .true
  | .zero, .succ m' => .false
  | .succ n', .zero => .false
  | .succ n', .succ m' => eqb n' m'

theorem eqb_refl (n : MyNat) : eqb n n = .true := by
  /-
  This theorem states that comparing any number to itself with eqb always returns true.

  The eqb function is defined recursively, so this is another good candidate for induction.

  Hint: Follow the recursive structure of eqb in your proof.
  -/
  sorry

/-!
### Exercise: 2 stars, standard, optional (even_S)
One inconvenient aspect of our definition of even is the recursive call on n - 2.
This makes proofs about even n harder when done by induction on n, since we may need
an induction hypothesis about n - 2.

The following lemma gives an alternative characterization of even for successor
numbers that works better with induction:
-/

def even (n : MyNat) : Bool :=
  match n with
  | .zero => .true
  | .succ .zero => .false
  | .succ (.succ n') => even n'

theorem even_S (n : MyNat) : even (MyNat.succ n) = negb (even n) := by
  /-
  This theorem states that a number n+1 is even if and only if n is odd.
  In boolean terms, even(S n) = negb(even n).

  This requires case analysis on n and careful reasoning about the definition of even.

  Hint: Try using cases on n to handle different possibilities.
  -/
  sorry

/-!
## Proofs Within Proofs

In mathematics, large proofs are often broken down into smaller lemmas and theorems.
Similarly, in Lean, we can create smaller "sub-proofs" within a larger proof
using the `have` tactic.

The `have` tactic allows us to state and prove a fact locally within a proof,
without needing to create a separate top-level theorem. This is useful when we
need a specific fact that may not be general enough to deserve its own named theorem.
-/

theorem mult_0_plus' (n m : MyNat) : mult (plus (plus n .zero) .zero) m = mult n m := by
  have h : plus (plus n .zero) .zero = n := by
    /-
    This is our "sub-proof" where we establish that n + 0 + 0 = n
    We could have used add_zero_r, but we're showing how to do it directly
    -/
    rw [add_comm]  -- Swap n and 0, giving 0 + n + 0 = n
    rw [plus]      -- Compute 0 + n = n, giving n + 0 = n
    rw [add_comm]  -- Swap n and 0 again, giving 0 + n = n
    rfl            -- 0 + n = n is true by definition

  /-
  Now we use our local lemma h to rewrite the goal:
  mult (plus (plus n .zero) .zero) m = mult n m
  becomes:
  mult n m = mult n m
  -/
  rw [h]
  /- And we're done! mult n m = mult n m is reflexively true -/

/-!
The `have` tactic introduces two subgoals:

1. First, we must prove the statement we're asserting (in this case, that `plus (plus n .zero) .zero = n`).
   We name this assertion `h` so we can refer to it later.

2. Second, we continue with our main proof, but now we have `h` available as a premise
   that we can use.

This technique is invaluable for breaking down complex proofs into smaller, more
manageable pieces. It improves readability and makes proofs easier to understand
and debug.
-/

/-!
### Exercise: 3 stars, standard, especially useful (mul_comm)
Use `have` to help prove add_shuffle3. You don't need to use induction yet.
-/

theorem add_shuffle3 (n m p : MyNat) : plus n (plus m p) = plus m (plus n p) := by
  /-
  This theorem states that n + (m + p) = m + (n + p).
  Intuitively, it means we can shuffle the order of addition as long as
  the last element stays the same.

  The `have` tactic can be useful here to establish intermediate steps.
  This can be proven using commutativity and associativity of addition.

  Hint: Try breaking this down into smaller steps using `have`.
  -/
  sorry

/-!
Now prove commutativity of multiplication. You will probably want to look for
(or define and prove) a "helper" theorem to be used in the proof of this one.
Hint: what is n × (1 + k)?
-/

theorem mul_comm (m n : MyNat) : mult m n = mult n m := by
  /-
  This theorem states that multiplication is commutative: m × n = n × m.

  This is quite challenging and likely requires both induction and
  helper lemmas. Think about how mult is defined and what properties
  you might need along the way.

  Hint: Consider proving a helper lemma about distributivity or about
  multiplying by successor numbers.
  -/
  sorry

/-!
### Exercise: 2 stars, standard, optional (plus_leb_compat_l)
If a hypothesis has the form H: P → a = b, then rewrite H will rewrite a to b
in the goal, and add P as a new subgoal. Use that in the inductive step of this exercise.
-/

def leb (n m : MyNat) : MyBool :=
  match n, m with
  | .zero, _ => .true           -- 0 is always less than or equal to any number
  | .succ n', .zero => .false   -- n+1 is never less than or equal to 0
  | .succ n', .succ m' => leb n' m'  -- n+1 ≤ m+1 if and only if n ≤ m

theorem plus_leb_compat_l (n m p : MyNat) :
  leb n m = .true → leb (plus p n) (plus p m) = .true := by
  /-
  This theorem states that if n ≤ m, then p + n ≤ p + m.
  In other words, adding the same number to both sides of an inequality
  preserves the inequality.

  The unique aspect of this theorem is that it has a premise (n ≤ m)
  and uses the implication arrow (→).

  Hint: Try using induction on p and carefully consider how to handle
  the induction hypothesis, which also has an implication.
  -/
  sorry

/-!
### Exercise: 3 stars, standard, optional (more_exercises)
Take a piece of paper. For each of the following theorems, first think about whether
(a) it can be proved using only simplification and rewriting, (b) it also requires
case analysis (destruct), or (c) it also requires induction. Write down your prediction.
Then fill in the proof.
-/

theorem leb_refl (n : MyNat) : leb n n = .true := by
  /-
  This theorem states that n ≤ n for any natural number n.

  Think about the definition of leb and what proof technique would be most appropriate.

  Hint: Consider how leb compares equal numbers.
  -/
  sorry

theorem zero_neqb_S (n : MyNat) : eqb .zero (MyNat.succ n) = .false := by
  /-
  This theorem states that 0 is never equal to any successor number.

  Think about how eqb handles comparison between 0 and S n.

  Hint: Look at the definition of eqb.
  -/
  sorry

theorem andb_false_r (b : Bool) : andb b .false = .false := by
  /-
  This theorem states that AND with false on the right is always false.

  Think about the definition of andb and what proof technique would be most appropriate.

  Hint: Consider using case analysis on b.
  -/
  sorry

theorem S_neqb_0 (n : MyNat) : eqb (MyNat.succ n) .zero = .false := by
  /-
  This theorem states that no successor number is equal to 0.

  Similar to zero_neqb_S, but with the arguments to eqb swapped.

  Hint: Look at the definition of eqb.
  -/
  sorry

theorem mult_1_l (n : MyNat) : mult (MyNat.succ .zero) n = n := by
  /-
  This theorem states that 1 × n = n for any natural number n.

  Think about how mult is defined and what 1 (i.e., S 0) means in this context.

  Hint: Consider using the definition of mult and rewriting.
  -/
  sorry

theorem all3_spec (b c : Bool) :
  orb (andb b c) (orb (negb b) (negb c)) = .true := by
  /-
  This is a boolean logic theorem: (b ∧ c) ∨ (¬b ∨ ¬c) is always true.

  Think about the possible combinations of b and c and how to approach this proof.

  Hint: Case analysis on b and c would be helpful here.
  -/
  sorry

theorem mult_plus_distr_r (n m p : MyNat) :
  mult (plus n m) p = plus (mult n p) (mult m p) := by
  /-
  This theorem states the distributive property of multiplication over addition:
  (n + m) × p = (n × p) + (m × p)

  This likely requires induction and careful use of previous theorems.

  Hint: Try induction on n and use the definitions of mult and plus.
  -/
  sorry

theorem mult_assoc (n m p : MyNat) :
  mult n (mult m p) = mult (mult n m) p := by
  /-
  This theorem states that multiplication is associative:
  n × (m × p) = (n × m) × p

  This is another challenging proof that will likely require induction
  and careful reasoning about the definition of mult.

  Hint: Try induction on n and use the distributive property.
  -/
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
  /-
  This theorem states the same property as add_shuffle3, but you should
  use the replace tactic instead of have.

  Hint: Think about which sub-expression you want to replace and with what.
  -/
  sorry

/-!
## Nat to Bin and Back to Nat

Now we'll explore the relationship between unary natural numbers (MyNat)
and binary numbers (Bin). Recall that we defined the binary representation
in the basics file:

```lean
inductive Bin where
  | Z              -- Zero
  | B0 (n : Bin)  -- Append 0 (multiply by 2)
  | B1 (n : Bin)  -- Append 1 (multiply by 2 and add 1)

  Along with functions to increment a binary number and convert a binary number to a natural number:
  ```lean
  def incr (b : Bin) : Bin
  def bin_to_nat (b : Bin) : MyNat
  ```

These functions allow us to move between the binary and unary representations of numbers.
Binary representation is particularly important in computer science as computers store
numbers in binary format. Understanding the relationship between these representations
helps us grasp how computers handle numbers efficiently.
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

This property is important because it shows that our two number representations
and the operations we've defined on them are consistent with each other. It
confirms that "incrementing" means the same thing in both representations.
-/

theorem bin_to_nat_pres_incr (b : Bin) :
  bin_to_nat (incr b) = MyNat.succ (bin_to_nat b) := by
  /-
  This theorem establishes that the diagram above commutes - incrementing in
  binary and then converting to nat gives the same result as converting to nat
  and then incrementing.

  Let's think about how to approach this:

  1. We need to consider what happens when we increment a binary number
  2. The result depends on the structure of the binary number (Z, B0, or B1)
  3. Since both incr and bin_to_nat are defined recursively, induction is appropriate

  The proof will require induction on b, with separate cases for Z, B0(b'), and B1(b').
  For each case, we'll need to:
   - Apply the definition of incr
   - Apply the definition of bin_to_nat
   - Use the induction hypothesis when appropriate
   - Simplify to show the two sides are equal
  -/
  sorry

/-!
### Exercise: 3 stars, standard (nat_bin_nat)
Write a function to convert natural numbers to binary numbers.

This function completes the circle, allowing us to convert from natural numbers
to binary and back again. When designing this function, think about how binary
numbers are constructed - each digit position represents a power of 2.
-/

def nat_to_bin (n : MyNat) : Bin :=
  /-
  To convert a natural number to binary, we need a systematic approach.

  There are several ways to implement this:

  1. The recursive approach:
     - Base case: 0 converts to Z
     - For n > 0, we can determine if n is odd or even, and build the binary
       representation from least significant bit to most significant bit

  2. An iterative approach:
     - Start with Z (binary 0)
     - For each number from 1 to n, increment the binary representation

  The iterative approach aligns well with our incr function, but might be less efficient.
  The recursive approach is more efficient but requires handling odd/even cases.

  Hint: For a recursive solution, consider using a helper function that handles
  division by 2 and checking for odd/even.
  -/
  sorry

/-!
Prove that, if we start with any nat, convert it to bin, and convert it back,
we get the same nat which we started with.

This is an important "round-trip" property. It ensures that our conversion
functions preserve the value of the number, which is crucial for using binary
representation reliably.
-/

theorem nat_bin_nat (n : MyNat) : bin_to_nat (nat_to_bin n) = n := by
  /-
  This theorem establishes that converting from nat to bin and back to nat
  preserves the original number.

  The approach here is to use induction on n:

  1. Base case: Show that bin_to_nat (nat_to_bin 0) = 0
  2. Inductive step: Assume bin_to_nat (nat_to_bin n') = n'
     and prove bin_to_nat (nat_to_bin (succ n')) = succ n'

  The inductive step might require using the previous theorem about
  bin_to_nat and incr, depending on how nat_to_bin is implemented.

  A key insight: If nat_to_bin (succ n) = incr (nat_to_bin n),
  then we can leverage bin_to_nat_pres_incr.
  -/
  sorry

/-!
## Bin to Nat and Back to Bin (Advanced)

The opposite direction -- starting with a bin, converting to nat, then converting
back to bin -- turns out to be problematic. That is, the following theorem does
not hold:

theorem bin_nat_bin_fails (b : Bin) : nat_to_bin (bin_to_nat b) = b

This theorem fails because binary representations of numbers are not unique.
For example, Z (zero) and B0 Z (adding a leading zero) both represent the natural
number 0. The bin_to_nat function maps both Z and B0 Z to 0, and then nat_to_bin
would map 0 back to a canonical representation (likely Z), not necessarily
the original b.

This is a common issue with number representation conversions. To resolve it,
we need to define a "normalization" function that converts any binary number
to a canonical form. Then we can prove that converting to nat and back gives
us the normalized form of the original binary number.
-/

/-!
### Exercise: 2 stars, advanced (double_bin)
Prove this lemma about double, which we defined earlier in the chapter.

This lemma establishes a property about the double function that will be useful
for our normalization approach.
-/

theorem double_incr (n : MyNat) : double (MyNat.succ n) = MyNat.succ (MyNat.succ (double n)) := by
  /-
  This theorem relates doubling the successor of n to adding 2 to the double of n.

  Let's recall the definition of double:
  def double (n : MyNat) : MyNat :=
    match n with
    | .zero => .zero
    | .succ n' => .succ (.succ (double n'))

  For the successor case, we need to show:
  double (succ n) = succ (succ (double n))

  This can be done directly from the definition of double, followed by
  straightforward rewriting steps.
  -/
  sorry

/-!
Now define a similar doubling function for bin.

This function will be essential for creating our normalization function.
The relationship between doubling and binary representation should be
straightforward: doubling a binary number is equivalent to appending a 0 bit.
-/

def double_bin (b : Bin) : Bin :=
  /-
  Implement a function that doubles a binary number.

  In binary, doubling a number means shifting all bits one position to the left,
  or equivalently, appending a 0 at the end.

  For example:
  - double_bin Z = Z (0 × 2 = 0)
  - double_bin (B1 Z) = B0 (B1 Z) (1 × 2 = 2, which is 10 in binary)
  - double_bin (B1 (B0 Z)) = B0 (B1 (B0 Z)) (2 × 2 = 4, which is 100 in binary)

  Hint: The simplest implementation is just to append a 0 bit (use B0).
  -/
  sorry

/-!
Check that your function correctly doubles zero.
-/

theorem double_bin_zero : double_bin .Z = .Z := by
  /-
  Verify that doubling zero gives zero.

  This should follow directly from your definition of double_bin,
  as doubling zero should still be zero.
  -/
  sorry

/-!
Prove this lemma, which corresponds to double_incr.

This lemma establishes an important property about the relationship between
doubling and incrementing in binary representation.
-/

theorem double_incr_bin (b : Bin) :
  double_bin (incr b) = incr (incr (double_bin b)) := by
  /-
  This theorem for Bin corresponds to the double_incr theorem for MyNat.
  It states that doubling the increment of b is the same as
  incrementing twice the double of b.

  In mathematical terms: 2 × (b + 1) = (2 × b) + 2

  The proof will require induction on b, with separate cases for Z, B0(b'), and B1(b').
  For each case, we'll need to:
   - Apply the definitions of double_bin and incr
   - Use the induction hypothesis when appropriate
   - Simplify to show the two sides are equal

  This can be tricky because incrementing a binary number can require carrying
  operations that propagate through multiple bits.
  -/
  sorry

/-!
### Exercise: 4 stars, advanced (bin_nat_bin)
Define normalize. You will need to keep its definition as simple as possible
for later proofs to go smoothly. Do not use bin_to_nat or nat_to_bin, but do
use double_bin.

The normalize function converts any binary number to a canonical form,
ensuring that each natural number has a unique binary representation.

Hint: Structure the recursion such that it always reaches the end of the bin
and process each bit only once. Do not try to "look ahead" at future bits.
-/

def normalize (b : Bin) : Bin :=
  /-
  Implement a function that converts a binary number to its canonical form.

  The main goal is to eliminate redundant leading zeros. For example,
  both Z and B0 Z represent 0, but we want to normalize both to Z.

  For the canonical form, we should follow these principles:
  1. Z is the canonical form for 0
  2. No leading zeros (except for Z itself)
  3. Every other binary number should have a unique representation

  A recursive approach works well here:
  - Base case: Z is already normalized
  - Recursive cases: Handle B0 and B1, ensuring correct normalization

  Remember to use double_bin in your implementation. This will make
  later proofs more straightforward.

  Hint: For B0 b', consider whether b' normalizes to Z, as this is a special case
  (we don't want B0 Z, which would be a leading zero).
  -/
  sorry

/-!
Finally, prove the main theorem. The inductive cases could be a bit tricky.

This theorem establishes that the round-trip conversion from bin to nat and
back creates the normalized form of the original binary number.

Hint: Start by trying to prove the main statement, see where you get stuck,
and see if you can find a lemma -- perhaps requiring its own inductive proof --
that will allow the main proof to make progress. We have one lemma for the B0
case (which also makes use of double_incr_bin) and another for the B1 case.
-/

theorem bin_nat_bin (b : Bin) : nat_to_bin (bin_to_nat b) = normalize b := by
  /-
  This theorem establishes that converting from bin to nat and back to bin
  gives the normalized version of the original binary number.

  The approach is to use induction on b, with cases for Z, B0 b', and B1 b'.

  For each case:
  1. Apply definitions of bin_to_nat, nat_to_bin, and normalize
  2. Use the induction hypothesis when appropriate
  3. Apply lemmas about double_bin and other properties
  4. Simplify to show the two sides are equal

  This is quite a challenging proof and may require developing additional
  helper lemmas along the way. For example:

  - A lemma relating nat_to_bin and double_bin
  - A lemma about the relationship between normalize and double_bin

  Breaking down the proof into smaller steps and proving these relationships
  individually will make the main theorem more manageable.
  -/
  sorry
