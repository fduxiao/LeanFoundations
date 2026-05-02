/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George
-/

/-!
# Logic in Lean

We have now seen many examples of factual claims (propositions) and ways of presenting
evidence of their truth (proofs). In particular, we have worked extensively with
equality propositions (e1 = e2), implications (P → Q), and quantified propositions
(∀ x, P). In this chapter, we will see how Lean can be used to carry out other
familiar forms of logical reasoning.
-/

namespace Logic

/-!
Before diving into details, we should talk a bit about the status of mathematical
statements in Lean. Recall that Lean is a typed language, which means that every
sensible expression has an associated type. Logical claims are no exception: any
statement we might try to prove in Lean has a type, namely `Prop`, the type of
propositions. We can see this with the `#check` command:
-/

#check (∀ n m : Nat, n + m = m + n) -- : Prop

/-!
Note that all syntactically well-formed propositions have type `Prop` in Lean,
regardless of whether they are true or not.

Simply being a proposition is one thing; being provable is a different thing!
-/

#check 2 = 2 -- : Prop
#check 3 = 2 -- : Prop
#check ∀ n : Nat, n = 2 -- : Prop

/-!
Indeed, propositions don't just have types -- they are first-class entities that
can be manipulated in all the same ways as any of the other things in Lean's world.

So far, we've seen one primary place where propositions can appear: in `theorem`
(and `example`) declarations.
-/

theorem plus_2_2_is_4 : 2 + 2 = 4 := by rfl

/-!
But propositions can be used in other ways. For example, we can give a name to a
proposition using a `def`, just as we give names to other kinds of expressions.
-/

def plus_claim : Prop := 2 + 2 = 4

#check plus_claim -- : Prop

/-!
We can later use this name in any situation where a proposition is expected --
for example, as the claim in a `theorem` declaration.
-/

theorem plus_claim_is_true : plus_claim := by rfl

/-!
We can also write parameterized propositions -- that is, functions that take
arguments of some type and return a proposition.

For instance, the following function takes a number and returns a proposition
asserting that this number is equal to three:
-/

def is_three (n : Nat) : Prop := n = 3

#check is_three -- : Nat → Prop

/-!
In Lean, functions that return propositions are said to define properties of their arguments.

For instance, here's a (polymorphic) property defining the familiar notion of an
injective function.
-/

def injective {A B : Type} (f : A → B) : Prop :=
  ∀ x y : A, f x = f y → x = y

theorem succ_inj : injective Nat.succ := by
  intros x y h
  cases h
  rfl

/-!
The familiar equality operator `=` is a (binary) function that returns a `Prop`.

Because `=` can be used with elements of any type, it is also polymorphic:
-/

#check @Eq -- : {α : Sort u_1} → α → α → Prop

/-!
## Logical Connectives

### Conjunction

The conjunction, or logical and, of propositions A and B is written `A ∧ B`; it
represents the claim that both A and B are true.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  -- To prove a conjunction, use the `constructor` tactic or `⟨_, _⟩` syntax.
  -- This will generate two subgoals, one for each part of the statement:
  constructor
  · -- 3 + 4 = 7
    rfl
  · -- 2 * 2 = 4
    rfl

/-!
For any propositions A and B, if we assume that A is true and that B is true,
we can conclude that A ∧ B is also true. Lean's library provides a constructor
`And.intro` that does this:
-/

#check @And.intro -- : {a b : Prop} → a → b → a ∧ b

/-!
Since applying a theorem with hypotheses to some goal has the effect of generating
as many subgoals as there are hypotheses for that theorem, we can apply `And.intro`
to achieve the same effect as `constructor`.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · -- 3 + 4 = 7
    rfl
  · -- 2 * 2 = 4
    rfl

/-!
**Exercise: 2 stars, standard (plus_is_O)**
-/

/-!
**Exercise: 2 stars, standard (plus_is_O)**
-/

example (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  sorry

/-!
So much for proving conjunctive statements. To go in the other direction -- i.e.,
to use a conjunctive hypothesis to help prove something else -- we employ
destructuring patterns.

When the current proof context contains a hypothesis H of the form `A ∧ B`, we can
destructure it using pattern matching or the `cases` tactic to get two new hypotheses:
one stating that A is true, and another stating that B is true.
-/

theorem and_example2 (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro h
  cases h with
  | intro hn hm =>
    rw [hn, hm]

/-!
As usual, we can also destructure H right when we introduce it, instead of
introducing and then destructuring it:
-/

theorem and_example2' (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]

/-!
You may wonder why we bothered packing the two hypotheses `n = 0` and `m = 0`
into a single conjunction, since we could also have stated the theorem with two
separate premises:
-/

theorem and_example2'' (n m : Nat) : n = 0 → m = 0 → n + m = 0 := by
  intros hn hm
  rw [hn, hm]

/-!
For this specific theorem, both formulations are fine. But it's important to
understand how to work with conjunctive hypotheses because conjunctions often
arise from intermediate steps in proofs, especially in larger developments.
Here's a simple example:
-/

theorem and_example3 (n m : Nat) : n + m = 0 → n * m = 0 := by
  intro h
  -- We need to show that if n + m = 0, then at least one of n or m is 0
  cases n with
  | zero => simp
  | succ n' =>
    simp at h

/-!
Another common situation is that we know `A ∧ B` but in some context we need
just A or just B. In such cases we can use projection functions.
-/

theorem proj1 (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1

/-!
**Exercise: 1 star, standard, optional (proj2)**
-/

theorem proj2 (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.2

/-!
Finally, we sometimes need to rearrange the order of conjunctions and/or the
grouping of multi-way conjunctions. We can see this at work in the proofs of
the following commutativity and associativity theorems:
-/

theorem and_commut (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  constructor
  · -- left
    exact hq
  · -- right
    exact hp

/-!
Finally, the infix notation `∧` is actually just syntactic sugar for `And A B`.
That is, `And` is a Lean constructor that takes two propositions as arguments
and yields a proposition.
-/

#check And -- : Prop → Prop → Prop

/-!
### Disjunction

Another important connective is the disjunction, or logical or, of two propositions:
`A ∨ B` is true when either A or B is. (This infix notation stands for `Or A B`,
where `Or : Prop → Prop → Prop`.)

To use a disjunctive hypothesis in a proof, we proceed by case analysis -- which,
as with other data types like Nat, can be done explicitly with `cases` or implicitly
with pattern matching:
-/

theorem factor_is_O (n m : Nat) : n = 0 ∨ m = 0 → n * m = 0 := by
  -- This pattern implicitly does case analysis on n = 0 ∨ m = 0
  intro h
  cases h with
  | inl hn =>
    -- Here, n = 0
    rw [hn]
    simp
  | inr hm =>
    -- Here, m = 0
    rw [hm]
    simp

/-!
We can see in this example that, when we perform case analysis on a disjunction
`A ∨ B`, we must separately discharge two proof obligations, each showing that
the conclusion holds under a different assumption -- A in the first subgoal and
B in the second.

Conversely, to show that a disjunction holds, it suffices to show that one of
its sides holds. This can be done via the `left` and `right` tactics. As their
names imply, the first one requires proving the left side of the disjunction,
while the second requires proving the right side. Here is a trivial use:
-/

theorem or_intro_l (A B : Prop) : A → A ∨ B := by
  intro ha
  left
  exact ha

/-!
... and here is a slightly more interesting example requiring both `left` and `right`:
-/

theorem zero_or_succ (n : Nat) : n = 0 ∨ n = Nat.succ (Nat.pred n) := by
  cases n with
  | zero =>
    left
    rfl
  | succ n' =>
    right
    rfl

/-!
**Exercise: 2 stars, standard (mult_is_O)**
-/

theorem mult_is_O (n m : Nat) : n * m = 0 → n = 0 ∨ m = 0 := by
  sorry

/-!
**Exercise: 1 star, standard (or_commut)**
-/

theorem or_commut (P Q : Prop) : P ∨ Q → Q ∨ P := by
  sorry

/-!
### Falsehood and Negation

Up to this point, we have mostly been concerned with proving "positive" statements --
addition is commutative, appending lists is associative, etc. Of course, we are
sometimes also interested in negative results, demonstrating that some given
proposition is not true. Such statements are expressed with the logical negation
operator `¬`.

To see how negation works, recall the principle of explosion from earlier chapters,
which asserts that, if we assume a contradiction, then any other proposition can
be derived.

Following this intuition, we could define `¬ P` ("not P") as `∀ Q, P → Q`.

Lean actually makes a slightly different (but equivalent) choice, defining `¬ P`
as `P → False`, where `False` is a specific un-provable proposition defined in
the standard library.
-/

#check Not -- : Prop → Prop
#check @False -- : Prop

/-!
Since `False` is a contradictory proposition, the principle of explosion also
applies to it. If we can get `False` into the context, we can use `False.elim`
on it to complete any goal:
-/

theorem ex_falso_quodlibet (P : Prop) : False → P := by
  intro contra
  exact False.elim contra

/-!
The Latin "ex falso quodlibet" means, literally, "from falsehood follows whatever
you like"; this is another common name for the principle of explosion.

**Exercise: 2 stars, standard, optional (not_implies_our_not)**

Show that Lean's definition of negation implies the intuitive one mentioned above.
-/

theorem not_implies_our_not (P : Prop) : ¬ P → (∀ (Q : Prop), P → Q) := by
  intro hnp Q hp
  exact False.elim (hnp hp)

/-!
Inequality is a very common form of negated statement, so there is a special
notation for it:
-/

#check (0 ≠ 1) -- equivalent to ¬(0 = 1)

/-!
For example:
-/

theorem zero_not_one : 0 ≠ 1 := by
  -- The proposition 0 ≠ 1 is exactly the same as ¬(0 = 1) -- that is,
  -- Not (0 = 1) -- which unfolds to (0 = 1) → False.
  intro contra
  -- ... and deduce a contradiction from it. Here, the equality 0 = 1 contradicts
  -- the disjointness of constructors, so `cases` takes care of it.
  cases contra

/-!
It takes a little practice to get used to working with negation in Lean. Even
though you can see perfectly well why a statement involving negation is true,
it can be a little tricky at first to see how to make Lean understand it!

Here are proofs of a few familiar facts to help get you warmed up.
-/

theorem not_False : ¬ False := by
  intro h
  exact h

theorem contradiction_implies_anything (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro ⟨hp, hnp⟩
  exact False.elim (hnp hp)

theorem double_neg (P : Prop) : P → ¬¬P := by
  intro hp hnp
  exact hnp hp

/-!
**Exercise: 2 stars, advanced (double_neg_informal)**

Write an informal proof of double_neg:

Theorem: P implies ¬¬P, for any proposition P.

Proof: Assume P holds. We want to show ¬¬P, which means ¬P → False.
So assume ¬P. But we have P from our assumption and ¬P from this assumption,
so we have a contradiction. From False we can derive anything, completing the proof. □
-/

/-!
**Exercise: 1 star, standard, especially useful (contrapositive)**
-/

theorem contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  sorry

/-!
**Exercise: 1 star, standard (not_both_true_and_false)**
-/

theorem not_both_true_and_false (P : Prop) : ¬ (P ∧ ¬P) := by
  sorry

/-!
**Exercise: 2 stars, standard (de_morgan_not_or)**

De Morgan's Laws, named for Augustus De Morgan, describe how negation interacts
with conjunction and disjunction. The following law says that "the negation of
a disjunction is the conjunction of the negations."
-/

theorem de_morgan_not_or (P Q : Prop) : ¬ (P ∨ Q) → ¬P ∧ ¬Q := by
  sorry

/-!
Since inequality involves a negation, it also requires a little practice to be
able to work with it fluently. Here is one useful trick.

If you are trying to prove a goal that is nonsensical (e.g., the goal state is
`False`), apply `False.elim` to change the goal to `False`.

This makes it easier to use assumptions of the form `¬P` that may be available
in the context -- in particular, assumptions of the form `x ≠ y`.
-/

theorem not_true_is_false (b : Bool) : b ≠ true → b = false := by
  cases b with
  | true =>
    intro h
    -- b = true but we have b ≠ true, contradiction
    exact False.elim (h rfl)
  | false =>
    intro h
    rfl

/-!
### Truth

Besides `False`, Lean's standard library also defines `True`, a proposition that
is trivially true. To prove it, we use the constant `True.intro`:
-/

theorem True_is_true : True := True.intro

/-!
Unlike `False`, which is used extensively, `True` is used relatively rarely,
since it is trivial (and therefore uninteresting) to prove as a goal, and
conversely it provides no interesting information when used as a hypothesis.

However, `True` can be quite useful when defining complex `Prop`s using conditionals
or as a parameter to higher-order `Prop`s.

### Logical Equivalence

The handy "if and only if" connective, which asserts that two propositions have
the same truth value, is simply the conjunction of two implications.
-/

#check Iff -- : Prop → Prop → Prop

-- P ↔ Q is notation for Iff P Q, which is defined as (P → Q) ∧ (Q → P)

theorem iff_sym (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  intro ⟨hab, hba⟩
  constructor
  · -- →
    exact hba
  · -- ←
    exact hab

theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · -- →
    exact not_true_is_false b
  · -- ←
    intro h
    rw [h]
    simp

/-!
We can also use `apply` with an `↔` in either direction, without explicitly
thinking about the fact that it is really an and underneath.
-/

theorem apply_iff_example1 (P Q R : Prop) : (P ↔ Q) → (Q → R) → (P → R) := by
  intros hiff h hp
  exact h (hiff.mp hp)

theorem apply_iff_example2 (P Q R : Prop) : (P ↔ Q) → (P → R) → (Q → R) := by
  intros hiff h hq
  exact h (hiff.mpr hq)

/-!
**Exercise: 1 star, standard, optional (iff_properties)**

Using the above proof that `↔` is symmetric (`iff_sym`) as a guide, prove that
it is also reflexive and transitive.
-/

theorem iff_refl (P : Prop) : P ↔ P := by
  constructor
  · intro h; exact h
  · intro h; exact h

theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros h1 h2
  cases h1 with
  | intro hpq hqp =>
    cases h2 with
    | intro hqr hrq =>
      constructor
      · intro hp
        exact hqr (hpq hp)
      · intro hr
        exact hqp (hrq hr)

/-!
**Exercise: 3 stars, standard (or_distributes_over_and)**
-/

theorem or_distributes_over_and (P Q R : Prop) :
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      constructor
      · left; exact hp
      · left; exact hp
    | inr h_qr =>
      cases h_qr with
      | intro hq hr =>
        constructor
        · right; exact hq
        · right; exact hr
  · intro h
    cases h with
    | intro h1 h2 =>
      cases h1 with
      | inl hp => left; exact hp
      | inr hq =>
        cases h2 with
        | inl hp => left; exact hp
        | inr hr => right; constructor; exact hq; exact hr

/-!
### Existential Quantification

Another basic logical connective is existential quantification. To say that there
is some x of type T such that some property P holds of x, we write `∃ x : T, P`.
As with `∀`, the type annotation `: T` can be omitted if Lean is able to infer
from the context what the type of x should be.

To prove a statement of the form `∃ x, P`, we must show that P holds for some
specific choice for x, known as the witness of the existential. This is done in
two steps: First, we explicitly tell Lean which witness t we have in mind by
invoking the tactic `use t`. Then we prove that P holds after all occurrences
of x are replaced by t.
-/

def Even (x : Nat) := ∃ n : Nat, x = 2 * n

#check Even -- : Nat → Prop

theorem four_is_Even : Even 4 := by
  exists 2

/-!
Conversely, if we have an existential hypothesis `∃ x, P` in the context, we can
destructure it to obtain a witness x and a hypothesis stating that P holds of x.
-/

theorem exists_example_2 (n : Nat) : (∃ m, n = 4 + m) → (∃ o, n = 2 + o) := by
  intro h
  cases h with
  | intro m hm =>
    exists 2 + m
    rw [hm]
    rw [← Nat.add_assoc]

/-!
**Exercise: 1 star, standard, especially useful (dist_not_exists)**

Prove that "P holds for all x" implies "there is no x for which P does not hold."
-/

theorem dist_not_exists (X : Type) (P : X → Prop) :
  (∀ x, P x) → ¬ (∃ x, ¬ P x) := by
  sorry

/-!
**Exercise: 2 stars, standard (dist_exists_or)**

Prove that existential quantification distributes over disjunction.
-/

theorem dist_exists_or (X : Type) (P Q : X → Prop) :
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

/-!
## Programming with Propositions

The logical connectives that we have seen provide a rich vocabulary for defining
complex propositions from simpler ones. To illustrate, let's look at how to express
the claim that an element x occurs in a list l. Notice that this property has a
simple recursive structure:

- If l is the empty list, then x cannot occur in it, so the property "x appears in l" is simply false.
- Otherwise, l has the form `x' :: l'`. In this case, x occurs in l if it is equal to x' or if it occurs in l'.

We can translate this directly into a straightforward recursive function taking
an element and a list and returning a proposition (!):
-/

def List.mem {A : Type} (x : A) (l : List A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x ∨ List.mem x l'

/-!
When `List.mem` is applied to a concrete list, it expands into a concrete sequence
of nested disjunctions.
-/

example : List.mem 4 [1, 2, 3, 4, 5] := by
  simp [List.mem]

example (n : Nat) : List.mem n [2, 4] → ∃ n', n = 2 * n' := by
  sorry

/-!
We can also reason about more generic statements involving `List.mem`.
-/

theorem mem_map {A B : Type} (f : A → B) (l : List A) (x : A) :
  List.mem x l → List.mem (f x) (List.map f l) := by
  intro h
  induction l with
  | nil =>
    simp [List.mem] at h
  | cons x' l' ih =>
    simp [List.mem] at h ⊢
    cases h with
    | inl h =>
      left
      rw [h]
    | inr h =>
      right
      exact ih h

/-!
**Exercise: 2 stars, standard (mem_map_iff)**
-/

theorem mem_map_iff {A B : Type} (f : A → B) (l : List A) (y : B) :
  List.mem y (List.map f l) ↔ ∃ x, f x = y ∧ List.mem x l := by
  sorry

/-!
**Exercise: 2 stars, standard (mem_app_iff)**
-/

theorem mem_app_iff {A : Type} (l l' : List A) (a : A) :
  List.mem a (l ++ l') ↔ List.mem a l ∨ List.mem a l' := by
  sorry

/-!
**Exercise: 3 stars, standard, especially useful (All)**

We noted above that functions returning propositions can be seen as properties
of their arguments. For instance, if P has type `Nat → Prop`, then `P n` says
that property P holds of n.

Drawing inspiration from `List.mem`, write a recursive function `All` stating that
some property P holds of all elements of a list l. To make sure your definition
is correct, prove the `All_mem` theorem below.
-/

def All {T : Type} (P : T → Prop) (l : List T) : Prop :=
  sorry

theorem All_mem {T : Type} (P : T → Prop) (l : List T) :
  (∀ x, List.mem x l → P x) ↔ All P l := by
  sorry

/-!
**Exercise: 2 stars, standard, optional (combine_odd_even)**

Complete the definition of combine_odd_even below. It takes as arguments two
properties of numbers, Podd and Peven, and it should return a property P such
that P n is equivalent to Podd n when n is odd and equivalent to Peven n otherwise.
-/

def combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop :=
  sorry

/-!
To test your definition, prove the following facts:
-/

theorem combine_odd_even_intro (Podd Peven : Nat → Prop) (n : Nat) :
  (n % 2 = 1 → Podd n) →
  (n % 2 = 0 → Peven n) →
  combine_odd_even Podd Peven n := by
  sorry

theorem combine_odd_even_elim_odd (Podd Peven : Nat → Prop) (n : Nat) :
  combine_odd_even Podd Peven n →
  n % 2 = 1 →
  Podd n := by
  sorry

theorem combine_odd_even_elim_even (Podd Peven : Nat → Prop) (n : Nat) :
  combine_odd_even Podd Peven n →
  n % 2 = 0 →
  Peven n := by
  sorry

/-!
## Applying Theorems to Arguments

One feature that distinguishes Lean from some other popular proof assistants
is that it treats proofs as first-class objects.

We have seen that we can use `#check` to ask Lean to check whether an expression
has a given type:
-/

#check Nat.add -- : Nat → Nat → Nat

/-!
We can also use it to check the theorem a particular identifier refers to:
-/

#check Nat.add_comm -- : ∀ (n m : Nat), n + m = m + n

/-!
Lean checks the statements of theorems in the same way that it checks the type
of any term. If we leave off the colon and type, Lean will print these types for us.

The reason is that theorems actually refer to proof objects -- logical derivations
establishing the truth of the statement. The type of this object is the proposition
that it is a proof of.

If we have a term of type `Nat → Nat → Nat`, we can give it two nats as arguments
and get a nat back. Similarly, the statement of a theorem tells us what we can
use that theorem for.

If we have a term of type `∀ n m, n = m → n + n = m + m` and we provide it two
numbers n and m and a third "argument" of type `n = m`, we can derive `n + n = m + m`.

Operationally, this analogy goes even further: by applying a theorem as if it
were a function, we can specialize its result without having to resort to
intermediate assertions. For example, suppose we wanted to prove the following result:
-/

theorem add_comm3 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm y z]
  rw [Nat.add_comm x (z + y)]

/-!
Here's another example of using a theorem like a function. The theorem says:
if a list l contains some element x, then l must be nonempty.
-/

theorem in_not_nil {A : Type} (x : A) (l : List A) :
  List.mem x l → l ≠ [] := by
  intro h
  cases l with
  | nil =>
    simp [List.mem] at h
  | cons a l' =>
    intro contra
    cases contra

/-!
## Working with Decidable Properties

We've seen two different ways of expressing logical claims in Lean: with booleans
(of type `Bool`), and with propositions (of type `Prop`).

Here are the key differences between `Bool` and `Prop`:

                                           Bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes

The crucial difference between the two worlds is decidability. Every (closed)
Lean expression of type `Bool` can be simplified in a finite number of steps
to either `true` or `false`.

By contrast, the type `Prop` includes both decidable and undecidable mathematical
propositions.

Since `Prop` includes both decidable and undecidable properties, we have two
options when we want to formalize a property that happens to be decidable: we
can express it either as a boolean computation or as a function into `Prop`.

For example, we can express evenness either as a boolean test:
-/

def even_b (n : Nat) : Bool := n % 2 = 0

example : even_b 42 = true := by rfl

/-!
... or as a proposition:
-/

example : Even 42 := by
  exists 21

/-!
Of course, it would be pretty strange if these two characterizations of evenness
did not describe the same set of natural numbers!
-/

theorem even_bool_prop (n : Nat) : even_b n = true ↔ Even n := by
  constructor
  · intro h
    simp [even_b] at h
    exists n / 2
    sorry -- This requires more advanced number theory
  · intro h
    cases h with
    | intro k hk =>
      simp [even_b]
      rw [hk]
      simp

/-!
Similarly, to state that two numbers n and m are equal, we can say either
(1) that `n == m` returns true, or
(2) that `n = m`.

Again, these two notions are equivalent:
-/

theorem beq_nat_true_iff (n m : Nat) : (n == m) = true ↔ n = m := by
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp [h]

/-!
## Classical vs. Constructive Logic

We have seen that it is not possible to test whether or not a proposition P
holds while defining a Lean function. A similar restriction applies in proofs!
The following intuitive reasoning principle is not derivable in Lean:
-/

def excluded_middle := ∀ P : Prop, P ∨ ¬ P

/-!
To understand operationally why this is the case, recall that, to prove a
statement of the form `P ∨ Q`, we use the `left` and `right` tactics, which
effectively require knowing which side of the disjunction holds. But the
universally quantified P in excluded_middle is an arbitrary proposition,
which we know nothing about.

However, if we happen to know that P is reflected in some boolean term b,
knowing whether it holds or not is trivial:
-/

theorem restricted_excluded_middle (P : Prop) (b : Bool) :
  (P ↔ b = true) → P ∨ ¬ P := by
  intro h
  cases b with
  | true =>
    left
    rw [h]
  | false =>
    right
    rw [h]
    intro contra
    cases contra

/-!
In particular, the excluded middle is valid for equations `n = m` between
natural numbers n and m:
-/

theorem restricted_excluded_middle_eq (n m : Nat) : n = m ∨ n ≠ m := by
  apply restricted_excluded_middle (n = m) (n == m)
  exact (beq_nat_true_iff n m).symm

/-!
It may seem strange that the general excluded middle is not available by
default in Lean, since it is a standard feature of familiar logics like ZFC.
But there is a distinct advantage in not assuming the excluded middle:
statements in Lean make stronger claims than the analogous statements in
standard mathematics.

Notably, a Lean proof of `∃ x, P x` always includes a particular value of x
for which we can prove `P x` -- in other words, every proof of existence is
constructive.

Logics like Lean's, which do not assume the excluded middle, are referred to
as constructive logics.

More conventional logical systems such as ZFC, in which the excluded middle
does hold for arbitrary propositions, are referred to as classical.
-/

-- The end of the main content
