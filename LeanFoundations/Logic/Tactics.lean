/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/


/-!
# More Basic Tactics
We are going to lean more tactics. We first inspect more on the *implications*.
Then, we move to how to prove and make use of conjuction and disjuncitons. Then,
we discuss the injection and discrimination on inductive types. Finally,
we look at tactics on hypothesis and unfolding, and other useful tactics.
-/

/-!
## Implications and Tactic Apply
We first look at the *implications*. Recall that in Lean, we prove
things by [fulfilling the goal under certain *context*](LeanFoundations.Logic.Basic.html#Proofs).
Basically, an *implication* means a proposition with a condition, i.e.,
a proposition of the form *if `A` then `B`*, written as `A -> B` in Lean. We call
`A` the antecedent (condition) and `B` the consequent (conclusion) of `A -> B`.
As we learned before, to prove such a `theorem` in Lean, we `intro` the
antecedent `A` into the *context*, and try to fulfil goal `B`.
Here, we have to two questions:
1. How to yield the `A -> B`, or how to yield `B` under the *context* `A`;
2. How to make use of the implication `A -> B`.

For the first question, we have already seen some special situations, for example
if `B` is already in the context.
-/
example: forall n: Nat, n = n -> n = n := by
  intro n
  intro H
  -- Now, the gaol is already in the context
  exact H

/-!
Or, `B` is some silly fact.
-/
example: 1 = 2 -> 0 = 0 := by
  intro H
  eq_refl

/-!
You can also add more unnecessary conditions (recall `->` is right
associative just like *curried functions*)
-/
example:
  1 = 2 ->
  3 = 4 ->
  7 = 8 ->
  0 = 0
:= by
  -- you can introduce them with `intro`,
  intro H1
  -- or with one `intros` to bring in them all if you don't care the names.
  intros
  eq_refl

/-!
For the second, we look at a simplest case. If we know `A` and `A -> B`,
certainly, we shall know `B`. The idea behind it is that to get the `B`,
we will *apply* `A -> B`, and then the goal is turned to `A`, and we
want to prove `A`.
-/
theorem ModusPones: forall A B: Prop,  -- indicating we are dealing with propositions
  A ->
  (A -> B) ->
  B
:= by
  intro A B  -- We bring A B into premises.
  intro HA HAB  -- Then, we have two facts: `A` and `A -> B`.
  apply HAB  -- This turns the goal into `A`.
  apply HA  -- And `A` is already known.

/-!
> Note that we can use `exact` instead of `apply`. The only difference is
> that `exact` can only be the last tactic (it must conclude the proof) and
> the conclusion is already in the context.

We then look at how to make use of the theorem `ModusPones`. Let's think
about a proof that if `1 = 2` and `1 = 2 -> 3 = 4`, then `3 = 4`, i.e., a
proposition `1 = 2 -> (1 = 2 -> 3 = 4) -> 3 = 4`. This is exactly of the form
`ModusPones`. Just like functions, we can **specialize** it by specify
`A := 1 = 2` and `B := 3 = 4`.
-/

#check (ModusPones (A := 1 = 2) (B := 3 = 4))

/-!
Or, you can omit the names and Lean will fill in the parameters in order.
-/
#check (ModusPones (A := 1 = 2) (3 = 4))
#check (ModusPones (1 = 2) (3 = 4))

/-!
Thus, to prove the proposition, we first `intro` `H1: 1 = 2` and `H2: 3 = 4`,
and apply `(ModusPones (A := 1 = 2) (B := 3 = 4))`. This time, since we have
two *conditions*, after the application, we will have two goals. We use
`.` to list their proofs respectively.
-/

example:
  1 = 2 ->
  (1 = 2 -> 3 = 4) ->
  3 = 4
:= by
  intros H1 H2
  apply ModusPones (A := 1 = 2) (B := 3 = 4)
  . apply H1
  . apply H2

/-!
You may also want to ask that since the *specialized* `ModusPones` is exactly
the goal we want to prove, can we use it directly? The answer is affirmative.
-/

example:
  1 = 2 ->
  (1 = 2 -> 3 = 4) ->
  3 = 4
:= by
  exact ModusPones (A := 1 = 2) (B := 3 = 4)

/-!
### Proof? Term?
So, we have another syntactic sugar to save our lives? Not quite. In Lean,
`Prop` is a special type universe to collect all propositions and each
proposition is considered as a special *type* whose terms can be made by
those *tactics*. The goal is the *type* you want to find a term of and
tactics allows you to yield such a term or change the goal, though you may
not know how it works for now. Instead of *terms* and *types*, let's say
*proofs* and *propsitions* just for `theorem`s for a while.

In our case, `forall A B: Prop, A -> (A -> B) -> B` is a proposition (type)
in the universe `Prop`, and we have found a proof (term) `ModusPones` of this
type. We still use the `:` notation to indicate the proof and its proposition.

Like terms, we can manipulate proofs in order to make new proofs of new
propositions and fulfil the goal. The specialization
`ModusPones (A := 1 = 2) (B := 3 = 4)` yields a proof of
`1 = 2 -> (1 = 2 -> 3 = 4) -> 3 = 4`. `apply` uses it turns the goal into
`1 = 2` and `1 = 2 -> 3 = 4`. `intro` brings in conditions and allows you
write a more intuitive proof.

In fact, both `term: type` and `proof: proposition` shares the same judging
system, known as [Curry-Howard correspondence][sorensen2006lectures].
We will reveal that later. Let's look at an intermediate example.
-/

example:
  1 = 2 ->
  (1 = 2 -> 3 = 4) ->
  3 = 4
:= by
  intro H1
  apply ModusPones (A := 1 = 2) (B := 3 = 4)
  exact H1

/-!
This time, we only `intro` `H1` and it works similarly.
-/

/-!
### Type Inference and Early Application
Another notable thing is that `apply` will try to figure out the type
(proposition) such as those after the quantifiers. For example, if
we want to apply `ModusPones` to `(1 = 2 -> 3 = 4) -> 3 = 4`, then
`A` must be `1 = 2` and `B` must be `3 = 4`. There is no need to specify
them.
-/

example:
  1 = 2 ->
  (1 = 2 -> 3 = 4) ->
  3 = 4
:= by
  intro H1
  apply ModusPones
  exact H1

/-!
The situation will be a bit different if you `intro` both `H1` and `H2`, then
`apply` will not know what to choose for `A`. In the context you can observe
an `?A`. Sometimes you may not know everything of an application, you have
to apply it early and try to figure it later. In our situation, `A` is inferred
from the next tactic `exact H1`, so we don't need to write the full speclization.
-/
example:
  1 = 2 ->
  (1 = 2 -> 3 = 4) ->
  3 = 4
:= by
  intro H1 H2
  apply ModusPones  -- We have an `?A` in the context.
  . exact H1
  . exact H2


/-!
And `apply` is even more powerful, you can just write the following.
-/
example:
  1 = 2 ->
  (1 = 2 -> 3 = 4) ->
  3 = 4
:= by
  apply ModusPones


/-!
### Proofs inside Proofs
As you may imagine, we may have a very complicated implicational proof. For
example, `A -> (A -> B) -> (B -> C) -> (B -> D) -> (B -> C -> D -> E) -> E`.
Certainly, you can prove it just with `apply` and `intro`.
-/

example (A B C D E: Prop):
  A ->
  (A -> B) ->
  (B -> C) ->
  (B -> D) ->
  (B -> C -> D -> E) ->
  E
:= by
  intro Ha Hab Hbc Hbd Hbcde
  apply Hbcde
  . -- B
    apply Hab
    exact Ha
  . -- C
    apply Hbc
    apply Hab
    exact Ha
  . -- D
    apply Hbd
    apply Hab
    apply Ha


/-!
The thing is that the proof of `B` is repeated may times. We want to `have`
the proof of `B` during the whole proof. Lean provides two syntactic sugars
for that, one is `have`, which allows you prove some facts inside a large
proof. The other is `let`, this is a bit like `giving a name to some term`.
Both will introduce corresponding terms into the context and you can then
make use of them.
-/

example (A B C D E: Prop):
  A ->
  (A -> B) ->
  (B -> C) ->
  (B -> D) ->
  (B -> C -> D -> E) ->
  E
:= by
  intro Ha Hab Hbc Hbd Hbcde
  have Hb: B := by
    apply Hab
    exact Ha
  -- Now, you can see a new entry `Hb: B` in the context.
  let Hb' := Hab Ha -- Similarly, this will add `Hb': B`

  -- You can use it as an ordinary variable.
  apply Hbcde Hb
  . -- C
    apply Hbc
    exact Hb
  . -- D
    apply Hbd
    exact Hb


/-!
## Conjuctions and Disjunctions
Our next target is conjuctions (and) and disjunctions (or). From the previous
section, we can find that to make an *implication*, we first `intro` its antecedent
into the context and prove the consequent; if we want to make use of it, we
`apply` it and prove the antecedent. This shows the general principles of
dealing with logical connectives:
- Introduction rule: given two propositions, how to make a new proposition from
  the connective.
- Construction rule: in order to prove a proposition made of this connective, what
  tactics we shall use.
- Elimination rule: given such a proposition, how to use it to prove other things,
  i.e., how to remove the connective to get new proofs.
-/

/-!
### Conjuction
Here, we use `And(∧)` as an example to explain that. Sometimes, we may want to
prove talk about two facts, e.g., `1 = 1 ∧ 2 = 2`. Two propositions `1 = 1` and
`2 = 2` are connected by an `∧`. Or equivalently, you can use `And (1 = 1) (2 = 2)`.
This shows us the *introduction rule*: `And` takes two propositions and yields
another. You can think of that as a function of type `Prop -> Prop -> Prop`.
-/
#check And  -- And (a b : Prop) : Prop

/-!
Then, we ask how to prove `1 = 1 ∧ 2 = 2`. Intuitively, to prove an `And` of
`A` and `B`, we have to prove both `A` and `B`. This is the *construction
rule*, which can be considered as a function of type `A -> B -> A ∧ B`.
Lean provides a term `And.intro` for it, and it is called the *constructor*.
-/

#check And.intro

/-!
Then, we can simply use `apply And.intro` to change our goals to `A` and
`B` and prove them respectively.

> Hint: use `.` to separate different proofs of different goals as before.
-/

example: 1 = 1 ∧ 2 = 2 := by
  apply And.intro
  . eq_refl
  . eq_refl


/-!
If you don't remember the exact name of the constructor, Lean also provides
a tactics called `constructor`, which will try all available constructors to
fulfill the goal.
-/

example: 1 = 1 ∧ 2 = 2 := by
  constructor
  . eq_refl
  . eq_refl


/-!
As you may have thought, we next deal with the elimination rule, i.e., how
to make prove out of a conjunction. The answer is quite simple: given
`c: A ∧ B`, we naturally have `c.left: A` and `c.right: B`. They are called
*projections*.

> The real eliminators are the *inductive principles* of types. We will talk
> about them later.
-/

#check And.left  -- ∀ {a b : Prop}, a ∧ b → a
#check And.right  -- ∀ {a b : Prop}, a ∧ b → b


example: 1 = 2 ∧ 2 = 2 -> 1 = 2 := by
  intro c
  exact c.left

/-!
You may wonder why we need the conjunctions, since they seems to be a syntactic
sugar to organize two facts. The answer is that sometimes we need to express
complicated things in a proof.

> Note that `∧` is prior to `->`.
-/

example (A B C: Prop): (A -> B ∧ C) -> (A -> B) ∧ (A -> C) := by
  intros c
  constructor  -- split the goals
  . -- A -> B
    intros a
    exact (c a).left
  . -- A -> C
    intros a
    exact (c a).right


/-!
### Exercises
-/

example (A B C: Prop): (A -> B) ∧ (A -> C) -> (A -> B ∧ C) := by
  admit

example (A B C: Prop): (A -> B -> C) -> (A ∧ B -> C) := by
  admit

example (A B C: Prop): (A ∧ B -> C) -> (A -> B -> C) := by
  admit

/-!
### If and Only If
-/

/-!
### Disjuction
-/


/-!
elimination rule of `∨`: forall {A B C}, (A -> C) -> (B -> C) -> (A ∨ B -> C)
-/

/-!
## Injection and Discrimination

Recall the definition of Nat
```lean
inductive Nat where
  | zero | succ
```
-/

namespace scratch

theorem Nat.succ_inj {a b: Nat}: a.succ = b.succ -> a = b := by
  intro H1
  have H2: a = a.succ.pred := by
    eq_refl
  rewrite [H2]
  rewrite [H1]
  eq_refl

end scratch


/-!
## Falsehood and Negation
-/

/-!
## Existential Quantification
-/

/-!
## Tactics on Hypotheses
-/

/-!
## Unfolding
-/
