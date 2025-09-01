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

In This chapter we are going to inspect _binary relations_ on a type. In mathematics, a binary
relation is to associate two elements of a set. In set theory, we model such a relation $R$ on a set
$X$ to be a subset $R \subseteq X\times X$. Thus, if two elements $x,y\in X$ are associated, we say
$R x y$, which means $(x, y) \in R$. Some typical relations are equalities, the _le_ (less than or
equal to) relation on $\mathbb{N}$.
-/

/-!
## Relations as Propositions
Another perspective about relation is that given $x, y\in X$, you have to determine whether
$R x y$ holds or not, i.e., the relation is a family of propositions parameterized by two elements of
$X$ -- i.e., a proposition about pairs of elements of $X$. For instance, we've seen the
relation `le` on numbers.
-/

#check le

/-!
The relation `le` gives us a family of propositions: for any two numbers `n` and `m`, we have
the proposition `n ≤' m`, which may or may not be provable.

Hence, in Lean, we model relations on `X` as `X -> X -> Prop`.
> Recall that `abbrev` means you give an alias to some type, while `def` means you want to define
> a new.
-/

abbrev Relation (X: Type) := X -> X -> Prop

/-!
Since propositions are just objects in Lean, we can study the properties about relations. For
example, we can classify relations (as reflexive, transitive, etc.), prove theorem about them,
or make new relations upon them. And, you will see that typeclass will help a lot.
-/


/-!
## Basic Properties of Relations

We begin with some basic mathematical examples and shows some naive applications of typeclass.

### Partial Functions
A relation `R` on a set `X` is a *partial function* if, for every `x`, there is at most one `y`
such that `R x y` -- i.e., `R x y1` and `R x y2` together imply `y1 = y2`.
-/

class Relation.PartialFunction {X: Type} (R: Relation X): Prop where
  functional: forall x y1 y2, R x y1 -> R x y2 -> y1 = y2

/-!
For example, the `next_nat` relation is a partial function.
-/

inductive next_nat : Nat → Nat → Prop where
  | nn (n : Nat) : next_nat n (n + 1)

instance next_nat_partial_function : Relation.PartialFunction next_nat where
  functional := by
    intro x y1 y2 H1 H2
    cases H1 with
    | nn =>
      cases H2 with
      | nn =>
        -- We have next_nat x (x + 1) and next_nat x (x + 1)
        -- Therefore y1 = y2 = x + 1
        eq_refl

/-!
However, the `≤` relation on numbers is not a partial function.

### Exercise: 2 stars, standard, optional (le_not_a_partial_function)

Show that the `≤` relation on naturals is not a partial function.
-/

theorem le_not_a_partial_function : ¬ Relation.PartialFunction le := by
  intro H
  -- We'll show that le 0 0 and le 0 1, which would imply 0 = 1 by partial_function
  have H1 : le 0 0 := le.le_refl 0
  have H2 : le 0 1 := le.le_step 0 0 H1
  have : 0 = 1 := H.functional 0 0 1 H1 H2
  -- This is a contradiction
  cases this

/-!
## Common Kinds of Relations
We next talk about the tranditional classifications of relations such as reflexive ones,
transitive ones, etc.

> Lean has already provides us some pre-defined typeclasses, but this time,
> we will define our own typeclasses and syntactic sugar. Lean also provides its own
> ones like `rfl` or `symm`. Refer to the official documents of Lean if you are interested.

### Reflexive Relations
A relation `R` on a set `X` is *reflexive* if every element of `X` is related to itself.
A relation `R` on a set `X` is *irreflexive* if every element of `X` is not related to itself.
-/

class Reflexive {X} (P: Relation X) where
  refl: forall x: X, P x x

def Relation.refl {X: Type} {P: Relation X} [inst: Reflexive P]:
  forall {x: X}, P x x := inst.refl _  -- `_` is the placeholder, which is inferred automatically.

class Irreflexive {X} (P: Relation X) where
  irrefl: forall x: X, Not (P x x)

def Relation.irrefl {X: Type} {P: Relation X} [inst: Irreflexive P]:
  forall {x: X}, Not (P x x) := inst.irrefl _


/-!
For example, `le` is reflexive.
-/

instance le_reflexive: Reflexive le where
  refl := le.le_refl


example: 5 ≤' 5 := by
  apply Relation.refl


/-!
`Eq` is another example
-/

instance {X: Type}: Reflexive (Eq (α := X)) where
  refl := Eq.refl


/-!
<hr/>

Note that Lean provides us the `Std.Refl` typeclass:
-/
instance: Std.Refl le where
  refl := le.le_refl


/-!
It also provides the `rfl` tactic. But to use it, you have to
tag it with the attribute `refl`.
-/
@[refl] theorem le_refl: forall x, le x x := by
  apply le.le_refl

example: 5 ≤' 5 := by
  rfl

/-!
You can think of `rfl` as an alias to `apply Relation.refl`. We will learn
how to build our own tactic later. Besides, Lean also added a lot of automation
to `rfl`. In real-world programming, you may prefer `@[refl]`.
-/

/-!
### Transitive Relations
A relation `R` is *transitive* if `R a c` holds whenever `R a b` and `R b c` do.
-/

class Transitive {X} (P: Relation X) where
  trans: forall a b c: X, P a b -> P b c -> P a c

def Relation.trans {A: Type} {P: Relation A} [inst: Transitive P]:
  forall {a b c: A}, P a b -> P b c -> P a c := inst.trans _ _ _


/-!
> Lean provides a hetergeneous version `Trans`, a bit like the `HAdd` class. Check it
> if you are interested.

We still use the example of `le`.
-/
instance le_transitive: Transitive le where
  trans a b c := by
    intro Hab Hbc
    induction Hbc with
    | le_refl => exact Hab
    | le_step c' Hbc' ih =>
      apply le.le_step
      exact ih


/-!
So now, if you want to prove `3 ≤' 5`, you can use the transitivity, i.e., it suffices to
prove `3 ≤' 4` and `4 ≤' 5`, which are exactl a `le.le_step` followed by `le.le_refl`.
Note that this time we specify the intermediate value `b := 4`.
-/
example: 3 ≤' 5 := by
  apply Relation.trans (b := 4)  -- you can specify the intermediate value
  . apply le.le_step
    apply le.le_refl
  . apply le.le_step
    apply le.le_refl

/-!
You can also repeat `Relation.trans` in chain, and let Lean to figure out the
intermediate value. This suggests some kinds of automation of proof.
-/
example: 3 ≤' 6 := by
  apply Relation.trans  -- or let Lean to figure that out
  . apply le.le_step
    apply le.le_refl
  . apply Relation.trans
    . apply le.le_step
      apply le.le_refl
    . apply le.le_step
      apply le.le_refl

/-!
### Symmetric and Antisymmetric Relations
A relation `R` is *symmetric* if `R a b` implies `R b a`.
A relation `R` is *antisymmetric* if `R a b` and `R b a` together imply `a = b` -- that is,
if the only "cycles" in `R` are trivial ones.

> Lean provides us `Std.Antisymm` and @[symm].
-/

class Symmetric {X} (P: Relation X) where
  symm: forall x y: X, P x y -> P y x

def Relation.symm {X} {P: Relation X} [inst: Symmetric P]:
  forall {x y: X}, P x y -> P y x := inst.symm _ _


class Antisymmetric {X} (P: Relation X) where
  asymm: forall x y: X, P x y -> P y x -> x = y

def Relation.asymm {X} {P: Relation X} [inst: Antisymmetric P]:
  forall {x y: X}, P x y -> P y x -> x = y := inst.asymm _ _


/-!
### Exercise: 2 stars, standard, optional (le_not_symmetric)

Prove that the `≤` relation on naturals is not symmetric.
-/

theorem le_not_symmetric_rel : ¬ Symmetric le := by
  intro H
  have H1 : le 0 1 := le.le_step 0 0 (le.le_refl 0)
  have H2 : le 1 0 := H.symm 0 1 H1
  -- Now we have le 1 0, which means 1 ≤ 0, but this is impossible
  cases H2

/-!
### Exercise: 2 stars, standard, optional (le_antisymmetric)
-/

instance le_antisymmetric : Antisymmetric le where
  asymm := sorry

/-!
### Equivalence Relations

A relation is an *equivalence* if it's reflexive, symmetric, and transitive.

This time, we cannot define it as a typeclass based on `Reflexive`, `Transitive` and
`Symmetric` because Lean dose not provide us suitable syntactic sugar. Instead, I
declare it as a predicate. We will soon see the usage of predicates when it comes
to _closure_. Let's just look at the definition now.
-/


def EPred {A: Type} (P: Relation A) := Reflexive P ∧ Transitive P ∧ Symmetric P


/-!
### Partial Orders and Preorders

A relation is a *partial order* when it's reflexive, antisymmetric, and transitive.
-/

def PartialOrder {X : Type} (R : X → X → Prop) : Prop :=
  Reflexive R ∧ Antisymmetric R ∧ Transitive R

/-!
A *preorder* is almost the same as a partial order, but doesn't require antisymmetry.
-/

def Preorder {X : Type} (R : X → X → Prop) : Prop :=
  Reflexive R ∧ Transitive R

theorem le_order_rel : PartialOrder le := by
  constructor
  · -- reflexive
    exact le_reflexive
  constructor
  · -- antisymmetric
    exact le_antisymmetric
  · -- transitive
    exact le_transitive

/-!
### Congruence
Finally, we give the definition of a congruence relation. Mathematically speaking, it is an
equivalence relation that is compatible with some algebraic operation. Here, we only define
it to be a relation that is preserved under some endomorphism.
-/

class Congruence {X: Type} (R: Relation X) (S: X -> X) where
  cong: forall x y: X, R x y -> R (S x) (S y)

/-!
For example, `le` is a congruence relation under `Nat.succ`.
-/

instance: Congruence le Nat.succ where
  cong := by
    intro x y
    intro H
    induction H with
    | le_refl =>
      apply le.le_refl
    | le_step t H IH =>
      apply Transitive.trans
      . apply IH
      . simp
        apply le.le_step
        apply le.le_refl


/-!
We also say the congruence is kept if `P` is a congruence under `f` implies
`Q` is a congruence under `f`.
-/
class KeepCong {X: Type} (P Q: Relation X) where
  keep_cong: forall (f: X -> X),
    (forall x y, (P x y) -> P (f x) (f y)) ->
    forall x y, (Q x y) -> Q (f x) (f y)


def Relation.keep_cong {X: Type}
  {P Q: Relation X} (f: X -> X)
  [inst: KeepCong P Q]:
    (forall {x y}, (P x y) -> P (f x) (f y)) ->
    forall {x y}, (Q x y) -> Q (f x) (f y) :=
    inst.keep_cong f

/-!
## Predicates on Relations and Closure
We have seen the _transitive closure_ before. Since we have defined a relation to be
_transitive_, are they related or not? The answer is certainly affirmative. Here we think of
`Transitive` as a predicate on `Relation`, and the transitive closure of `R` is the _smallest_
one that satisfies the predicate. We then look at the meaning of this 'smallest'.
-/

/-!
### Sub-relation
A relation `P` is a sub-relation of `Q` if `P x y` implies `Q x y` for all `x y`.
-/

class SubRel {X} (P: Relation X) (Q: Relation X): Prop where
  inclusion: forall x y: X, P x y -> Q x y

notation: 60 P " sub_rel " Q => SubRel P Q

def Relation.super {X: Type} {R Super: Relation X}
  [inst: R sub_rel Super]: forall {x y: X}, R x y -> Super x y
:=
  inst.inclusion _ _


/-!
### Reflexive and Transitive Closure
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
