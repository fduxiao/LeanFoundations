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
> a new one.
-/

abbrev Relation (X: Type) := X -> X -> Prop

/-!
Since propositions are just objects in Lean, we can study the properties about relations. For
example, we can classify relations (as reflexive, transitive, etc.), prove theorem about them,
or make new relations upon them. And, you will see that typeclass will help a lot.
-/


/-!
## Basic Properties of Relations

We begin with some basic mathematical examples and show some naive applications of typeclass.

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

> Note that they are defined with implicit parameters.
-/

class Reflexive {X} (P: Relation X) where
  refl: forall {x: X}, P x x

def Relation.refl {X: Type} {P: Relation X} [inst: Reflexive P]:
  forall {x: X}, P x x := inst.refl

class Irreflexive {X} (P: Relation X) where
  irrefl: forall {x: X}, Not (P x x)

def Relation.irrefl {X: Type} {P: Relation X} [inst: Irreflexive P]:
  forall {x: X}, Not (P x x) := inst.irrefl


/-!
For example, `le` is reflexive.
-/

instance le_reflexive: Reflexive le where
  refl := le.le_refl _  -- `_` is the placeholder, which is inferred automatically.


example: 5 ≤' 5 := by
  apply Relation.refl


/-!
`Eq` is another example
-/

instance {X: Type}: Reflexive (Eq (α := X)) where
  refl := Eq.refl _


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

class Transitive {X} (R: Relation X) where
  trans: forall {x y z: X}, R x y -> R y z -> R x z

def Relation.trans {X: Type} {R: Relation X} [inst: Transitive R]:
  forall {x y z: X}, R x y -> R y z -> R x z := inst.trans


/-!
> Lean provides a hetergeneous version `Trans`, a bit like the `HAdd` class. Check it
> if you are interested.

We still use the example of `le`.
-/
instance le_transitive: Transitive le where
  trans := by
    intro x y z
    intro Hab Hbc
    induction Hbc with
    | le_refl => exact Hab
    | le_step c' Hbc' ih =>
      apply le.le_step
      exact ih


/-!
So now, if you want to prove `3 ≤' 5`, you can use the transitivity, i.e., it suffices to
prove `3 ≤' 4` and `4 ≤' 5`, which are exactl a `le.le_step` followed by `le.le_refl`.
Note that this time we specify the intermediate value `y := 4`.
-/
example: 3 ≤' 5 := by
  apply Relation.trans (y := 4)  -- you can specify the intermediate value
  . apply le.le_step
    apply le.le_refl
  . apply le.le_step
    apply le.le_refl

/-!
You can also repeat `Relation.trans` in chain, and let Lean to figure out the
intermediate value. This suggests some kind of automation of proof.
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
  symm: forall {x y: X}, P x y -> P y x

def Relation.symm {X} {P: Relation X} [inst: Symmetric P]:
  forall {x y: X}, P x y -> P y x := inst.symm


class Antisymmetric {X} (P: Relation X) where
  asymm: forall {x y: X}, P x y -> P y x -> x = y

def Relation.asymm {X} {P: Relation X} [inst: Antisymmetric P]:
  forall {x y: X}, P x y -> P y x -> x = y := inst.asymm


/-!
### Exercise: 2 stars, standard, optional (le_not_symmetric)

Prove that the `≤` relation on naturals is not symmetric.
-/

theorem le_not_symmetric_rel : ¬ Symmetric le := by
  intro H
  have H1 : le 0 1 := le.le_step 0 0 (le.le_refl 0)
  have H2 : le 1 0 := H.symm H1
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
declare it as a _predicate_. We will soon see the usage of predicates when it comes
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

class Congruence {X: Type} (R: Relation X) (f: X -> X) where
  cong: forall {x y: X}, R x y -> R (f x) (f y)

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
    (forall {x y}, (P x y) -> P (f x) (f y)) ->
    forall {x y}, (Q x y) -> Q (f x) (f y)


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
  inclusion: forall {x y: X}, P x y -> Q x y

notation: 60 P " sub_rel " Q => SubRel P Q

def Relation.super {X: Type} {R Super: Relation X}
  [inst: R sub_rel Super]: forall {x y: X}, R x y -> Super x y
:=
  inst.inclusion

/-!
For example `=` is a sub-relation of `≤'`.
-/
instance: SubRel Eq le where
  inclusion := by
    intro x y H
    rewrite [H]
    apply le.le_refl


/-!
We can also observe that `SubRel` is itself a poset on all relations
-/

instance sub_rel_refl {X} {R: Relation X}: R sub_rel R where
  inclusion := id

instance: forall {X: Type}, Reflexive (SubRel (X := X)) where
  refl := by
    intro P
    apply sub_rel_refl


instance: forall {X: Type}, Transitive (SubRel (X := X)) where
  trans {P Q R} {s1 s2} := by
    apply SubRel.mk
    intro a b H
    apply Q.super
    apply P.super
    apply H


/-!
To prove the antisymmetry, we have to use functional and propositional extensionality.
-/

theorem rel_eq: forall {A: Type} {P Q: Relation A},
  (forall x y: A, P x y <-> Q x y) ->
  P = Q
:= by
  intro A P Q H
  apply funext
  intro x
  apply funext
  intro y
  apply propext
  apply H

instance: forall {X: Type}, Antisymmetric (SubRel (X := X)) where
  asymm := by
    intro P Q s1 s2
    apply rel_eq
    intro a b
    apply Iff.intro
    . apply s1.inclusion
    . apply s2.inclusion


/-!
### Closure under a Predicate

Given a predicate `Pred: Relation X -> Prop` and a relation `R: X -> X -> Prop`, the closure `C` of
`R` under `Pred` is a relation satisfying the following:
1. `R` is a sub-relation of `C`;
2. `Pred C` is proved;
3. if `D` is another relation satyisfying 1,2, then `C` is a sub-relation of `D`.
-/

abbrev RelationPred (X: Type) := Relation X -> Prop

class Closure {X: Type} (Pred: outParam (RelationPred X)) (R: outParam (Relation X)) (C: Relation X) where
  sub: R sub_rel C
  pred: Pred C
  least: forall (D: Relation X), Pred D -> (R sub_rel D) -> C sub_rel D


/-!
Then, we can instantialize `R sub_rel C` so that we can use `Relation.super` as defined above.
Also, two closures must be the sub-relation of each other. We instantialize then as `Closure.cl_sub`
and `Closure.cl_cl_sub`.
-/

instance Closure.cl_sub {X: Type} {R C: Relation X} {Pred: RelationPred X} [inst: Closure Pred R C] : R sub_rel C
:= inst.sub

instance Closure.cl_cl_sub {X: Type} (Pred: RelationPred X) {R: Relation X} {C1 C2: Relation X}
  [inst1: Closure Pred R C1] [inst2: Closure Pred R C2]
: C1 sub_rel C2 where
  inclusion := by
    intro a b
    let sub := inst1.least C2 inst2.pred inst2.sub
    apply sub.inclusion

/-!
> Note that we need to declare `Pred` and `R` to be `outParam`, because the information of
> them will be erased if we want to instantialize `R sub_rel C`. When Lean wants to find an
> instance of `R sub_rel C`, it has to also search for the instances of `Closure.cl_sub`. As
> noted before, the parameter `Pred` will be unknown at this point, and Lean will refuse to
> continue if you don't tag them with `outParam`.
>
> We are doing this purely for technical reason: to use `Relation.super` with a relaiton and its
> closure, we have to fulfill the class `SubRel`. If you are unhappy with this technical compromise,
> you can remove them, but instead, prove the following two auxiliary theorems.
> ```lean
> theorem Closure.super {X: Type} {R C: Relation X} {Pred: RelationPred X} [inst: Closure Pred R C]
> : forall {x y: X}, R x y -> C x y
> := inst.sub.inclusion
>
> theorem Closure.cl_cl_sub {X: Type} {Pred: RelationPred X} {R: Relation X} {C1 C2: Relation X}
>   [inst1: Closure Pred R C1] [inst2: Closure Pred R C2]
> : forall {x y: X}, C1 x y -> C2 x y
> := by
>   intro x y
>   let sub := inst1.least C2 inst2.pred inst2.sub
>   apply sub.inclusion
> ```
-/

/-!
We then define the closure operation. Here, a relation operation is a function mapping a relation
to another, and being a closure operation means that it can turn a relation into its closure under
some predicate.
-/

abbrev RelationOp (X: Type) := Relation X -> Relation X

class ClosureOp {X: Type} (Pred: outParam (RelationPred X)) (Cl: (RelationOp X)) where
  close (R: Relation X): Closure Pred R (Cl R)
  sub {R: Relation X} := (close R).sub (R := R)
  pred {R: Relation X} := (close R).pred (R := R)
  least {R D: Relation X} := (close R).least (R := R) (D := D)

/-!
We also define the related syntactic sugar and instances.
-/

def RelationOp.close {X: Type}
  (Cl: RelationOp X) (R: Relation X) {Pred: RelationPred X}
  [inst: ClosureOp Pred Cl]
:= inst.close R


instance {X: Type} {Pred: RelationPred X} (Cl: RelationOp X) [inst: ClosureOp Pred Cl]
  (R: Relation X): Closure Pred R (Cl R)
:= inst.close R


instance {X: Type} {Pred: RelationPred X} {Cl: RelationOp X}
  [inst: ClosureOp Pred Cl] {R: Relation X}: R sub_rel (Cl R)
:= (inst.close R).sub


/-!
Of course, the closure operation makes `sub_rel` a congruence relation, and is montone
as a function from a poset to itself.
-/
instance cl_op_cl_op_sub {X: Type} {Pred: RelationPred X} {C1 C2: RelationOp X}
  [inst1: ClosureOp Pred C1] [inst2: ClosureOp Pred C2]
  {R: Relation X}: C1 R sub_rel C2 R
where
  inclusion := by
    intro a b
    let sub := @inst1.least R (C2 R) inst2.pred inst2.sub
    apply sub.inclusion

instance cl_mono {X: Type} {Pred: RelationPred X} {Cl: RelationOp X} [inst: ClosureOp Pred Cl]
  {R S: Relation X} [r1: R sub_rel S]: Cl R sub_rel Cl S
where
  inclusion := by
    have r2: S sub_rel Cl S := inst.sub
    have r3: R sub_rel Cl S := Relation.trans r1 r2
    let H := @inst.least R (Cl S) inst.pred r3
    intro x y
    apply H.inclusion


/-!
### Reflexive and Transitive Closure
The *reflexive, transitive closure* of a relation `R` is the smallest relation that contains `R`
and that is both reflexive and transitive. We saw this concept earlier when we looked at the
`clos_refl_trans` relation in the IndProp chapter.

Let's define it again here and explore its properties with the `Closure` typeclass.
-/
def RTPred {X: Type} (R: Relation X) := Reflexive R ∧ Transitive R

/--
Reflexive Transitive relation Closure
-/
inductive RTCl {X} (R: Relation X): Relation X where
  | refl {x: X}: RTCl R x x
  | step {x y z: X}: R x y -> RTCl R y z -> RTCl R x z


instance {X} {R: Relation X}: Transitive (RTCl R) where
  trans := by
    intro x y z Hxy
    induction Hxy with
    | refl => solve_by_elim
    | @step x t y Hxt Hty IHty =>
      intro Hyz
      specialize (IHty Hyz)
      constructor
      . apply Hxt
      . apply IHty

instance {X} {R: Relation X}: Reflexive (RTCl R) where
  refl := RTCl.refl

/-!
We define this function in case Lean cannot figure out the correct instance
when using `Relation.trans`.
-/
def RTCl.trans {X} {R: Relation X}: forall {x y z},
  RTCl R x y -> RTCl R y z -> RTCl R x z
:= (RTCl R).trans


/-!
Then, the mean theorem: `RTCl R` is the closure of `R` under `RTPred`. It has the
name `RTCl.close` so that `RTCl.close R` will be the closure.
-/
instance RTCl.close {X} (R: Relation X): Closure RTPred R (RTCl R) where
  sub := SubRel.mk $ by
    intro x y H
    apply RTCl.step
    . apply H
    . apply RTCl.refl
  pred := by
    constructor
    . /- Reflexive -/
      apply Reflexive.mk RTCl.refl
    . /- Transitive -/
      constructor
      intro x y z
      apply RTCl.trans
  least := by
    intro Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right
    apply SubRel.mk
    intro x y H
    induction H with
    | refl =>
      apply Q.refl
    | @step x t y Hxt Hty IH =>
      apply Q.trans
      . apply sub.inclusion
        apply Hxt
      . apply IH


/-!
Moreover, this says that `RTCl` is the closure operation.
-/
instance rtcl_cl_op {X: Type}: ClosureOp RTPred RTCl (X := X) where
  close := RTCl.close

instance {X} {R: Relation X}: KeepCong R (RTCl R) where
  keep_cong := by
    intro f HCong x y HR
    induction HR with
    | refl =>
      apply RTCl.refl
    | @step x y z Hxy Hyz IHyz =>
      have Hfxy := (HCong Hxy)
      apply RTCl.step Hfxy IHyz


/-!
### Equivalence Closure
Recall that we have seen the equivalence predicate:
```lean
def EPred {A: Type} (P: Relation A) := Reflexive P ∧ Transitive P ∧ Symmetric P
```
We can also define its closure operation.
-/

/--
Equivalence Closure
-/
inductive ECl {X} (R: Relation X): Relation X where
  | inclusion {x y}: R x y -> ECl R x y
  | refl {x}: ECl R x x
  | trans {x y z}: ECl R x y -> ECl R y z -> ECl R x z
  | symm {x y}: ECl R x y -> ECl R y x

/-!
Of course, it satisfies these three classes.
-/
instance {X} {R: Relation X}: Reflexive (ECl R) where
  refl := ECl.refl

instance {X} {R: Relation X}: Transitive (ECl R) where
  trans := ECl.trans

instance {X} {R: Relation X}: Symmetric (ECl R) where
  symm := ECl.symm


/-!
And, it is the smallest one.
-/
instance ECl.close {X} (R: Relation X): Closure EPred R (ECl R) where
  sub := SubRel.mk ECl.inclusion
  pred := by
    constructor
    . /- Reflexive -/
      apply Reflexive.mk ECl.refl
    constructor
    . /- Transitive -/
      apply Transitive.mk ECl.trans
    . /- Symmetric -/
      apply Symmetric.mk ECl.symm
  least := by
    intro Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right.left
    let inst_symm := inst.right.right
    apply SubRel.mk
    intro x y H
    induction H
    case inclusion x y Hxy =>
      apply sub.inclusion
      apply Hxy
    case refl x =>
      apply Q.refl
    case trans Hxy Hyz =>
      apply Q.trans Hxy Hyz
    case symm Hab =>
      apply Q.symm Hab

instance ecl_cl_op {X: Type}: ClosureOp EPred ECl (X := X) where
  close := ECl.close

/-!
And, `ECl` also keeps the congruence.
-/

instance {X} {R: Relation X}: KeepCong R (ECl R) where
  keep_cong := by
    intro f HCong x y HR
    induction HR with
    | @inclusion x y H =>
      apply ECl.inclusion (HCong H)
    | @refl =>
      apply ECl.refl
    | @trans x y z Hxy Hyz IHxy IHyz =>
      apply ECl.trans IHxy IHyz
    | @symm x y Hxy IHxy =>
      apply ECl.symm IHxy


/-!
## Church-Rosser Theorem

Our final section is to prove the Church-Rosser theorem. This theorem was proposed to prove the
uniqueness of β-normal λ-terms (see [here][sorensen2006lectures]). The same technique can also be
applied to other [formal reduction (rewriting) systems][baader1998term]. Here, we give an example
about the formal terms of natural numbers. This could be a good exercise before we eventually go
to λ-calculus.

Let's consider arithmetic expressions of natural numbers and `+` only (with parentheses). For
example, `(3 + 7) + (4 + 2)`. In elementary school, we were taught that the expression is
calculated by `(3 + 7) + (4 + 2) = 10 + 6 = 16`. This seems trivial, but we have to answer a
question: why `16` is the final answer instead of `10 + 6` or even `1 + 15`?

One possible answer is that "we have to eliminate all `+`, or the teacher will give us 0 points".
The intuition behind that is we think of those numbers as the _simplest_ forms, because they are
just how we count things. For example, `6 = S (S (S (S (S (S Z)))))`, and `3 + (1 + 2) = 6` means
the simplest way to represent the result of _putting `3`, `1`, `2` together_ is to count `6` times.

We can now describe the uniqueness problem: we use a set $T$ to collect those expressions, and
define a _reduction_ relation $\to_T$ on $T$ to be the smallest one compatible with $S$ and $+$
generated by $Z + n \to_T n$ and $(S\ n) + m \to_T S\ (n + m)$, i.e., the smallest set (as a
subset of $T\times T$) generated by the following rules:
- $Z + n \to_T n$;
- $(S\ n) + m \to_T S\ (n + m)$;
- if $m\to_T n$, $S\ m\to S\ n$;
- if $m\to_T n$, $m + t\to n + t$ and $t + m\to t + n$.

(If you are confused by this _smallest relation generated by rules_, look at the formal definition
in Lean).

The relation mimics the _calculation_ of natural numbers. Given an expression $e_1$, we can
calculate it into a _simpler_ $e_2$, which is then written as $e_1 \to_T e_2$. This explains
why it is called _reduction_. We also write $\twoheadrightarrow_T$ for the reflexive and transitive
closure of $\to_T$, and $=_T$ for the equivalence closure of $\to_T$. Then, $\to_T$ is a single
step of the calculation (reduction), and $\twoheadrightarrow_T$ means multi-step calculation, and
$=_T$ is the usual $=$ of calculation.

For example, `3 + (1 + 2) = 6` means the following process.
- By the $(Z\ +)$ rule, $0 + 2 \to_T 2$.
- By the congruence under $S$, $S\ (0 + 2) \to_T S\ 2$.
- So, $1 + 2\to_T S\ (0 + 2) \to_T S\ 2$.
- Then, using the congruence under $+$, we get $3 + (1 + 2) \to_T 3 + 3 \to_T \cdots \to_T 6$.

Thus, the equality means exactly that two representations of expressions $3 + (1 + 2)$ and
$6$ are in the equivalence closure of $\to_T$. Apparently, we have different ways to _calculate_
the expression, and since $=_T$ is symmetric, we may have some process like $3 + (1 + 2) =_T
3 + 3 =_T (0 + 3 + 0) + (2 + 1) =_T (0 + 3) + ((1 + 0) + 2)$. Then, the uniqueness problem is
whether the final result is still 6, when it is calculated to the _simplest_ form, despite the
calculation process.

> Note that we have to distinguish between the literal equality $=$ on terms and the
> equivalence $=_T$. For example `6` and `3 + (1 + 2)` are two different elements in
> the set of terms, but are related by the equivalence $=_T$.

Let's formalize this in Lean. First, we model the terms as a type `NatAdd`.
-/

inductive NatAdd where
  | Z : NatAdd
  | S : NatAdd -> NatAdd
  | A : NatAdd -> NatAdd -> NatAdd
  deriving Repr

/-!
This mimics the formal system of natural numbers with only the addition operation.
We also reload the number literals and operator `+` for it.
-/

def NatAdd.fromNat: Nat -> NatAdd
  | .zero => .Z
  | .succ m => .S (.fromNat m)


instance {n}: OfNat NatAdd n where
  ofNat := .fromNat n


instance: Add NatAdd where
  add := .A


/-!
Let's look at some examples of the expressions.
-/
#eval (6: NatAdd)
#eval (3 + (1 + 2): NatAdd)


/-!
They should be two syntax trees like the following.
```
6: S - S - S - S - S - S - Z
3 + (1 + 2):
  A
  | - S - S - S - Z
  |
  | - A
      | - S - Z
      |
      | - S - S - Z
```

The reduction relation is then defined as follows. (It is called R2 to mean _reduced to_.)
-/

inductive NatAdd.R2: Relation NatAdd where
  -- arithmetic
  | ZAdd {n: NatAdd}: NatAdd.R2 (0 + n) n
  | SAdd {m n}: NatAdd.R2 (m.S + n) (m + n).S
  -- for congruence
  | SCong {m n}: NatAdd.R2 m n -> NatAdd.R2 m.S n.S
  | AddCong1 {m1 m2 n}: NatAdd.R2 m1 m2 -> NatAdd.R2 (m1 + n) (m2 + n)
  | AddCong2 {m n1 n2}: NatAdd.R2 n1 n2 -> NatAdd.R2 (m + n1) (m + n2)


/-!
The relation is irreflexive.
-/
instance: Irreflexive NatAdd.R2 where
  irrefl := by
    intro x HR2
    induction x with
    | Z =>
      cases HR2
    | S n IHn =>
      cases HR2 with
      | SCong H =>
        apply IHn
        apply H
    | A x1 x2 IHx1 IHx2 =>
      cases HR2 with
      | AddCong1 H =>
        apply IHx1
        apply H
      | AddCong2 H =>
        apply IHx2
        apply H

/-!
### Normal Forms
With this definition, you can find that those made only by `S` and `Z` are special, because
they cannot be reduced to other forms. We say they are _of normal form_ or simply _normal_
with respect to the relation `R2`. So, the uniqueness problem is that if $m =_T n_1$,
$m =_T n_2$ and $n_1, n_2$ are normal, whether $n_1$ is identical to $n_2$.

This is formalized as follows.
-/

/--
Normal terms with respect to a reduction
-/
def Relation.Normal {X: Type} (R: Relation X) (x: X) := Not (exists y, R x y)

abbrev NatAdd.normal (n: NatAdd) := NatAdd.R2.Normal n

/-!
A direct result is that those of form `Z` or `S something_normal` are normal, while
those of form `A _ _` are not. We start with the trivial two.
-/

theorem NatAdd.Z_normal: NatAdd.Z.normal := by
  unfold NatAdd.normal
  unfold Relation.Normal
  intro contra
  let ⟨y, Hy⟩ := contra
  cases Hy


theorem NatAdd.S_normal_normal: forall n: NatAdd, n.S.normal -> n.normal := by
  intro n H
  intro contra
  let ⟨y, Hy⟩ := contra
  apply H
  exists (y.S)
  constructor
  exact Hy


/-!
Next, we prove the reducibility of `A _ _`, so we know they are not normal.
-/
theorem NatAdd.A_reduce: forall m n: NatAdd, exists k, (m + n).R2 k := by
  intro m
  induction m with (intro n)
  | Z =>
    exists n
    apply NatAdd.R2.ZAdd
  | S m' =>
    exists (m' + n).S
    -- You can also try the `constructor` tactic
    constructor  -- equivalent to `apply NatAdd.R2.SAdd`
  | A m1 m2 IHm1 IHm2 =>
    -- By IH, `(m1 + m2)` is reduced to some `k`.
    -- Then, use congruence.
    let ⟨k, Hk⟩ := IHm1 m2
    exists (k + n)
    constructor  -- `apply NatAdd.R2.AddCong1`
    exact Hk


theorem NatAdd.A_not_normal: forall m n: NatAdd, Not (m + n).normal := by
  intro m n contra
  -- You can choose to unfold the defintions, but Lean is not stupid.
  -- unfold NatAdd.normal at contra
  -- unfold Relation.Normal at contra
  apply contra
  apply NatAdd.A_reduce



/-!
Finally, the successor of a normal term is also normal.
-/
theorem NatAdd.normal_S_normal: forall n: NatAdd, n.normal -> n.S.normal := by
  intro n H
  cases n with
  | Z =>
    intro contra
    let ⟨y, Hy⟩ := contra
    cases Hy with
    | SCong H =>  -- the only possible case
      cases H
  | S m =>
    intro contra
    let ⟨y, Hy⟩ := contra
    cases Hy with
    | @SCong _ k Hk =>   -- the only possible case
      apply H
      exists k
  | A =>
    -- this is impossible
    exfalso
    apply NatAdd.A_not_normal
    exact H


/-!
We can also formalize this with the following function.
-/

def NatAdd.isValue: NatAdd -> Bool
  | .Z => true
  | .S n => n.isValue
  | .A _ _ => false


/-!
So, a term is normal if and only if it is a _value_. This means the normality of
`NatAdd` is decidable.
-/

theorem NatAdd.normal_value: forall (n: NatAdd), n.normal -> n.isValue = true := by
  intro n H
  induction n with
  | Z =>
    simp [NatAdd.isValue]
  | S m IHm =>
    simp [NatAdd.isValue]
    apply IHm
    apply NatAdd.S_normal_normal
    exact H
  | A n1 n2 IHn1 IHn2 =>
    -- this is impossible
    exfalso
    apply NatAdd.A_not_normal
    exact H


theorem NatAdd.value_normal: forall (n: NatAdd), n.isValue = true -> n.normal := by
  intro n H
  induction n with
  | Z =>
    apply NatAdd.Z_normal
  | S m IHm =>
    -- we only have to show that `m` is normal
    apply NatAdd.normal_S_normal
    -- and this can be tell from the inductive hypothesis
    apply IHm
    -- Thus, we only have to prove `m.isValue` is true.
    simp [NatAdd.isValue] at H
    exact H
  | A =>
    -- this is impossible since `(_ + _).isValue` is always false
    simp [NatAdd.isValue] at H

/-!
<hr/>

An equivalent definition of normal forms is to use the reflexive and transitive closure.
Since a normal form cannot be reduced further, if it is reduced by the closure, the result
must be itself. This is formalized as `Relation.MNormal`.
-/

/--
Normal terms with respect to multi-step reduction
-/
def Relation.MNormal {X: Type} (R: Relation X) (x: X) := forall {y}, RTCl R x y -> x = y


def Relation.Normal.MNormal {X: Type} {R: Relation X}:
  forall {x: X}, R.Normal x -> R.MNormal x
:= by
  intro n HR m HMR
  induction HMR with
  | @refl x =>
    eq_refl
  | @step a b c Hab Hbc Hbc =>
    exfalso
    apply HR
    constructor
    apply Hab


/-!
### Exercise: 1 stars, standard, optional (Relation.MNormal.Normal)
-/
theorem Relation.MNormal.Normal {X: Type} {R: Relation X} [Irreflexive R]:
  forall {x: X}, R.MNormal x -> R.Normal x
:= by
  intro n HMR Hx
  let ⟨x, Hx⟩ := Hx
  have E: n = x := by
    sorry
  rewrite [E] at Hx
  apply R.irrefl Hx
