/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/

/-!
# Typeclass
In this chapter, we are going to learn a syntactic sugar to organize the
common behavior shared by different types. To begin with, let's think about
the uniqueness of identity in monoid theory. In math, a monoid is a set $M$
with an associative binary operation $op: M\times M \to M$ and an identity
$e\in M$ with respect to that operation. This concept is used to mimic basic
arithmetic. For example, all integers form a monoid, where the
binary operation is the multiplication and the _identity_ is $1$.
(If you are not familiar with _monoid_, just see the Lean code below.)

This abstract definition enables us to discuss the common behavior
about arithmetic. For example, there is only a unique $1$ such that
$1 \times a = a \times 1 = a$ for all $a \in \mathbb{Z}$. And of course,
the same proof can be shifted to other _monoids_, e.g., all rational
numbers under addition or all matrix under multiplication.

In Lean, we have defined the natural numbers `Nat`, and of course, `Nat.zero`
and `Nat.add` should give you a monoid and certainly it satisfies this
uniqueness. Again, the type `Bool` may also be considered as a monoid with
identity `Bool.false` and operation `Bool.xor` (exclusively or).
The uniqueness works for all monoid, but how can we represent this for
all monoids in Lean?

A trivial way is to always write the axioms in the premises.
For example, the following.
-/

example (U: Type) (e: U) (op: U -> U -> U):
  (forall x, op e x = x ∧ op x e = x) ->  -- identity axiom
  (forall x y z, op (op x y) z = op x (op y z)) ->  -- associative axiom
  forall t: U,
    (forall x, op t x = x ∧ op x t = x) -> t = e
:= by
  intro Hid Hassoc
  intro t Hid_t
  let Hte_is_e := (Hid_t e).left
  let Hte_is_t := (Hid t).right
  rewrite [<-Hte_is_e]
  symm
  exact Hte_is_t


/-!
This works well, but the problem is that you have to always repeat all
the necessary axioms. As in the previous chapters, propositions are just
objects, so we can `struct` them together.
-/


structure Monoid (U: Type) where
  e: U  -- underlying set
  op: U -> U -> U
  id: forall x, op e x = x ∧ op x e = x
  assoc: forall x y z, op (op x y) z = op x (op y z)


/-!
This is to say that if we want to call `U` a monoid, we have to provide
the identity, binary operation, and the witness of the two axioms.
Then, we can write the theorem as follows, and the proof is still
the same.
-/
theorem Monoid.id_unique (U: Type) (m: Monoid U):
  forall t: U,
    (forall x, m.op t x = x ∧ m.op x t = x) -> t = m.e
:= by
  intro t Hid_t
  let Hte_is_e := (Hid_t m.e).left
  let Hte_is_t := (m.id t).right
  rewrite [<-Hte_is_e]
  symm
  exact Hte_is_t


/-!
> Note that a more intuitive definition is
> ```lean
> structure Monoid where
>   U: Type  -- underlying set
>   e: U
>   op: U -> U -> U
>   id: forall x, op e x = x ∧ op x e = x
>   assoc: forall x y z, op (op x y) z = op x (op y z)
> ```
> We choose to use the current one because it will later be more helpful
> with the typeclass syntactic sugar.
-/

/-!
Now, we see `Nat` and `Bool` can be defined as two monoids.
-/
def NatMonoid: Monoid Nat := Monoid.mk Nat.zero Nat.add Hid Hassoc where
  Hid := by simp
  Hassoc := Nat.add_assoc


def BoolMonoid: Monoid Bool := Monoid.mk false Bool.xor Hid Hassoc where
  Hid := by simp
  Hassoc := Bool.xor_assoc


/-!
And we can utilize the theorem by providing them.
-/
#check Monoid.id_unique (m := NatMonoid)
#check Monoid.id_unique (m := BoolMonoid)


/-!
## Define a typeclass
The above shows how we explicitly describe the common behavior. It is tedious
that we have to pass the `NatMonoid` repeatedly. Since it is the only one
that is available now, can we tell Lean to infer it just like the implicit
arguments? This requires two things:
1. We have to tell Lean to search for a definition if it sees `Monoid`;
2. How Lean find the corresponding `NatMonoid: Monoid Nat`.

Lean provides a mechanism for this purpose called _typeclass_. Instead of
the `struct`, we use the keyword `class` to tell Lean that we hope to use
it implicitly, and correspondingly, we use `instance` instead of `def` to
define a term of this type and Lean will search for it when an instance
is needed. As you may imagine, their behaviors are exactly the same as the
`Monoid` we have just defined.
-/

class IsMonoid (U: Type) where
  e: U
  op: U -> U -> U
  id: forall x, op e x = x ∧ op x e = x
  assoc: forall x y z, op (op x y) z = op x (op y z)


instance NatIsMonoid': IsMonoid Nat := IsMonoid.mk .zero .add id assoc where
  id := by simp
  assoc := Nat.add_assoc

/-!
> Note that the `: IsMonoid Nat` cannot be omitted as is required by Lean.

Or, you can use the following style to specify the entries.
-/
instance NatIsMonoid: IsMonoid Nat where
  e := .zero
  op := .add
  id := by simp
  assoc := Nat.add_assoc


/-!
Now, let's see how to use such an _implicit argument_ in functions and proofs.
Still, we start with the explicit form.
```lean
theorem IsMonoid.id_unique (U: Type) (inst: IsMonoid U):
  forall t: U,
    (forall x, inst.op t x = x ∧ inst.op x t = x) -> t = inst.e
:= by
  ...
```
Since typeclasses and instances are just normal types and terms, we can
use them as before, and if we want to make `inst: IsMonoid U` implicit,
shall we just enclose it in `{}`? Well, `{}` means the argument can be
inferred from the definition or other types, which does not mean to search
other definitions. For such a parameter, we use `[]` to indicate it.
-/

theorem IsMonoid.id_unique (U: Type) [inst: IsMonoid U]:
  forall t: U,
    (forall x, inst.op t x = x ∧ inst.op x t = x) -> t = inst.e
:= by
  intro t Hid_t
  let Hte_is_e := (Hid_t inst.e).left
  let Hte_is_t := (inst.id t).right
  rewrite [<-Hte_is_e]
  symm
  exact Hte_is_t

/-!
You can see the proof is still the same, where the `inst` means Lean has
to find a definition after keyword `instance` and pass it to the theorem.
Now, we can see that to utilize the theorem `IsMonoid.id_unique`, we don't
have to pass `NatIsMonoid`.
-/

example (t: Nat):
  (forall x, t.add x = x ∧ x.add t = x) -> t = Nat.zero
:= by
  apply IsMonoid.id_unique


/-!
### Passing instance
In the above examples, I write `inst: IsMonoid U` explicitly. If you check
the types of members of a `IsMonoid`, i.e. the _projections_, you can find
they all contains a `[self : IsMonoid U]`.
-/

#check IsMonoid.op  -- IsMonoid.op {U : Type} [self : IsMonoid U] : U → U → U
#check IsMonoid.e  -- IsMonoid.e {U : Type} [self : IsMonoid U] : U


/-!
As in the example above, we don't have to pass the `inst: IsMonoid U` and
Lean shall figure it out by itself, and we can further omit the `inst:`
inside `[]`.
-/
example (U: Type) [/- inst: -/ IsMonoid U]:
  forall t: U,
    (forall x, IsMonoid.op t x = x ∧ IsMonoid.op x t = x) -> t = IsMonoid.e
:= by
  intro t Hid_t
  let Hte_is_e := (Hid_t IsMonoid.e).left
  let Hte_is_t := (IsMonoid.id t).right
  rewrite [<-Hte_is_e]
  symm
  exact Hte_is_t

/-!
### Multiple instances
We have another binary operation on `Nat`, the mutiplication. Obviously, it
gives another monoid, so we can declare a second one.
-/
instance NatIsMonoid2: IsMonoid Nat where
  e := 1
  op := .mul
  id := by simp
  assoc := Nat.mul_assoc

/-!
Lean allows you to define multiple instances, and when you want to use a
definition/theorem with typeclass, you can specify the instance as a normal
argument.
-/

#check IsMonoid.id_unique Nat (inst := NatIsMonoid2)

example (t: Nat):
  (forall x, t.mul x = x ∧ x.mul t = x) -> t = 1
:= by
  apply IsMonoid.id_unique


/-!
However, this still brings us some trouble. The newer `NatIsMonoid2`
shadows the older `NatIsMonoid` in the sense that you cannot prove
the following without specifying the instance.
-/

example (t: Nat):
  (forall x, t.add x = x ∧ x.add t = x) -> t = Nat.zero
:= by
  apply IsMonoid.id_unique (inst := NatIsMonoid)  -- try removing the `(inst := NatIsMonoid)`


/-!
In general, we shall have only one instance, or otherwise, we may not make
the best use of this syntactic sugar. Thus, the name for the instance is not
necessary.
-/
instance: IsMonoid Bool where
  op := .xor
  e := .false
  id := by simp
  assoc := Bool.xor_assoc

/-!
## Operator Reloading
-/

/-!
## Instance Search
-/

/-!
## Type Coercion
-/
