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
objects, so we can `structure` them together.
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
the `structure`, we use the keyword `class` to tell Lean that we hope to use
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
You may want to ask why we need typeclasses. If we have more than one
instance, then they just behave as normal types. If we only have one instance,
why do we have to save it? One benefit of typeclass is operator reloading.
We have seen that for natural numbers, we can use `+` instead of `.add` to
write long expressions. This `+` is such a _common behavior_ described by
typeclass.

We give the example of type `Bool`. We consider `Bool.xor` as the _addition_
of `Bool`, (which can be thought as $\mathbb{F}_2$). If you try `true + true`
in Lean, it will complain that it is illegal. This is because `+` is not
defined for `Bool`, and to tell Lean we want to add two terms for some type,
we fulfill the `Add` instance.
-/

instance: Add Bool where
  add := Bool.xor


/-!
And now, you can add true and false.
-/
#eval true + false

/-!
Similarly, we can define substraction, multiplication and division.
-/
instance: Sub Bool where
  sub := Bool.xor

#eval true - false

instance: Mul Bool where
  mul := Bool.and

#eval true * false

-- We don't have a good definition for `/0`.
instance: Div Bool where
  div a b := if b == false then b else a

/-!
Besides, we also want to use `0`, `1` for `false` and `true`. In other words,
Lean interprets number literals as _nullary_ functions, or you can think of
the interpretation as a function `Nat -> Bool`. Depending on your need, this
interpretation function can be a partial one, e.g., you may only want to
define `0` as `false` and `1` as `true`. Thus, the interpretation of number
literals is describled by the following typeclass.
```lean
class OfNat (A : Type) (n : Nat) where
  ofNat : A
```
If you want to interpret `0`, you just _instantialize_ `OfNat A 0`, etc.
-/

instance: OfNat Bool 0 where
  ofNat := false

instance: OfNat Bool 1 where
  ofNat := true

/-!
Of course, the interpretation can be defined for all natural numbers.
Note that the definition of `OfNat` is a polymorphic one, just like `list`.
When we are instantializing them, we have to specify the `ofNat: Bool` for
all `n: Nat`. To achieve that, we just put the parameters like `n: Nat`
before the `:`, like a normal dependent function, and do the rest depending on `n`.
-/

instance some_interp (n: Nat): OfNat Bool n :=
  OfNat.mk (if n %2 == 0 then false else true)


/-!
Or, with the syntactic sugar.
-/

instance (n: Nat): OfNat Bool n where
  ofNat := if n %2 == 0 then false else true


/-!
Now you can try something like
```lean
#eval 3 + true
```

Note that we have just made the convention that literal `3` is considered as
`3`, which does not mean that we interpret all `Nat` as `Bool`, for example,
`(3: Nat) + true` is still not allowed.

For more Lean-predefined typeclasses, see
[here](https://lean-lang.org/functional_programming_in_lean/Overloading-and-Type-Classes/Standard-Classes/).
-/

/-!
### Auto Derivation
Sometimes, Lean could figure out the instance of a typeclass by itself. For example, if you want
to _pretty print_ a term (e.g., `#eval`, `#print` or use `IO`), you have
to tell Lean how to translate it into a `String` so Lean can display it.
This is specified by the `Repr` typeclass.
```lean
class Repr (α : Type u) where
  reprPrec : α → Nat → Format
```
Despite the complicated definition, you can just think of it as a function `α -> String`
that translates a term of type `α` into a `String`.
-/

namespace ReprExample

inductive Bool where
  | true
  | false

#eval Bool.true  -- ReprExample.Bool.true

instance: Repr Bool where
  reprPrec b _ := match b with
    | Bool.true => "correct"
    | Bool.false => "wrong"

#eval Bool.true  -- correct


/-!
You can use `deriving Repr` clause to tell Lean to automatically generate a `Repr`
instance that just prints the constructor names. This is extremely useful for
type alias (`abbrev`).
-/

inductive Bool' where
  | true
  | false
deriving Repr

end ReprExample

/-!
## Instance Searching
Next, we focus on the case `(3: Nat) + false`. Intuitively, this `false` can
also be understood as `0`, so this should be some `4: Nat`. To Lean this, we
instantialize a heterogeneous addition.
-/

instance: HAdd Nat Bool Nat where
  hAdd n b := n + if b then 1 else 0

/-!
The class `HAdd` is defined with 3 type parameters:
```lean
class HAdd A B C where
  hAdd: A -> B -> C
```
which says that if you want to add a term of `A` and a term of `B` to get
a result of type `C`, you have to specify `hAdd: A -> B -> C`. Then, to
evaluate `(a: A) + (b: B)` of type `C`, Lean will use this `hAdd`.

We defined such an addition for a `Nat` and a `Bool`, and the result type
of it is `Nat`. We can try it now.
-/

#eval (3: Nat) + false

/-!
However, Lean played a trick here. As a polymorphic type, `HAdd` requires
all its three type parameters to do the instance search. To illustrate that,
let's define our own `HAdd` class.
-/
class MyHAdd (A B C: Type) where
  hAdd: A -> B -> C

/-!
Then, we instantialize it.
-/
instance: MyHAdd Nat Bool Nat where
  hAdd n b := n + if b then 1 else 0

/-!
You can try `#eval (myadd (3: Nat) false)`, and Lean will complain that it
cannot determine without the third parameter. You may want to argue that there
is only one instance whose first type is `Nat` and second type is `Bool`, so
Lean should pick that definition. Well, Lean does not do the search for
instances if one metavariable (the type parameter `C`) is not filled in.
Thus, to use it, we must specify the `C` as follows.
-/

#eval (MyHAdd.hAdd (3: Nat) false: Nat)

/-!
Lean allows us to control this by tag the third type `C` as an
_output parameter_, which means it will not do the search on this `C`.
We can look at the following example, and if you are interested, you can
look at the Lean-predefined `HAdd`. See
[here](https://lean-lang.org/functional_programming_in_lean/Overloading-and-Type-Classes/Controlling-Instance-Search/)
for more informations.
-/
class MyHAdd' (A B: Type) (C: outParam Type) where
  hAdd: A -> B -> C

instance: MyHAdd' Nat Bool Nat where
  hAdd n b := n + if b then 1 else 0

#eval (MyHAdd'.hAdd (3: Nat) false)

/-!
## Type Coercion
In the above examples, we only defined how to interpret natural number
literals into `Bool`, and what if a `Nat` is added with to a `Bool`. They
don't necessarily mean 'we can use a `Bool` as a `Nat`'. From the above, it's
not hard to figure out that as long as we need a `Nat`, we can interpret
`false` as `0` and `true` as `1`. To make such a convention, we instantialize
the class `Coe`.
-/

instance: Coe Bool Nat where
  coe b := match b with
    | false => 0
    | true => 1


/-!
Now, we can use a `Bool` as a `Nat`. For example,
-/
#eval false + (3: Nat)

/-!
There are other useful kinds of coersions. We introduce some of
[them](https://lean-lang.org/functional_programming_in_lean/Overloading-and-Type-Classes/Coercions/).

### Coercing to Types
Mathematical objects often consist of a type and some structures defined on
it. For example, a pointed type is just a type with a term of it.
-/

structure Pointed where
  U: Type
  e: U


def pointedNat := Pointed.mk Nat 0

/-!
In general, a term `P: Pointed` is not a type, just as the pointedNat.
We cannot say `0: pointedNat` but `0: pointedNat.U`. Thus, to define functions,
you have to write down everything explicitly.
-/

def Pointed.map (P: Pointed) (f: P.U -> P.U): P.U := f P.e
#eval Pointed.map pointedNat (fun x => x.add 1)

/-!
It will be convenient if we can use `Pointed` itself as a `type`. For example,
we want to write `f: P -> P`. This means as long as we see a `P: Pointed` is
used as a type, it should be `P.U`. To tell Lean that, we instantialize the
`CoeSort` class. (Recall that `Sort` is `Type` + `Prop`.)
-/

instance: CoeSort Pointed Type where
  coe p := p.U

/-!
Now, we can write it more concisely.
-/
def Pointed.map' (P: Pointed) (f: P -> P): P := f P.e

/-!
### Coercing to Functions
Another situation is that we want a term to behavior like a function.
For example, we want to make an `Adder` for natural numbers.
-/

structure Adder where
  amount: Nat

def add4 := Adder.mk 4
def Adder.add (adder: Adder): Nat -> Nat := fun n => adder.amount + n
#eval add4.add 3

/-!
To use the adder, we have to call `Adder.add`. Lean allows us to make the
convention that `add4` can be used as a function `Nat -> Nat`. To do that,
we instantialize the `CoeFun` class.
```lean
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x
```
This definition is a dependent version for the general cases. It has two
parameters: the first for the type to be considered as a function, the
second the type of that function. Since this type can be dependent on the
first parameter, the second is declared as a function from the first one
to the desired type.

In the example of `Adder`, we only want a function of type `Nat -> Nat`,
so we make a constant function to specify the type.
-/

instance: CoeFun Adder (fun _ => Nat -> Nat) where
  coe a := a.add

#check add4 3


/-!
The function definition for the second parameter will be helpful if we want
encode the result type into the first parameter, e.g., the following.
-/

structure NatInterp where
  output: Type
  interp: Nat -> output

instance: CoeFun NatInterp (fun i => Nat -> i.output) where
  coe i := i.interp

/-!
This means for each `NatInterp`, we can specify the output type and it is
then interpreted as a function from `Nat` to the output type.
-/


def interp2True := NatInterp.mk Bool (fun _ => true)
#eval interp2True 9


def interp2List := NatInterp.mk (List Nat) (fun n => [n])
#eval interp2List 3
