/-
Copyright (c) 2025 Your Name. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file introduces polymorphism and higher-order functions in Lean,
with detailed explanations suitable for beginners.
-/

import LeanFoundations.Logic.Lists  -- Import the lists file with NatList definitions

set_option linter.unusedVariables false
/-!
# Polymorphism and Higher-Order Functions

This chapter explores two fundamental concepts in functional programming:

1. **Polymorphism** - Writing code that works with many different types
2. **Higher-order functions** - Treating functions as first-class values

These concepts enable powerful abstractions that make functional programming
particularly effective for building modular, reusable software components.

## What We'll Cover
* Defining polymorphic types and functions
* Understanding type parameters and arguments
* Using type inference for cleaner code
* Working with higher-order functions
* Implementing common functional patterns like map, filter, and fold
* Building functions that generate other functions

## Why This Matters
Modern programming increasingly relies on these functional concepts. Even primarily
object-oriented languages now incorporate functional features. Understanding these
ideas will make you a more effective programmer in any language.
-/

/-!
## Understanding Polymorphism

In programming, "polymorphism" comes from Greek words meaning "many forms."
In functional programming, polymorphic code can work with values of many
different types.

For example, the length of a list doesn't depend on what type of elements are in
the list - the logic works exactly the same for a list of numbers, a list of
strings, or a list of any other type.

This is different from object-oriented polymorphism, which typically refers to
subclasses that override behavior from their superclass. In this chapter, we're
focusing on parametric polymorphism - code that works identically for any type.
-/

/-!
## Polymorphic Functions and Type Universe

We first begin with a single case -- identity functions. For our `Nat` and `Bool`,
obviously we have two identity functions, `idNat: Nat -> Nat := λ x => x` and
`idBool: Bool -> Bool := λ x => x`. You can certainly define an identity function
for each type, but the underlying logic are the same: we take the input and use it
as the output. More explictly, we want to make a *polymorphic* identity function,
which takes the desired type `A: Type` and yield a function of type `A -> A`.

To make such a function, we introduce a type universe `Type`, which behaves like a
type itself. This is to say, we add a parameter `A: Type` to `id`, then we want
`id A: A -> A`.
-/

namespace scratch

def id (A: Type) (x: A): A := x
#check (id Nat)  -- should be Nat -> Nat
#check (id Bool)  -- should be Bool -> Bool
#eval (id Bool .true)  -- should be .true

/-!
### Functions Dependent on Types
-/

#check id

/-!
You may wonder what is the type of `id`. Certainly, you can try `#check id` and it
will tell that the type of `id` is `(A: Type) -> A -> A`. This is a function type
dependent on other types. Recall that `->` is right associative, so the above type
is read as `(A: Type) -> (A -> A)`, i.e., you first feed some `(A: Type)` and then
get a function of type `A -> A`. This type can also be written as
`forall (A: Type), A -> A` as in [dependent type theory][rijke2022introduction].

Caveat: `Type` is not a term of `Type`. In some other programming language, they
model every thing as an `object`, and each object has a `class` or a `type`. The
`type` is itself an `object`, whose type is again `type`. In Lean, this is not
admitted, or otherwise you may trigger [Russell's paradox][coq1992paradox].
For example, the following are invalid in Lean.

```lean
#check (Type: Type)
#check ((A: Type) -> A -> A: Type)
```

But, do we have a type for `(A: Type) -> A -> A`?
-/

#check (A: Type) -> A -> A

/-!
You can find that `(A : Type) → A → A : Type 1`, i.e., Lean adopts a hierarchical
type universe `Type 0: Type1`, `Type 1: Type 2` to avoid the paradox, and `Type`
is just the abbreviation of `Type 0`.

Besides, Lean provides a special universe called `Prop`, which is intended to capture
all propositions. We consider `Prop: Type` and they are unified as `Sort`, i.e.
`Prop := Sort 0`, `Type := Type 0 := Sort 1`, `Type 1 := Sort 2`, etc. The keyword
`theorem` shows one way to define terms in `Prop`.

To make the `id` available for all sorts, we put an `{}` after function names.
We will discover more usages later.
-/

def id_for_all.{u} (A: Sort u) (x: A) := x

/-!
### Type Inference and Implicit Arguments

The above `id` is exactly what we want, but a bit cumbersome. For example, if you
know you want to apply the `id` to `Bool.true`, then it is unnecessary to always
specify the `Bool` for `A` because the type `A` can be inferred from the term
`x: A`. By default, Lean require all parameters to be fed. To hint Lean do the type
inference, we use `{}` instead of `()` for the parameters.
-/

def id' {A: Type} (x: A): A := x
#eval id' Bool.true

/-!
Now, we can apply `id'` to a term directly. However, we may still meet with the case
that `id'` is needed for `Nat -> Nat`. To fill in an implicit argument, we use
`(A := Nat)`.
-/

#check id' (A := Nat)  -- should be Nat -> Nat

/-!
Or, if you want the version with all arguments to be explicit, put an `@` before
the function name.
-/
#check @id' Nat  -- should be Nat -> Nat

/-!
You can also specify some parameters (partially apply) with the `(param := term)` syntax.
-/
#check @id' (A := Nat)  -- should be Nat -> Nat
#eval id (A := Nat) (x := .zero)  -- should be .zero


/-!
You can also use the following alternative syntax to define `id`.
-/
def id'': {A: Type} -> (x: A) -> A := fun {A} x => x
def id''': forall {A: Type}, A -> A := fun {A} x => x


end scratch


/-!
## Polymorphic Types

In previous chapters, we worked with lists containing only natural numbers (NatList).
But real programs need to work with many kinds of lists:
* Lists of strings
* Lists of booleans
* Lists of custom types
* Even lists of other lists!

We *could* define separate list types for each element type we need:
-/

-- A list type specifically for booleans
inductive BoolList : Type where
  | nil : BoolList                      -- Empty boolean list
  | cons : Bool → BoolList → BoolList   -- Add a boolean to the front of a list
deriving Repr

/-!
But this approach has serious drawbacks:

1. **Duplication** - We'd need a new type definition for every element type
2. **Redundant functions** - We'd need separate versions of functions like
   `length` and `reverse` for each list type
3. **Redundant proofs** - We'd need to prove the same properties multiple times

This quickly becomes tedious and error-prone!

Instead, we can define a single polymorphic list type that works for any element type.
-/

-- A polymorphic list type that works for any element type
inductive MyList (α : Type) : Type where
  | nil : MyList α                       -- Empty list of α elements
  | cons : α → MyList α → MyList α       -- Add an α element to a list of α elements
deriving Repr

/-!
> To type the `α`, type `\alpha` in vscode.

Let's break down what's happening here:

1. `α` is a **type parameter** - a placeholder for any concrete type
2. `MyList α` is the complete type - a list containing elements of type α
3. When we use this type, we need to specify what type `α` actually is

For example:
* `MyList Nat` is a list of natural numbers
* `MyList String` is a list of strings
* `MyList Bool` is a list of booleans

Think of `MyList` as a "type constructor" or a function from types to types.
Just like a regular function takes a value and returns a value, `MyList` takes
a type and returns a new type.
-/

-- Let's check what type MyList itself has
#check MyList  -- MyList : Type → Type

/-!
The type of `MyList` is `Type → Type`, which confirms it's a function from types to types.

Now let's create some polymorphic lists:
-/

-- A list of natural numbers
def myNatList : MyList Nat :=
  MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.nil (α := Nat))))
  -- Important: We must specify the type parameter for nil: (MyList.nil (α := Nat))

-- A list of booleans
def myBoolList : MyList Bool :=
  MyList.cons true (MyList.cons false (MyList.nil (α := Bool)))
  -- Again, specify (MyList.nil (α := Bool)) to create an empty list of booleans

/-!
Notice that each constructor is also polymorphic:

* `MyList.nil` needs to know what type of elements the empty list could hold
* `MyList.cons` adds an element of the appropriate type to a list of that type

Let's check the types of these constructors:
-/

#check MyList.nil   -- MyList.nil : {α : Type} → MyList α
#check MyList.cons  -- MyList.cons : {α : Type} → α → MyList α → MyList α

/-!
### Understanding the Types of Constructors

The type of `MyList.nil` is `∀ (α : Type), MyList α`, which means it takes a type
argument `α` and returns a value of type `MyList α`.

The type of `MyList.cons` is `∀ (α : Type), α → MyList α → MyList α`, which means
it takes:
1. A type `α`
2. A value of type `α`
3. A list of type `MyList α`
And it returns a new list of type `MyList α`.

When we use these constructors, we need to provide the type parameter explicitly
for `nil` since there are no other values that would help Lean infer the type:
-/

-- Creating lists with explicit type parameters
def explicitNatList : MyList Nat :=
  MyList.cons 1 (MyList.cons 2 (MyList.nil (α := Nat)))

def explicitBoolList : MyList Bool :=
  MyList.cons true (MyList.cons false (MyList.nil (α := Bool)))

/-!
## Polymorphic Functions

Now that we have polymorphic types, we can define polymorphic functions that
work with these types. Let's implement a function that repeats a value to
create a list:
-/

-- Repeat a value n times to create a list
def myRepeat (α : Type) (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => MyList.nil (α := α)                            -- Empty list for count 0
  | n+1 => MyList.cons x (myRepeat α x n)        -- Add x to the front and recurse

/-!
The `myRepeat` function takes three arguments:
1. A type `α` - specifies what type of element we're repeating
2. A value `x` of type `α` - the element to repeat
3. A natural number `count` - how many times to repeat the element

Let's test our function:
-/

-- Examples using myRepeat with explicit type arguments
#eval myRepeat Nat 5 3       -- A list with three 5's
#eval myRepeat String "hello" 2  -- A list with two "hello"s
#eval myRepeat Bool false 2  -- A list with two false values

/-!
This is how polymorphic functions work in their most explicit form. But having
to specify type arguments all the time can be tedious. Next, we'll see how
Lean can infer these types automatically in many cases.
-/

/-!
## Type Argument Inference

When we define polymorphic functions like `myRepeat`, we have to pass the
type explicitly as the first argument. However, often this type can be
determined from the other arguments.

For example, in `myRepeat Nat 5 3`, the type parameter `Nat` could be inferred
from the fact that `5` has type `Nat`.

Again, we use the **implicit** arguments by wrapping them in curly braces and
Lean will try to figure out their values from context.
-/

-- Repeat with implicit type parameter
def myRepeat' {α : Type} (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => MyList.nil (α := α)  -- We still need to provide α here explicitly
  | n+1 => MyList.cons x (myRepeat' x n)  -- No need to pass α to myRepeat' recursively

/-!
There are two important differences here:

1. We put the type parameter `α` in curly braces `{α : Type}` instead of
   parentheses, making it an **implicit argument**

2. We don't pass `α` to `myRepeat'` in the recursive call because it's implicit

However, notice that we still need to provide `α` explicitly to `MyList.nil`.
This is because there's no other information in that context that would help
Lean determine what type `α` should be.

Now we can call myRepeat' without specifying the type:
-/

-- Now we can call myRepeat' without specifying the type explicitly
#eval myRepeat' 5 3       -- Lean infers α = Nat
#eval myRepeat' "hello" 2 -- Lean infers α = String

/-!
We can still provide the type explicitly when needed, using a named parameter:
-/

#eval myRepeat' (α := Bool) false 2 -- Explicitly telling Lean that α = Bool

/-!
## Implementing Polymorphic List Operations

Now let's implement some of the standard list operations in a polymorphic way.
-/

-- Calculate the length of a polymorphic list
def myLength {α : Type} (l : MyList α) : Nat :=
  match l with
  | MyList.nil => 0                -- Empty list has length 0
  | MyList.cons _ t => 1 + myLength t  -- Head plus length of tail

/-!
The `myLength` function doesn't care about the values in the list, only their
count. It works exactly the same regardless of what type of elements the list
contains.

Notice that we use wildcards (`_`) for both the type parameter in `MyList.nil _`
and the head value in `MyList.cons _ t`. This explicitly indicates that we don't
care about these values - we're ignoring them.
-/

-- Append two polymorphic lists
def myAppend {α : Type} (l1 l2 : MyList α) : MyList α :=
  match l1 with
  | MyList.nil => l2                                -- If first list is empty, return second list
  | MyList.cons h t => MyList.cons h (myAppend t l2)  -- Add head to result of appending tails

/-!
The `myAppend` function combines two lists of the same element type. This works
recursively:

1. If the first list is empty, return the second list
2. Otherwise, add the first element of the first list to the result of appending
   the rest of the first list with the second list

This builds up the result list one element at a time.
-/

-- Reverse a polymorphic list
def myReverse {α : Type} (l : MyList α) : MyList α :=
  match l with
  | MyList.nil => MyList.nil (α := α)                           -- Empty list reverses to itself
  | MyList.cons h t => myAppend (myReverse t) (MyList.cons h (MyList.nil (α := α)))  -- Reverse tail and append head

/-!
The `myReverse` function reverses the order of elements in a list. It works by:

1. If the list is empty, return the empty list (nothing to reverse)
2. Otherwise, reverse the tail, then append the head to the end

Notice that we need to explicitly provide the type parameter to `MyList.nil α` in
both places because Lean wouldn't be able to infer it otherwise.
-/

-- Let's test our polymorphic functions
def testList1 : MyList Nat := MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.nil (α := Nat))))
def testList2 : MyList Bool := MyList.cons true (MyList.cons false (MyList.nil (α := Bool)))

-- Testing myLength
#eval myLength testList1  -- Should be 3
#eval myLength testList2  -- Should be 2

-- Testing myReverse
#eval myReverse testList1     -- Should be [3, 2, 1]
#eval myAppend testList1 (MyList.cons 4 (MyList.nil (α := Nat)))  -- Should be [1, 2, 3, 4]

/-!
## Polymorphic Pairs

Another common polymorphic type is the **pair** (or **product**) type, which
combines two values that can have different types.
-/

-- A polymorphic pair type
structure MyPair (α β : Type) : Type where
  first : α    -- First component of type α
  second : β   -- Second component of type β
deriving Repr

/-!
This structure takes two type parameters, `α` and `β`, which can be completely
different types:

- `MyPair Nat Bool` represents pairs where the first component is a natural number
  and the second component is a boolean
- `MyPair String Nat` represents pairs where the first component is a string
  and the second component is a natural number
- `MyPair String String` represents pairs where both components are strings

The flexibility to mix different types is very powerful.
-/

-- Creating a pair and accessing its components
def pair1 : MyPair Nat String := { first := 42, second := "hello" }
#eval pair1.first   -- 42
#eval pair1.second  -- "hello"

/-!
We can define polymorphic functions that work with pairs:
-/

-- Swap the elements of a pair
def swap {α β : Type} (p : MyPair α β) : MyPair β α :=
  { first := p.second, second := p.first }

#eval swap pair1  -- { first := "hello", second := 42 }

/-!
## Polymorphic Options

Sometimes a function might not have a valid result for all inputs. For example,
what should the "head" function return when given an empty list?

One solution is to return a special value indicating "no result." We can define
a polymorphic `Option` type for this purpose:
-/

-- A polymorphic option type
inductive MyOption (α : Type) : Type where
  | some : α → MyOption α              -- Contains a value of type α
  | none : MyOption α                  -- Represents "no value"
deriving Repr

/-!
The `MyOption α` type represents either:
- `MyOption.some x` where `x` is a value of type `α`, or
- `MyOption.none` which represents the absence of a value

This is similar to nullable types in languages like C# or Kotlin, but more
powerful because it's made explicit in the type system. Functions that might
fail are required to return an option type, making it impossible to forget
to handle the "no value" case.
-/

-- Safely get the first element of a list (if it exists)
def headOption {α : Type} (l : MyList α) : MyOption α :=
  match l with
  | MyList.nil => MyOption.none                -- Empty list has no head
  | MyList.cons h _ => MyOption.some h          -- For non-empty list, return the head

-- Testing headOption
#eval headOption testList1  -- Should be Some 1
#eval headOption (MyList.nil (α := Nat))  -- Should be None

/-!
This is much better than returning a default value or crashing the program -
it explicitly communicates whether a valid result exists.

We can define a function to extract the value from an option, using a default
value when the option is `none`:
-/

-- Get the value from an option, with a default if none
def getOrElse {α : Type} (o : MyOption α) (default : α) : α :=
  match o with
  | MyOption.some x => x                -- If some value is present, return it
  | MyOption.none => default            -- If no value, return the default

-- Testing getOrElse
#eval getOrElse (headOption testList1) 0  -- Returns 1
#eval getOrElse (headOption (MyList.nil (α := Nat))) 0  -- Returns 0

/-!
## Higher-Order Functions

So far, we've seen how polymorphism lets us write functions that work with
values of any type. Now let's explore **higher-order functions**, which are
functions that take other functions as arguments or return functions as results.

Higher-order functions are powerful because they let us abstract over common
patterns of computation, factoring out repeated code structures.
-/

-- Apply a function three times to a value
def doit3times {α : Type} (f : α → α) (x : α) : α :=
  f (f (f x))  -- Apply f, then apply f again, then apply f a third time

/-!
The function `doit3times` takes:
1. A function `f` that transforms a value of type `α` into another value of type `α`
2. A starting value `x` of type `α`

It then applies `f` to `x` three times in succession.

This is higher-order because the function `f` is treated as a regular value
that can be passed in and applied within our function.
-/

-- Test with different functions and types
#eval doit3times (fun x => x + 1) 0  -- Apply (x => x + 1) three times to 0: 3
#eval doit3times (fun x => x ++ "!") "hi"  -- Apply (x => x ++ "!") three times: "hi!!!"

/-!
Notice how `doit3times` works with completely different types and operations:
- Numbers and addition
- Strings and concatenation

The function is truly polymorphic - it works with any type and any operation
that transforms values of that type.
-/

/-!
### The Filter Function

A particularly useful higher-order function is `filter`, which selects
elements from a list based on a predicate (a function that returns a boolean):
-/

-- Select elements from a list that satisfy a predicate
def myFilter {α : Type} (test : α → Bool) (l : MyList α) : MyList α :=
  match l with
  | MyList.nil => MyList.nil (α := α)             -- Empty list yields empty list
  | MyList.cons h t =>
      if test h then                         -- Test the head element
        MyList.cons h (myFilter test t)      -- Include head if test passes
      else
        myFilter test t                      -- Skip head if test fails

/-!
The `myFilter` function takes:
1. A predicate function `test` that takes a value of type `α` and returns a `Bool`
2. A list `l` of type `MyList α`

It returns a new list containing only the elements from `l` for which `test` returns `true`.

This is a powerful abstraction that captures the common pattern of "keep only
the elements that satisfy some condition". We can use it to define many useful functions:
-/

-- A function that tests if a number is even
def isEven (n : Nat) : Bool :=
  n % 2 == 0  -- True if n divides evenly by 2

-- Get only the even numbers from a list
def evenNumbers (l : MyList Nat) : MyList Nat :=
  myFilter isEven l

-- Test the filter function
def numberList : MyList Nat :=
  MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.cons 4 (MyList.nil (α := Nat)))))

#eval evenNumbers numberList  -- Should be [2, 4]

/-!
### The Map Function

Another extremely useful higher-order function is `map`, which applies
a function to each element of a list to transform it:
-/

-- Apply a function to each element of a list
def myMap {α β : Type} (f : α → β) (l : MyList α) : MyList β :=
  match l with
  | MyList.nil => MyList.nil (α := β)             -- Empty list maps to empty list
  | MyList.cons h t => MyList.cons (f h) (myMap f t)  -- Apply f to head and map the tail

/-!
The `myMap` function takes:
1. A function `f` that transforms values of type `α` into values of type `β`
2. A list `l` of type `MyList α`

It returns a new list of type `MyList β`, where each element is the result
of applying `f` to the corresponding element in the original list.

Notice that `myMap` is even more flexible than our previous functions -
the input and output types can be completely different!

For example:
- Map `Nat → Nat` transforms a list of numbers to another list of numbers
- Map `Nat → String` transforms a list of numbers to a list of strings
- Map `α → Bool` transforms a list of any type to a list of booleans
-/

-- Double each number in a list
#eval myMap (fun n => n * 2) numberList  -- Should be [2, 4, 6, 8]

-- Convert numbers to strings
#eval myMap (fun n => toString n) numberList  -- Should be ["1", "2", "3", "4"]

/-!
### The Fold Function

Perhaps the most powerful higher-order function is `fold`, which can
express almost any list operation by "folding" the list into a single value:
-/

-- Combine the elements of a list using a binary operation
def myFold {α β : Type} (f : α → β → β) (l : MyList α) (initial : β) : β :=
  match l with
  | MyList.nil => initial                  -- Empty list returns the initial value
  | MyList.cons h t => f h (myFold f t initial)  -- Combine head with fold of tail

/-!
The `myFold` function takes:
1. A function `f` that combines a value of type `α` and a value of type `β` to produce a new value of type `β`
2. A list `l` of type `MyList α`
3. An initial value of type `β`

It processes the list from left to right, using `f` to combine each element
with the accumulated result, starting with the initial value.

With `myFold`, we can implement many of our previous functions:
-/

-- Sum a list of numbers using fold
def mySum (l : MyList Nat) : Nat :=
  myFold (fun x acc => x + acc) l 0  -- Add each element to the accumulator

-- Calculate the length of a list using fold
def myLengthWithFold {α : Type} (l : MyList α) : Nat :=
  myFold (fun _ acc => acc + 1) l 0  -- Increment accumulator for each element

-- Test our fold-based functions
#eval mySum numberList  -- Should be 10
#eval myLengthWithFold numberList  -- Should be 4

/-!
### Anonymous Functions

In the examples above, we've been using anonymous functions (also called
lambda expressions) to pass to our higher-order functions. These are created
with the syntax `fun x => ...`, where `x` is the parameter name and `...` is
the body of the function.

Anonymous functions are convenient when we need a simple function that we'll
only use once. For example:
-/

-- Filter even numbers using an anonymous function
#eval myFilter (fun n => n % 2 == 0) numberList  -- [2, 4]

-- Map using an anonymous function to calculate squares
#eval myMap (fun n => n * n) numberList  -- [1, 4, 9, 16]

/-!
We could also define named functions and pass those:
-/

-- Named function to calculate the square of a number
def square (n : Nat) : Nat := n * n

-- Map using the named function
#eval myMap square numberList  -- [1, 4, 9, 16]

/-!
Both approaches are valid, and which one you choose depends on the situation.
Anonymous functions are great for simple, one-off operations, while named
functions are better for complex logic or functions you'll reuse.
-/

/-!
## Functions That Return Functions

Higher-order functions can also return functions as results. This is particularly
useful for creating specialized functions on demand:
-/

-- Create a function that adds a specific number
def addN (n : Nat) : Nat → Nat :=
  fun x => x + n  -- Return a function that adds n to its argument

-- Create specialized adder functions
def add5 : Nat → Nat := addN 5
def add10 : Nat → Nat := addN 10

-- Test our function-generating function
#eval add5 7   -- Should be 12
#eval add10 7  -- Should be 17

/-!
Here, `addN` is a function that takes a number `n` and returns a new function.
The returned function takes a number `x` and adds `n` to it.

We use `addN` to create specialized adder functions `add5` and `add10`, which
add 5 and 10 to their arguments, respectively.

This technique is called **partial application** and is very powerful for
creating customized functions.
-/

/-!
## Using Lean's Standard Library

So far, we've defined our own polymorphic types and functions for educational
purposes. In practice, you would use Lean's standard library, which includes
all of these types and many more functions and theorems about them.

The standard library provides:
- `List α` type for polymorphic lists
- `Option α` type for optional values
- `Prod α β` (or `α × β`) for pairs
- `Sum α β` (or `α ⊕ β`) for alternatives between types

And many higher-order functions:
- `List.map` for transforming each element
- `List.filter` for selecting elements
- `List.foldl` and `List.foldr` for reducing lists to values
- And many more specialized operations

Let's see a few examples of using the standard library:
-/

-- Using Lean's standard List type
def standardList : List Nat := [1, 2, 3, 4]

-- Standard library functions
#eval List.length standardList              -- 4
#eval List.map (fun n => n * 2) standardList  -- [2, 4, 6, 8]
#eval List.filter (fun n => n % 2 == 0) standardList  -- [2, 4]

/-!
## Exercises with Detailed Hints

Complete the following exercises to practice working with polymorphic
functions and higher-order functions.
-/

/-!
### Exercise 1: Polymorphic Length

Write a polymorphic function to calculate the length of a list.
This should work for any type of list.

**Hints:**
- Use pattern matching on the list
- For an empty list, the length is 0
- For a non-empty list, the length is 1 plus the length of the tail
- Remember to mark the type parameter as implicit with curly braces
-/

def ex1_length {α : Type} (xs : MyList α) : Nat :=
  match xs with
  | MyList.nil => 0                   -- Empty list has length 0
  | MyList.cons h tail => 1 + ex1_length tail  -- Length of a non-empty list is 1 + length of tail
  -- The variable h represents the head value

-- Tests (using MyList constructor syntax)
#eval ex1_length (MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.nil (α := Nat)))))  -- Should be 3
#eval ex1_length (MyList.cons "a" (MyList.cons "b" (MyList.nil (α := String))))  -- Should be 2
#eval ex1_length (MyList.nil (α := Nat))  -- Should be 0

/-!
### Exercise 2: Count Odd Members

Write a function that counts the number of odd numbers in a list.

**Hints:**
- First define a helper function `isOdd` that checks if a number is odd
- You can use the modulo operator `%` to check if a number is odd (n % 2 == 1)
- Then use `List.filter` to keep only the odd numbers
- Finally, use `List.length` to count how many remained
- Alternatively, you could use recursion and pattern matching directly
-/

-- Helper function to check if a number is odd
def isOdd (n : Nat) : Bool :=
  n % 2 == 1  -- True if there's a remainder of 1 when dividing by 2

def ex2_countOddMembers (xs : List Nat) : Nat :=
  List.length (List.filter isOdd xs)
  -- Filter the list to keep only odd numbers, then count how many remain

-- Tests
#eval ex2_countOddMembers [1, 2, 3, 4, 5]  -- Should be 3 (1, 3, 5 are odd)
#eval ex2_countOddMembers [2, 4, 6, 8]     -- Should be 0 (no odd numbers)
#eval ex2_countOddMembers [1, 3, 5, 7]     -- Should be 4 (all are odd)

/-!
### Exercise 3: Anonymous Functions

Use anonymous functions with `List.filter` to create specialized filters.

**Hints:**
- For the first function, combine two conditions using `&&` (logical AND)
- The condition should check if a number is even (n % 2 == 0) AND greater than 5
- For the second function, use String.length to get the length of a string
- Then compare this length to 3 using `>`
-/

def ex3_filterEvenGt5 (xs : List Nat) : List Nat :=
  List.filter (fun n => n % 2 == 0 && n > 5) xs
  -- Keep only numbers that are both even (divisible by 2) and greater than 5

def ex3_filterLongStrings (xs : List String) : List String :=
  List.filter (fun s => s.length > 3) xs
  -- Keep only strings with length greater than 3

-- Tests
#eval ex3_filterEvenGt5 [2, 4, 6, 8, 10, 12]  -- Should be [6, 8, 10, 12]
#eval ex3_filterEvenGt5 [1, 3, 5, 7, 9]       -- Should be [] (no even numbers > 5)
#eval ex3_filterLongStrings ["a", "abc", "abcd", "abcde"]  -- Should be ["abcd", "abcde"]

/-!
### Exercise 4: Partition

Implement a function that separates elements of a list into two lists:
those that satisfy a predicate and those that don't.

**Hints:**
- Use `List.filter` twice - once with the predicate and once with the negated predicate
- To negate a predicate `p`, use `fun x => !p x` or `fun x => !(p x)`
- Return a pair of lists using the tuple syntax `(listTrue, listFalse)`
- Remember that Lean uses tuples for pairs in the standard library
-/

def ex4_partition {α : Type} (test : α → Bool) (xs : List α) : List α × List α :=
  (List.filter test xs, List.filter (fun x => !test x) xs)
  -- First list: elements that pass the test
  -- Second list: elements that fail the test
  -- Returns these as a pair (tuple)

-- Tests
#eval ex4_partition isEven [1, 2, 3, 4, 5, 6]  -- Should be ([2, 4, 6], [1, 3, 5])
#eval ex4_partition (fun s => s.length > 3) ["a", "abc", "abcd", "abcde"]
  -- Should be (["abcd", "abcde"], ["a", "abc"])

/-!
### Exercise 5: Map with Composition

Write a function that takes a list of numbers and returns a list where
each number has been doubled and then increased by 1.

**Hints:**
- Use `List.map` with a single function that performs both operations
- The function should multiply by 2 and then add 1: `fun n => 2*n + 1`
- You could also create separate functions and compose them, but the
  direct approach is simpler in this case
-/

def ex5_doublePlusOne (xs : List Nat) : List Nat :=
  List.map (fun n => 2*n + 1) xs
  -- Double each number (multiply by 2) and then add 1

-- Alternative implementation with function composition
def doubleNum (n : Nat) : Nat := 2 * n
def plusOne (n : Nat) : Nat := n + 1

def ex5_doublePlusOne' (xs : List Nat) : List Nat :=
  List.map (fun n => plusOne (doubleNum n)) xs
  -- First double each number, then add 1

-- Tests
#eval ex5_doublePlusOne [1, 2, 3, 4]  -- Should be [3, 5, 7, 9]
#eval ex5_doublePlusOne' [1, 2, 3, 4]  -- Should also be [3, 5, 7, 9]

/-!
### Exercise 6: Flat Map

Implement a `flatMap` function that:
1. Applies a function that returns a list to each element
2. Concatenates all the resulting lists

**Hints:**
- Start with a recursive approach using pattern matching on the input list
- For an empty list, return an empty list
- For a non-empty list, apply the function to the head, then recursively flatMap the tail
- Concatenate the results using the `++` operator for lists
- Alternatively, you can implement this using `List.map` followed by a fold with `++`
-/

-- Recursive implementation
def ex6_flatMap {α β : Type} (f : α → MyList β) (xs : MyList α) : MyList β :=
  match xs with
  | MyList.nil => MyList.nil (α := β)  -- Empty list produces empty result
  | MyList.cons h t => myAppend (f h) (ex6_flatMap f t)
    -- Apply f to head and concatenate with flatMap of tail

-- Alternative implementation using map and fold
def ex6_flatMap' {α β : Type} (f : α → MyList β) (xs : MyList α) : MyList β :=
  myFold (fun x acc => myAppend acc (f x)) xs (MyList.nil (α := β))
  -- Fold over the list, accumulating the results by concatenating

-- Tests (using explicit MyList constructor syntax)
#eval ex6_flatMap (fun n => MyList.cons n (MyList.cons (n+1) (MyList.nil (α := Nat))))
       (MyList.cons 1 (MyList.cons 5 (MyList.cons 10 (MyList.nil (α := Nat)))))
  -- Should be [1, 2, 5, 6, 10, 11]

/-!
### Exercise 7: Map-Reduce Pattern

Implement a "map-reduce" pattern:
1. Map: Apply a function to each element
2. Reduce: Combine the results using a binary operation

**Hints:**
- First use `List.map` to transform each element with function `f`
- Then use `List.foldl` to combine the results using operation `op`
- Start the fold with the provided `zero` value
- For sumOfSquares, use this pattern with `square` and addition
-/

def ex7_mapReduce {α β : Type} (f : α → β) (op : β → β → β) (zero : β) (xs : List α) : β :=
  List.foldl op zero (List.map f xs)
  -- First map f over the entire list
  -- Then fold the results using op, starting with zero

def ex7_sumOfSquares (xs : List Nat) : Nat :=
  ex7_mapReduce (fun n => n * n) (fun x y => x + y) 0 xs
  -- Square each number, then sum the results

-- Tests
#eval ex7_sumOfSquares [1, 2, 3, 4]  -- Should be 30 (1 + 4 + 9 + 16)
#eval ex7_mapReduce toString (fun s1 s2 => s1 ++ "," ++ s2) "" [1, 2, 3]
  -- Should be "1,2,3"

/-!
## Additional Exercises

These are more challenging exercises to further develop your skills
with polymorphism and higher-order functions.
-/

/-!
### Exercise 8: Custom Option Map

Implement a function `optionMap` that applies a function to an option value:
- If the option is `none`, it returns `none`
- If the option is `some x`, it returns `some (f x)`

**Hints:**
- Pattern match on the option value
- Handle both `some` and `none` cases
- Use the appropriate constructor for the result
-/

def optionMap {α β : Type} (f : α → β) (o : Option α) : Option β :=
  match o with
  | none => none  -- If no value, return none
  | some x => some (f x)  -- If there's a value, apply f and wrap in some

-- Tests
#eval optionMap (fun n => n * 2) (some 3)  -- Should be some 6
#eval optionMap (fun n => n * 2) (none : Option Nat)  -- Should be none

/-!
### Exercise 9: Zip With Function

Implement a `zipWith` function that:
1. Takes a binary function and two lists
2. Applies the function to corresponding elements
3. Stops when either list runs out

**Hints:**
- Match on both lists simultaneously using pattern matching
- When either list is empty, return an empty list
- Otherwise, apply the function to the heads and recursively process the tails
-/

def zipWith {α β γ : Type} (f : α → β → γ) (xs : MyList α) (ys : MyList β) : MyList γ :=
  match xs, ys with
  | MyList.nil, _ => MyList.nil (α := γ)  -- If first list is empty, return empty list
  | _, MyList.nil => MyList.nil (α := γ)  -- If second list is empty, return empty list
  | MyList.cons x xs', MyList.cons y ys' => MyList.cons (f x y) (zipWith f xs' ys')
    -- Apply f to the heads and recursively zipWith the tails

-- Tests with MyList constructors
#eval zipWith (fun x y => x + y)
  (MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.nil (α := Nat)))))
  (MyList.cons 4 (MyList.cons 5 (MyList.cons 6 (MyList.nil (α := Nat)))))  -- Should be [5, 7, 9]

/-!
### Exercise 10: Implementing TakeWhile and DropWhile

Implement two functions:
1. `takeWhile`: Take elements from a list as long as they satisfy a predicate
2. `dropWhile`: Drop elements from a list as long as they satisfy a predicate

**Hints:**
- Both functions need pattern matching on the list
- For an empty list, both return an empty list
- For takeWhile, if the head satisfies the predicate, include it and recursively process the tail
- For dropWhile, if the head satisfies the predicate, drop it and recursively process the tail
- Be careful with the termination conditions
-/

def takeWhile {α : Type} (p : α → Bool) (xs : MyList α) : MyList α :=
  match xs with
  | MyList.nil => MyList.nil (α := α)  -- Empty list yields empty result
  | MyList.cons x xs' =>
      if p x then
        MyList.cons x (takeWhile p xs')  -- Keep head and continue if condition met
      else
        MyList.nil (α := α)  -- Stop taking elements once condition fails

def dropWhile {α : Type} (p : α → Bool) (xs : MyList α) : MyList α :=
  match xs with
  | MyList.nil => MyList.nil (α := α)  -- Empty list yields empty result
  | MyList.cons x xs' =>
      if p x then
        dropWhile p xs'  -- Drop head and continue if condition met
      else
        MyList.cons x xs'  -- Keep all remaining elements once condition fails

-- Tests with MyList constructors
#eval takeWhile (fun n => n < 5)
  (MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.cons 4
    (MyList.cons 5 (MyList.cons 6 (MyList.cons 7 (MyList.nil (α := Nat)))))))))
  -- Should be [1, 2, 3, 4]
