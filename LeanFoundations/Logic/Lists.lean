-- Software Foundations Volume 1: Logical Foundations
-- Lists Chapter - Translated to Lean 4

import LeanFoundations.Logic.Induction

set_option linter.unusedVariables false

/-!
# Working with Structured Data

In this chapter, we'll explore how to work with more complex data structures beyond
simple types. We'll start with pairs, then move to lists, and finally explore
more advanced concepts like bags (multisets) and partial maps.

Structured data is fundamental to programming - every meaningful program operates
on structured information rather than just individual primitive values. Learning
how to define, manipulate, and reason about structured data is therefore a key skill
for both programming and formal verification.

In Lean, we create these structures using "inductive types" - a powerful mechanism
that lets us define our own data types with exactly the properties we need.
-/

-- We build upon the definitions from previous chapters
-- In practice, you would use `import` statements for separate files

/-!
## Pairs of Numbers

Just as functions can take multiple arguments, data types can have constructors
that take multiple arguments. Let's define a type for pairs of numbers:
-/

inductive NatProd : Type
  | pair : Nat → Nat → NatProd

/-!
This declaration tells us that the only way to construct a `NatProd` is by applying
the `pair` constructor to two natural numbers. Think of it like this:
- To make a pair, you need exactly two numbers
- There's no other way to create a pair

The `inductive` keyword tells Lean we're defining a new type from scratch
The `NatProd : Type` specifies the name and indicates it's a type
The `| pair : Nat → Nat → NatProd` defines a constructor named "pair" that takes
two natural numbers and produces a pair
-/

-- Let's create a simple pair of numbers 3 and 5
#check NatProd.pair 3 5  -- This checks the type of the expression

-- We can also check what happens when we create more complex pairs
#check NatProd.pair 0 0  -- A pair of zeros
#check NatProd.pair 42 17  -- Another pair of numbers

/-!
Now that we have pairs, we need ways to extract their components. Here, we define
two functions, `fst` and `snd`, that extract the first and second components of
a pair, respectively. These functions use pattern matching to "take apart" the
pair structure.
-/

-- Functions that extract components from pairs use pattern matching
def NatProd.fst (p : NatProd) : Nat :=
  match p with
  | NatProd.pair x y => x  -- Extract the first component x

def NatProd.snd (p : NatProd) : Nat :=
  match p with
  | NatProd.pair x y => y  -- Extract the second component y

-- Let's test our extraction functions
#eval (NatProd.pair 3 5).fst  -- Should evaluate to 3
#eval (NatProd.pair 3 5).snd  -- Should evaluate to 5

-- We can also compose these operations
#eval (NatProd.pair (NatProd.pair 5 6).snd 7).fst  -- First extracts 6, then pairs (6,7), then extracts 6

/-!
The pattern matching expression `match p with | NatProd.pair x y => ...` works like this:
1. Take the input value `p`
2. Check if it matches the pattern `NatProd.pair x y`
3. If it does, bind `x` to the first component and `y` to the second component
4. Then evaluate the expression after `=>`

Since `NatProd` only has one constructor, `pair`, any value of type `NatProd` will
match this pattern. The variables `x` and `y` are then bound to the two components
of the pair, which we can use in the body of the function.
-/

/-!
### Creating a More Convenient Notation for Pairs

Writing `NatProd.pair` every time we want to create a pair is tedious. Let's define
a more convenient notation using the familiar mathematical syntax for pairs: (x, y).
Since Lean provides its own syntactic sugar for pair, we use `NatProd(,)` for this
case.
-/

-- Define notation for pairs to make them more readable
notation "NatProd(" x ", " y ")" => NatProd.pair x y

-- Now we can use the more familiar notation
#eval NatProd(3, 5).fst  -- This is much cleaner!

-- Let's test some more examples with the new notation
#eval NatProd(42, 99).snd  -- Should evaluate to 99
#eval NatProd(0, NatProd(5, 6).fst).fst  -- Should evaluate to 0


/-!
In Lean, the `notation` directive lets us define custom syntax. Here, we've defined
the notation "(" x ", " y ")" to mean `NatProd.pair x y`. This makes our code much
more readable, as it uses the familiar mathematical notation for pairs.

Note that the notation is just syntactic sugar - it doesn't change the underlying
implementation. The expression `(3, 5)` is still represented internally as
`NatProd.pair 3 5`.
-/

-- We can now rewrite our projection functions using the notation
def NatProd.fst' (p : NatProd) : Nat :=
  match p with
  | NatProd(x, y) => x  -- Using the pair notation in pattern matching

def NatProd.snd' (p : NatProd) : Nat :=
  match p with
  | NatProd(x, y) => y  -- Using the pair notation in pattern matching

-- Let's define a function to swap the elements of a pair
def NatProd.swap (p : NatProd) : NatProd :=
  match p with
  | NatProd(x, y) => NatProd(y, x)  -- Create a new pair with components swapped

-- Let's test our swap function
#eval (NatProd(3, 5).swap).fst  -- Should be 5
#eval (NatProd(3, 5).swap).snd  -- Should be 3

/-!
The `swapPair` function demonstrates how we can both decompose and construct pairs
in a single operation. It takes a pair, extracts its components using pattern matching,
and then constructs a new pair with the components in the opposite order.

Notice how pattern matching makes this very elegant: we directly write down the
structure of the data we expect (`(x, y)`) and then use the bound variables (`x` and `y`)
to construct the result.
-/

/-!
### Understanding Pattern Matching Syntax

It's important to distinguish between:
1. Pattern matching on a pair: `match p with | (x, y) => ...`
2. Pattern matching on multiple values: `match n, m with | _, _ => ...`

The parentheses make a crucial difference! In the first case, we're matching on a
single value of type `NatProd`. In the second case, we would be matching on two
separate values.
-/

-- This would NOT work (syntax error):
-- def badFst (p : NatProd) : Nat :=
--   match p with
--   | x, y => x    -- Can't match a single value with multiple patterns

/-!
The commented-out code above would fail because we're trying to match a single value `p`
against two patterns `x` and `y`. But pattern matching syntax expects either a single
pattern for each value, or multiple values being matched against multiple patterns.

The correct approach is to use the constructor pattern `(x, y)` which tells Lean
that we're expecting a pair and want to bind its components to the variables `x` and `y`.
-/

-- Here's an example of matching on multiple values (different from matching on a pair)
def maxTwo (n m : Nat) : Nat :=
  match n, m with
  | 0, m => m         -- If first number is 0, return the second
  | n, 0 => n         -- If second number is 0, return the first
  | n, m => if n > m then n else m  -- Otherwise compare them

-- Testing the multiple-value pattern matching
#eval maxTwo 3 7  -- Should return 7
#eval maxTwo 9 2  -- Should return 9
#eval maxTwo 0 5  -- Should return 5

/-!
### Proving Facts About Pairs

Now that we have defined pairs and operations on them, we can prove
theorems about their behavior. Proofs in Lean are constructive - we build
evidence that demonstrates the truth of our claims.
-/

-- Use explicit constructor to avoid ambiguity
theorem surjectivePairing' : ∀ n m : Nat, NatProd.pair n m = NatProd.pair NatProd(n, m).fst NatProd(n, m).snd := by
  intro n m
  eq_refl  -- This works because both sides are syntactically the same after evaluation

/-!
The theorem `surjectivePairing'` states that for any pair `(n, m)`, if we extract its
components using `fst` and `snd` and then construct a new pair with those components,
we get back the original pair. This may seem obvious, but it's important to prove
formally.

The proof is a single line: `eq_refl`, which stands for "reflexivity". This tactic
proves goals of the form `X = X`. Lean automatically evaluates `fst (NatProd.pair n m)`
to `n` and `snd (NatProd.pair n m)` to `m`, making the right side identical to the left.
-/

-- But if we state it more generally, we need to destructure:
theorem surjectivePairing : ∀ p : NatProd, p = NatProd.pair p.fst p.snd := by
  intro p
  match p with
  | NatProd(n, m) => eq_refl  -- Or: cases p with | pair n m => eq_refl

/-!
The theorem `surjectivePairing` states the same property but for an arbitrary pair `p`,
rather than a pair explicitly constructed as `NatProd.pair n m`. This makes the proof
a bit more complex.

We can't just use `eq_refl` directly because Lean doesn't automatically unfold the
definition of an arbitrary pair `p`. Instead, we need to explicitly pattern match
on `p` to expose its structure. Once we've done that, we can use `eq_refl` to complete
the proof.

This pattern of "expose the structure, then prove by simplification" is very common
in formal verification.
-/

-- EXERCISE: 1 star, standard (snd_fst_is_swap)
theorem sndFstIsSwap : ∀ p : NatProd, NatProd.pair p.snd p.fst = p.swap := by
  intro p
  -- Hint: Think about how to expose the structure of p
  -- Then consider how swapPair is defined
  sorry  -- TODO: Prove this

-- EXERCISE: 1 star, standard, optional (fst_swap_is_snd)
theorem fstSwapIsSnd : ∀ p : NatProd, p.swap.fst = p.snd := by
  intro p
  -- Hint: First understand what the theorem is stating in plain language
  -- Then think about the definitions of fst, swapPair, and snd
  sorry  -- TODO: Prove this


/-!
## Using structure to organize data
Though we defined `NatProd` with inductive type, it can be observed that we have
exactly defined one *constructor*, which takes two necessary components to yield
a term of type `NatProd`. Also, from the above equalities, we can conclude that
a term is determined by the two components, i.e.,  *projections* `fst` and `snd`.

For such a type with only one constructor, Lean provides a syntactic sugar
called *structure*.
-/

structure AnotherNatProd where
  fst: Nat
  snd: Nat


#check AnotherNatProd.mk 0 1

/-!
As shown in the syntax, you only have to specify all the *fields* (components) of
the type. Lean will then use *type_name*.mk as the unique constructor. And the field
names are automatically the projections.
-/

#eval (AnotherNatProd.mk 0 1).fst

/-!
> You may want to use a different name for the constructor. Lean allows you to
> change the default name by writting a `::`.
> ```lean
> structure NatProd where
>   pair ::
>     fst: Nat
>     snd: Nat
> ```
-/

/-!
Besides, Lean also provides a semantic way to write a term and to get a new term
based on it.
-/

def some_pair: AnotherNatProd := { fst := 1, snd := 2}
def another_pair := {
    some_pair with
      snd := 3
  }
#eval another_pair.fst  -- 1
#eval another_pair.snd  -- 3
#eval some_pair.snd  -- 2

/-!
You can also omit the names of the fields like `fst`, `snd`. This time, we use angled
brackets to enclose them.
-/
def a_third_pair: AnotherNatProd := ⟨7, 2⟩
#eval a_third_pair.fst -- 7
#eval a_third_pair.snd -- 2

/-!
## Lists of Numbers

Now let's generalize from pairs to lists - data structures that can hold any number
of elements of the same type. While a pair always has exactly two elements, a list
can have any number of elements (including zero).

A list is defined inductively as either:
1. Empty (nil), or
2. An element followed by another list (cons)

This reflects how we intuitively build up lists: we either have nothing (the empty list),
or we take an existing list and add an element to the front.
-/

namespace NatList

inductive NatList : Type
  | nil  : NatList                    -- The empty list
  | cons : Nat → NatList → NatList    -- A natural number followed by a list

/-!
The definition above tells us there are exactly two ways to create a `NatList`:
1. Using `NatList.nil` to create an empty list
2. Using `NatList.cons` to add a number to the front of an existing list

This is a recursive definition: a `NatList` is defined in terms of (another) `NatList`.
This is perfectly valid and is how we build up complex structures from simple ones.
-/

-- Let's create a simple list with three elements: 1, 2, and 3
def myList := NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil))

-- We can check that this has the expected type
#check myList  -- Should be of type NatList

-- We can also create other lists
#check NatList.nil  -- The empty list
#check NatList.cons 5 NatList.nil  -- A list with just the number 5

/-!
As you can see, writing lists with `NatList.cons` and `NatList.nil` is quite verbose
and not very readable. Just as we did with pairs, let's define some convenient notation
for working with lists.
-/

-- Infix operator for cons (adds an element to the front of a list)
scoped infixr:67 " :: " => NatList.cons

-- Empty list notation
scoped notation "[]" => NatList.nil

/-!
> The `scoped` prefix indicates that the new notation is only available in current
> namespace.

The `infixr:67 " :: " => NatList.cons` declaration defines a right-associative
infix operator `::` with precedence 67 that represents the `cons` constructor.
This lets us write `1 :: l` instead of `NatList.cons 1 l`.

The `notation "[]" => NatList.nil` declaration lets us write `[]` instead of
`NatList.nil` for the empty list.

The precedence level 67 and associativity (right) are chosen to match conventional
list notation in other languages and to ensure expressions are parsed correctly
when combined with other operators.
-/

-- Using the cons operator
def myList1 := 1 :: (2 :: (3 :: []))  -- Add 1, then 2, then 3 to empty list
def myList2 := 1 :: 2 :: 3 :: []      -- Same list, using right-associativity

-- Let's check that these are the same
#check myList1
#check myList2

-- We can verify they're the same list by checking their structure
example : myList1 = myList2 := by eq_refl  -- The proof succeeds, confirming equality

/-!
Now let's implement some fundamental operations on lists. These will form the
building blocks for more complex list manipulation.
-/

-- Repeat: creates a list with `count` copies of `n`
def repeatN (n : Nat) (count : Nat) : NatList :=
  match count with
  | 0 => []                           -- Base case: empty list
  | Nat.succ count' => n :: repeatN n count'  -- Recursive case: add n and repeat

/-!
The `repeatN` function works recursively:
1. For `count = 0`, it returns the empty list
2. For `count > 0`, it adds `n` to the front of a list with `count-1` copies of `n`

This is a common pattern in functional programming: handle a base case directly,
and handle other cases by reducing to a smaller problem.
-/

-- Let's test repeatN with some examples
#eval repeatN 7 3  -- Should create [7, 7, 7]
#eval repeatN 0 5  -- Should create [0, 0, 0, 0, 0]
#eval repeatN 9 0  -- Should create [], the empty list

/-!
Next, let's implement a function to calculate the length of a list:
-/

-- Length: counts the number of elements
def length (l : NatList) : Nat :=
  match l with
  | [] => 0                           -- Empty list has length 0
  | _ :: t => Nat.succ (length t)     -- Non-empty list: 1 + length of tail

/-!
The `length` function also works recursively:
1. For the empty list `[]`, it returns 0
2. For a non-empty list `h :: t`, it returns 1 plus the length of `t`

Notice the use of the wildcard pattern `_` for the head of the list. Since we don't
need the value of the head to compute the length, we can ignore it with a wildcard.
-/

-- Let's test length with some examples
#eval length []               -- Should be 0
#eval length (1 :: [])        -- Should be 1
#eval length (1 :: 2 :: 3 :: [])  -- Should be 3

/-!
Now let's implement a function to append (concatenate) two lists:
-/

-- Append: concatenates two lists
def app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2                          -- If first list is empty, return second list
  | h :: t => h :: (app t l2)         -- Otherwise, add head to (append of tail and l2)

/-!
The `app` function recursively builds a new list:
1. If the first list is empty, it returns the second list
2. If the first list is non-empty, it adds the head to the result of appending
   the tail of the first list with the second list

Notice that we only pattern match on the first list, not both. This is because
the function is recursive on the structure of the first list - we process it
element by element, prepending each to the second list.
-/

-- Infix notation for append
infixl:65 " ++ " => app

-- Testing append with examples
#eval [] ++ (1 :: 2 :: [])        -- Should be [1, 2]
#eval (1 :: 2 :: []) ++ []        -- Should be [1, 2]
#eval (1 :: []) ++ (2 :: 3 :: []) -- Should be [1, 2, 3]

-- Example with explicit NatList constructors
def exampleList1 : NatList := 1 :: 2 :: 3 :: []
def exampleList2 : NatList := 4 :: 5 :: []
example : exampleList1 ++ exampleList2 = 1 :: 2 :: 3 :: 4 :: 5 :: [] := by eq_refl

/-!
Finally, let's implement the standard head and tail operations for lists:
-/

-- Head (hd): returns the first element, or a default if the list is empty
def hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default                     -- Empty list: return the default value
  | h :: _ => h                       -- Non-empty list: return the head

-- Tail (tl): returns all but the first element, or empty list if already empty
def tl (l : NatList) : NatList :=
  match l with
  | [] => []                          -- Empty list: return empty list
  | _ :: t => t                       -- Non-empty list: return the tail

/-!
The `hd` function extracts the first element of a list, or returns a default value
if the list is empty. The `tl` function returns everything but the first element,
or an empty list if the input is empty.

Both functions handle the empty list case specially to prevent errors.
-/

-- Testing head and tail
#eval hd 0 []                     -- Should be 0 (the default value)
#eval hd 0 (1 :: 2 :: 3 :: [])    -- Should be 1
#eval tl []                       -- Should be []
#eval tl (1 :: 2 :: 3 :: [])      -- Should be [2, 3]

-- We can compose head and tail
#eval hd 0 (tl (1 :: 2 :: 3 :: []))  -- Should be 2 (the head of the tail)

/-!
Now let's move on to some exercises where you can practice working with lists!
-/

-- EXERCISE: 2 stars, standard, especially useful (list_funs)
-- Complete these definitions

/-!
The `nonzeros` function should remove all zeros from a list.
For example, `nonzeros [0, 1, 0, 2, 3, 0, 0]` should return `[1, 2, 3]`.

Think about how to process the list recursively:
1. What should happen for the empty list?
2. What should happen when the head is 0?
3. What should happen when the head is not 0?
-/
def nonzeros (l : NatList) : NatList :=
  match l with
  | [] => [] -- Empty list: return empty list
  | h :: t =>
    if h == 0 then
      nonzeros t -- Skip zero and process the rest
    else
      h :: nonzeros t -- Keep non-zero and process the rest
  -- You need to implement this function

example : nonzeros (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: []) = 1 :: 2 :: 3 :: [] := by
  -- Verify that nonzeros removes all zeros
  eq_refl -- If your implementation is correct, this should work

/-!
The `oddMembers` function should keep only the odd numbers from a list.
For example, `oddMembers [0, 1, 0, 2, 3, 0, 0]` should return `[1, 3]`.

Remember that a number is odd if it's not evenly divisible by 2.
In Lean, you can use `n % 2 == 1` to check if `n` is odd.
-/
def oddMembers (l : NatList) : NatList :=
  match l with
  | [] => [] -- Empty list case
  | h :: t =>
    if h % 2 == 1 then
      h :: oddMembers t -- Keep odd numbers
    else
      oddMembers t -- Skip even numbers
  -- You need to implement this function

example : oddMembers (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: []) = 1 :: 3 :: [] := by
  -- Verify that oddMembers keeps only odd numbers
  eq_refl -- If your implementation is correct, this should work

/-!
The `countOddMembers` function should count how many odd numbers are in a list.
For example, `countOddMembers [1, 0, 3, 1, 4, 5]` should return `4`.

This function could be implemented directly, but try to use `oddMembers` and
`length` to make your solution more elegant.
-/
def countOddMembers (l : NatList) : Nat :=
  length (oddMembers l) -- Length of the list of odd members
  -- You need to implement this function

example : countOddMembers (1 :: 0 :: 3 :: 1 :: 4 :: 5 :: []) = 4 := by
  -- Verify that countOddMembers counts correctly
  eq_refl -- If your implementation is correct, this should work

-- EXERCISE: 3 stars, advanced (alternate)
-- Interleave elements from two lists

/-!
The `alternate` function should take two lists and return a new list that contains
elements from both lists, alternating between them.

For example, `alternate [1, 2, 3] [4, 5, 6]` should return `[1, 4, 2, 5, 3, 6]`.

If one list is longer than the other, the remaining elements should be included at the end.
For example, `alternate [1] [4, 5, 6]` should return `[1, 4, 5, 6]`.

This requires pattern matching on both lists simultaneously:
-/
def alternate (l1 l2 : NatList) : NatList :=
  match l1, l2 with
  | [], l2 => l2                           -- If first list is empty, return second list
  | l1, [] => l1                           -- If second list is empty, return first list
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2  -- Take heads from both, then recurse
  -- You need to implement this function

example : alternate (1 :: 2 :: 3 :: []) (4 :: 5 :: 6 :: []) = 1 :: 4 :: 2 :: 5 :: 3 :: 6 :: [] := by
  -- Verify that alternate interleaves the lists
  eq_refl -- If your implementation is correct, this should work

-- Let's test alternate with lists of different lengths
example : alternate (1 :: []) (4 :: 5 :: 6 :: []) = 1 :: 4 :: 5 :: 6 :: [] := by
  eq_refl -- First list runs out first

example : alternate (1 :: 2 :: 3 :: []) (4 :: []) = 1 :: 4 :: 2 :: 3 :: [] := by
  eq_refl -- Second list runs out first

example : alternate [] (4 :: 5 :: []) = 4 :: 5 :: [] := by
  eq_refl -- First list is empty

/-!
## Bags (Multisets) via Lists

A bag, or multiset, is like a set except elements can appear multiple times.
For example, in a regular set, {1, 2, 1} would be the same as {1, 2}. But in a
bag, [1, 2, 1] is different from [1, 2] because the element 1 appears twice.

We can represent bags using lists, where each element's multiplicity (how many times
it appears) matters:
-/

def Bag := NatList  -- A bag is just a list of natural numbers

/-!
Now let's implement several operations on bags. These functions will let us count
elements, combine bags, and check properties of bags.
-/

-- EXERCISE: 3 stars, standard, especially useful (bag_functions)
-- Implement fundamental bag operations

/-!
The `count` function should count how many times a value appears in a bag.
For example, `count 1 [1, 2, 3, 1, 4, 1]` should return `3` because 1 appears
three times in the list.
-/
def count (v : Nat) (s : Bag) : Nat :=
  match s with
  | [] => 0                           -- Empty bag: count is 0
  | h :: t =>
    if h == v then
      1 + count v t  -- Found one, add 1 to the count in the rest
    else
      count v t      -- Not a match, just count the rest
  -- You need to implement this function

example : count 1 (1 :: 2 :: 3 :: 1 :: 4 :: 1 :: []) = 3 := by
  -- Verify that count counts correctly
  eq_refl -- If your implementation is correct, this should work

/-!
The `sum` function should combine two bags by concatenating their lists.
For example, `sum [1, 2, 3] [1, 4, 1]` would return a bag where `count 1`
yields 3, since 1 appears once in the first bag and twice in the second.
-/
-- Sum combines two bags
def sum : Bag → Bag → Bag :=
  app  -- We can just use the append function we defined earlier
  -- You need to implement this function

example : count 1 (sum (1 :: 2 :: 3 :: []) (1 :: 4 :: 1 :: [])) = 3 := by
  -- Verify that sum works correctly with count
  eq_refl -- If your implementation is correct, this should work

/-!
The `add` function should add a value to a bag (increasing its multiplicity by 1).
For example, `add 1 [1, 4, 1]` should return a bag where `count 1` yields 3.
-/
def add (v : Nat) (s : Bag) : Bag :=
  v :: s  -- Just add the value to the front of the list
  -- You need to implement this function

example : count 1 (add 1 (1 :: 4 :: 1 :: [])) = 3 := by
  -- Verify that add increases the count correctly
  eq_refl -- If your implementation is correct, this should work

/-!
The `member` function should check if a value appears at least once in a bag.
For example, `member 1 [1, 4, 1]` should return `true`, but `member 2 [1, 4, 1]`
should return `false`.
-/
def member (v : Nat) (s : Bag) : Bool :=
  match s with
  | [] => false                       -- Empty bag: not a member
  | h :: t =>
    if h == v then
      true            -- Found it!
    else
      member v t      -- Check the rest
  -- You need to implement this function

example : member 1 (1 :: 4 :: 1 :: []) = true := by
  -- Verify that member works correctly for present values
  eq_refl -- If your implementation is correct, this should work

example : member 2 (1 :: 4 :: 1 :: []) = false := by
  -- Verify that member works correctly for absent values
  eq_refl -- If your implementation is correct, this should work

-- EXERCISE: 3 stars, standard, optional (bag_more_functions)
-- More complex bag operations

/-!
The `removeOne` function should remove one occurrence of a value from a bag.
If the value isn't in the bag, the bag should be returned unchanged.
For example, `removeOne 5 [2, 1, 5, 4, 1]` should return `[2, 1, 4, 1]`.
-/
def removeOne (v : Nat) (s : Bag) : Bag :=
  match s with
  | [] => []                          -- Empty bag: nothing to remove
  | h :: t =>
    if h == v then
      t               -- Found it, remove by returning just the tail
    else
      h :: removeOne v t  -- Not found yet, keep head and look in tail
  -- You need to implement this function

-- Tests for removeOne
example : count 5 (removeOne 5 (2 :: 1 :: 5 :: 4 :: 1 :: [])) = 0 := by
  -- Verify that removeOne removes exactly one occurrence
  eq_refl -- If your implementation is correct, this should work

example : count 5 (removeOne 5 (2 :: 1 :: 4 :: 1 :: [])) = 0 := by
  -- Verify that removeOne handles absence correctly
  eq_refl -- If your implementation is correct, this should work

/-!
The `removeAll` function should remove all occurrences of a value from a bag.
For example, `removeAll 5 [2, 1, 5, 4, 5, 1, 4]` should return `[2, 1, 4, 1, 4]`.
-/
def removeAll (v : Nat) (s : Bag) : Bag :=
  match s with
  | [] => []                          -- Empty bag: nothing to remove
  | h :: t =>
    if h == v then
      removeAll v t   -- Found one, skip it and continue removing
    else
      h :: removeAll v t  -- Not a match, keep head and continue
  -- You need to implement this function

-- Tests for removeAll
example : count 5 (removeAll 5 (2 :: 1 :: 5 :: 4 :: 5 :: 1 :: 4 :: [])) = 0 := by
  -- Verify that removeAll removes all occurrences
  eq_refl -- If your implementation is correct, this should work

/-!
The `included` function should check if one bag is included in another.
A bag s1 is included in a bag s2 if every element in s1 appears in s2 with
at least the same multiplicity.
For example, `included [1, 2] [2, 1, 4, 1]` should return `true`, but
`included [1, 2, 2] [2, 1, 4, 1]` should return `false` (because 2 appears
twice in the first bag but only once in the second).
-/
def included (s1 s2 : Bag) : Bool :=
  match s1 with
  | [] => true                        -- Empty bag is included in any bag
  | h :: t =>
    if member h s2 then
      included t (removeOne h s2)  -- Check if the rest is included after removing one h
    else
      false  -- Not included if any element is missing
  -- You need to implement this function

-- Tests for included
example : included (1 :: 2 :: []) (2 :: 1 :: 4 :: 1 :: []) = true := by
  -- Verify that included works for actual inclusion
  eq_refl -- If your implementation is correct, this should work

example : included (1 :: 2 :: 2 :: []) (2 :: 1 :: 4 :: 1 :: []) = false := by
  -- Verify that included checks multiplicities correctly
  eq_refl -- If your implementation is correct, this should work

/-!
## Reasoning About Lists

Now that we've defined lists and operations on them, we can start proving
properties about them. This is where the power of formal verification really
shines - we can prove with mathematical certainty that our functions behave
as expected.

Many facts about lists can be proved by simplification:
-/

theorem nilApp : ∀ l : NatList, [] ++ l = l := by
  intro l
  eq_refl  -- Works because `[]` in `app` matches the first pattern

/-!
The theorem `nilApp` states that appending any list to the empty list gives back
the original list. This is a basic property of appending that follows directly
from the definition of `app`. When the first list is empty, `app` immediately
returns the second list.

The proof is a single line: `eq_refl` (reflexivity), which works because Lean can
automatically simplify `[] ++ l` to `l` based on the definition of `app`.
-/

-- But for more complex proofs, we need case analysis:
theorem tlLengthPred : ∀ l : NatList, Nat.pred (length l) = length (tl l) := by
  intro l
  cases l with
  | nil => eq_refl                        -- For empty list, both sides are 0
  | cons _ _ => eq_refl                   -- For non-empty list, both sides simplify to same value

/-!
The theorem `tlLengthPred` states that the predecessor of the length of a list
is equal to the length of the tail of the list. This makes intuitive sense:
removing the first element reduces the length by 1.

The proof uses case analysis with the `cases` tactic to handle two cases:
1. When `l` is the empty list (`nil`), both sides evaluate to 0
2. When `l` is a non-empty list (`cons _ _`), simplification gives the desired result

Case analysis is a fundamental proof technique where we consider all possible
forms the data could take and prove the property for each form separately.
-/

/-!
## Induction on Lists

For more complex properties, we often need induction, not just case analysis.
Induction is like case analysis but with an extra "inductive hypothesis" that
lets us build up from simple cases to complex ones.

The principle of induction on lists says:
1. Prove the property for the empty list
2. Prove that if it holds for a list, it holds when we add an element to the front

This is a powerful technique that lets us prove properties about lists of any length.
-/

theorem appAssoc : ∀ l1 l2 l3 : NatList, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  intro l1 l2 l3
  induction l1 with
  | nil =>                            -- Base case: l1 = []
    simp [app]                        -- Simplify using the definition of app
    -- Now we have l2 ++ l3 = l2 ++ l3, which is true by reflexivity
  | cons n l1' ih =>                  -- Inductive case: l1 = n :: l1'
    simp [app]                        -- Simplify using the definition of app
    -- Now we have n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3))
    -- We need to show the parts inside the n :: ... are equal
    rw [ih]                           -- Use the induction hypothesis
    -- Now we have n :: (l1' ++ (l2 ++ l3)) = n :: (l1' ++ (l2 ++ l3))

/-!
The theorem `appAssoc` states that append is associative, meaning that
`(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)` for any lists `l1`, `l2`, and `l3`.
In other words, it doesn't matter how we group the appends - we get the same
result either way.

The proof uses induction on `l1`:

1. Base case (`l1 = []`): We need to show `length ([] ++ l2) = length [] + length l2`.
   By the definition of `app` and `length`, this simplifies to
   `length l2 = 0 + length l2`, which is true.

2. Inductive case (`l1 = n :: l1'`): We need to show
   `length ((n :: l1') ++ l2) = length (n :: l1') + length l2`.
   By the definition of `app`, this simplifies to
   `1 + length (l1' ++ l2) = 1 + length l1' + length l2`.
   We have an induction hypothesis `ih` that tells us
   `length (l1' ++ l2) = length l1' + length l2`.
   Using this, the goal becomes `1 + (length l1' + length l2) = 1 + length l1' + length l2`.
   This requires some arithmetic properties to rearrange the terms:
   - Associativity: `1 + (length l1' + length l2) = 1 + length l1' + length l2`
   - Commutativity: We can swap the order of terms
   These properties let us complete the proof.

Now we can use this lemma to prove that reversing a list preserves its length:
-/

-- Definition of rev (reverse a list)
def rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => rev t ++ (h :: [])


theorem revLength : ∀ l : NatList, length (rev l) = length l := by
  intro l
  induction l
  case nil => eq_refl
  case cons n l' ih => sorry -- We'll complete this proof later


/-!
The theorem `revLength` states that reversing a list doesn't change its length.
Again, this is an intuitive property that we'd expect to hold.

The proof uses induction on `l`:

1. Base case (`l = []`): We need to show `length (rev []) = length []`.
   Both sides simplify to 0, so this is true by reflexivity.

2. Inductive case (`l = n :: l'`): We need to show
   `length (rev (n :: l')) = length (n :: l')`.
   By the definition of `rev`, this becomes
   `length (rev l' ++ (n :: [])) = 1 + length l'`.
   Using the `appLength` lemma, this becomes
   `length (rev l') + length (n :: []) = 1 + length l'`.
   Simplifying `length (n :: [])` to 1, we get
   `length (rev l') + 1 = 1 + length l'`.
   The induction hypothesis `ih` tells us `length (rev l') = length l'`.
   Substituting this, we get `length l' + 1 = 1 + length l'`.
   By commutativity of addition, this is true.

Now let's move on to some exercises where you can practice proving properties
about lists:
-/

-- EXERCISE: 3 stars, standard (list_exercises)
-- More list properties to prove

/-!
The `appNilR` theorem should state that appending an empty list to the end of
any list leaves the list unchanged.

More formally: For all lists l, l ++ [] = l.

This is a natural counterpart to `nilApp` which we proved earlier.
-/
theorem appNilR : ∀ l : NatList, l ++ [] = l := by
  intro l
  induction l with
  | nil =>
    -- We need to show [] ++ [] = []
    eq_refl -- This is true by definition of app
  | cons h t ih =>
    -- We need to show (h :: t) ++ [] = h :: t
    -- By definition of app, this is h :: (t ++ []) = h :: t
    simp [app]
    rw [ih]

/-!
The `revAppDistr` theorem should state that reversing a concatenation of two lists
is the same as concatenating the reversed lists in the opposite order.

More formally: For all lists l1 and l2, rev (l1 ++ l2) = rev l2 ++ rev l1.

This property is less intuitive but very useful in proofs about reversed lists.
-/
theorem revAppDistr : ∀ l1 l2 : NatList, rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  intro l1 l2
  induction l1 with
  | nil =>
    -- Base case: we need to show rev ([] ++ l2) = rev l2 ++ rev []
    -- This simplifies to rev l2 = rev l2 ++ []
    simp [app, rev]
    rw [appNilR]
  | cons h t ih =>
    -- Inductive case: we need to show rev ((h :: t) ++ l2) = rev l2 ++ rev (h :: t)
    -- By definition of app and rev:
    -- rev (h :: (t ++ l2)) = rev l2 ++ (rev t ++ (h :: []))
    -- which is rev (t ++ l2) ++ (h :: []) = rev l2 ++ (rev t ++ (h :: []))
    -- By IH: rev (t ++ l2) = rev l2 ++ rev t
    -- So we need: (rev l2 ++ rev t) ++ (h :: []) = rev l2 ++ (rev t ++ (h :: []))
    -- This requires associativity of append
    simp [app, rev]
    rw [ih]
    -- Now we need to show (rev l2 ++ rev t) ++ [h] = rev l2 ++ (rev t ++ [h])
    rw [appAssoc]

/-!
The `revInvolutive` theorem should state that reversing a list twice gives back
the original list.

More formally: For all lists l, rev (rev l) = l.

This is a property known as involutivity, which means that applying a function
twice gets you back to where you started.
-/
theorem revInvolutive : ∀ l : NatList, rev (rev l) = l := by
  intro l
  induction l with
  | nil =>
    -- Base case: rev (rev []) = []
    simp [rev]
  | cons h t ih =>
    -- Inductive case: rev (rev (h :: t)) = h :: t
    -- By definition: rev (rev t ++ [h]) = h :: t
    -- We need to use revAppDistr to handle rev (rev t ++ [h])
    simp [rev]
    rw [revAppDistr]
    -- Now we have rev [h] ++ rev (rev t) = h :: t
    -- By IH: rev (rev t) = t
    simp [rev]
    rw [ih]
    -- Now we have [h] ++ t = h :: t
    simp [app]

-- EXERCISE: 2 stars, standard (eqblist)
-- Define equality for lists

/-!
The `eqblist` function should check if two lists are equal element by element.
For example, `eqblist [1, 2, 3] [1, 2, 3]` should return `true`, but
`eqblist [1, 2, 3] [1, 2, 4]` should return `false`.

To implement this function, think about:
1. What happens when both lists are empty?
2. What happens when one list is empty and the other isn't?
3. What happens when the heads are equal? What about when they're different?
-/
def eqblist (l1 l2 : NatList) : Bool :=
  match l1, l2 with
  | [], [] => true                    -- Empty lists are equal
  | [], _ => false                    -- Empty list is not equal to non-empty list
  | _, [] => false                    -- Non-empty list is not equal to empty list
  | h1 :: t1, h2 :: t2 =>
    if h1 == h2 then
      eqblist t1 t2  -- Heads equal, recursively check tails
    else
      false          -- Heads different, lists not equal
  -- You need to implement this function

/-!
Now prove that `eqblist` is reflexive, meaning that any list is equal to itself.
More formally: For all lists l, eqblist l l = true.
-/
theorem eqblistRefl : ∀ l : NatList, eqblist l l = true := by
  intro l
  induction l
  case nil =>
    unfold eqblist
    eq_refl
  case cons h t ih =>
    unfold eqblist
    simp
    exact ih

/-!
## Options

What if we want to extract an element from a position that might not exist?
For example, trying to get the head of an empty list would cause problems.
We need a type that can represent "no value" in addition to actual values.

The `Option` type handles this elegantly:
-/

inductive NatOption : Type
  | some : Nat → NatOption              -- A value is present
  | none : NatOption                     -- No value is present

/-!
The `NatOption` type has two constructors:
1. `some` takes a natural number and represents the presence of a value
2. `none` represents the absence of a value (like when a list is empty)

This lets us write functions that might not always return a value, such as
safely extracting an element from a list:
-/

-- Now we can safely extract the nth element
def nthError (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => NatOption.none               -- Empty list: no nth element exists
  | a :: l' =>
    match n with
    | 0 => NatOption.some a           -- n = 0: return the head
    | Nat.succ n' => nthError l' n'   -- n > 0: look in the tail at position n-1


/-!
The `nthError` function returns the nth element of a list as an option:
- If the list is empty or n is beyond the end of the list, it returns `none`
- Otherwise, it returns `some a` where `a` is the element at position n

This is safer than returning an arbitrary default value because it explicitly
tells us whether the requested element exists.
-/

-- Testing nthError with examples
example : nthError (4 :: 5 :: 6 :: 7 :: []) 0 = NatOption.some 4 := by eq_refl
example : nthError (4 :: 5 :: 6 :: 7 :: []) 3 = NatOption.some 7 := by eq_refl
example : nthError (4 :: 5 :: 6 :: 7 :: []) 9 = NatOption.none := by eq_refl

/-!
Sometimes we still need to extract a value from an option, defaulting to some
value if the option is `none`. The `optionElim` function handles this:
-/

-- Extract value with a default
def optionElim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | NatOption.some n' => n'            -- If some value is present, return it
  | NatOption.none => d                -- If no value, return the default

-- Testing optionElim with examples
example : optionElim 0 (NatOption.some 4) = 4 := by eq_refl
example : optionElim 0 NatOption.none = 0 := by eq_refl

-- EXERCISE: 2 stars, standard (hd_error)
-- Safe head function using options

/-!
The `hdError` function should be a safer version of `hd` that returns an option
instead of requiring a default value.

For example:
- `hdError []` should return `none` (no head exists)
- `hdError [1]` should return `some 1` (the head is 1)
-/
def hdError (l : NatList) : NatOption :=
  match l with
  | [] => NatOption.none              -- Empty list: no head exists
  | h :: _ => NatOption.some h        -- Non-empty list: return the head
  -- You need to implement this function

example : hdError [] = NatOption.none := by
  -- Verify that hdError handles empty lists correctly
  eq_refl -- If your implementation is correct, this should work

example : hdError (1 :: []) = NatOption.some 1 := by
  -- Verify that hdError handles non-empty lists correctly
  eq_refl -- If your implementation is correct, this should work

example : hdError (5 :: 6 :: []) = NatOption.some 5 := by
  -- Another test for hdError
  eq_refl -- If your implementation is correct, this should work

/-!
## Partial Maps

As a final example, let's build a simple dictionary (partial map) data structure.
A partial map associates keys with values, but not every key needs to have an
associated value.
-/

-- Keys for our map
inductive Identifier : Type
  | mk : Nat → Identifier                -- A simple identifier with a number

/-!
For simplicity, we'll use natural numbers wrapped in an `Identifier` type as our keys.
This gives us flexibility to change the implementation later if needed.
-/

-- Equality test for keys
def eqbId (x1 x2 : Identifier) : Bool :=
  match x1, x2 with
  | Identifier.mk n1, Identifier.mk n2 => n1 == n2  -- Compare the underlying numbers

-- EXERCISE: 1 star, standard (eqb_id_refl)
theorem eqbIdRefl : ∀ x : Identifier, eqbId x x = true := by
  intro x
  cases x with
  | mk n =>
    -- We need to show eqbId (Identifier.mk n) (Identifier.mk n) = true
    -- This simplifies to n == n = true
    simp [eqbId]
    -- The equality check on equal natural numbers returns true

-- The partial map type
inductive PartialMap : Type
  | empty : PartialMap                  -- Empty map
  | record : Identifier → Nat → PartialMap → PartialMap  -- Map with an entry and a rest

/-!
The `PartialMap` type is defined inductively:
1. `empty` represents an empty map with no entries
2. `record i v m` represents a map with an entry mapping identifier `i` to value `v`,
   followed by the rest of the map `m`

This is a simple implementation where later entries can shadow earlier ones
with the same key.
-/

-- Update adds or overrides a key-value pair
def update (d : PartialMap) (x : Identifier) (value : Nat) : PartialMap :=
  PartialMap.record x value d          -- Add new entry at the front

/-!
The `update` function adds a new entry to a map, mapping the key `x` to the value `value`.
If `x` is already mapped in `d`, the new entry will shadow the old one when searching.
-/

-- Find searches for a key
def find (x : Identifier) (d : PartialMap) : NatOption :=
  match d with
  | PartialMap.empty => NatOption.none  -- Empty map: key not found
  | PartialMap.record y v d' =>
    if eqbId x y then
      NatOption.some v                  -- Key found: return associated value
    else
      find x d'                         -- Key not found yet: look in the rest of the map

/-!
The `find` function searches for a key in a map:
- If the map is empty, it returns `none` (key not found)
- If the first entry's key matches the target, it returns `some v` with the associated value
- Otherwise, it recursively searches the rest of the map

This implementation does a linear search through the entries, checking each key
in order until it finds a match or runs out of entries.
-/

-- EXERCISE: 1 star, standard (update_eq)
theorem updateEq : ∀ (d : PartialMap) (x : Identifier) (v : Nat),
    find x (update d x v) = NatOption.some v := by
  intro d x v
  -- The key insight: when we add a new entry with key x, then search for x,
  -- we'll find the entry we just added
  unfold update find
  rw [eqbIdRefl x]
  simp

-- EXERCISE: 1 star, standard (update_neq)
theorem updateNeq : ∀ (d : PartialMap) (x y : Identifier) (o : Nat),
    eqbId x y = false → find x (update d y o) = find x d := sorry

end NatList
