/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan and Robert Joseph George

This file is a Lean 4 translation of the "Maps" chapter from Software Foundations
(Logical Foundations).
-/

/-!
# Maps

Maps (or dictionaries) are ubiquitous data structures both in ordinary programming
and in the theory of programming languages; we're going to need them in many places
in the coming chapters.

They also make a nice case study using ideas we've seen in previous chapters, including
building data structures out of higher-order functions (from Basics and Poly) and the
use of reflection to streamline proofs (from IndProp).

We'll define two flavors of maps: total maps, which include a "default" element to be
returned when a key being looked up doesn't exist, and partial maps, which instead
return an option to indicate success or failure. The latter is defined in terms of
the former, using `none` as the default element.

## The Lean Standard Library

Unlike the chapters we have seen so far, this one does not import the chapter before it
(nor, transitively, all the earlier chapters). Instead, in this chapter and from now on,
we're going to import the definitions and theorems we need directly from Lean's standard
library. You should not notice much difference, though, because we've been careful to
name our own definitions and theorems the same as their counterparts in the standard
library, wherever they overlap.

In Lean 4, we can import specific modules and use their definitions directly:
-/

-- We'll use String for identifiers and basic logical operations
-- These are available by default in Lean 4

/-!
Documentation for the standard library can be found at https://leanprover-community.github.io/mathlib4_docs/.

The `#check` command is a good way to look for theorems involving objects of specific types.

If you want to find out how or where a notation is defined, you can use `#print` or look
at the documentation. For example, where is the natural addition operation defined?
-/

#check Nat.add
#print Nat.add

/-!
## Identifiers

First, we need a type for the keys that we will use to index into our maps. In Lists
we introduced a fresh type `id` for a similar purpose; here and for the rest of our
development we will use the `String` type from Lean's standard library.

To compare strings, we use the function `String.beq` (or the `==` operator) from Lean's
standard library.
-/

-- In Lean 4, string equality is decidable and we have these properties:
example (a : String) : (a == a) = true := by simp

/-!
We will often use a few basic properties of string equality...
-/

-- String.beq s₁ s₂ = true ↔ s₁ = s₂
example (s1 s2 : String) : (s1 == s2) = true ↔ s1 = s2 := by simp [BEq.beq]

-- In Lean 4, we can use decidable equality directly
example (s1 s2 : String) : Decidable (s1 = s2) := by infer_instance

/-!
## Total Maps

Our main job in this chapter will be to build a definition of partial maps that is
similar in behavior to the one we saw in the Lists chapter, plus accompanying lemmas
about its behavior.

This time around, though, we're going to use functions, rather than lists of key-value
pairs, to build maps. The advantage of this representation is that it offers a more
"extensional" view of maps: two maps that respond to queries in the same way will be
represented as exactly the same function, rather than just as "equivalent" list structures.
This, in turn, simplifies proofs that use maps.

We build up to partial maps in two steps. First, we define a type of total maps that
return a default value when we look up a key that is not present in the map.
-/

def TotalMap (A : Type) := String → A

/-!
Intuitively, a total map over an element type `A` is just a function that can be used
to look up strings, yielding `A`s.

The function `t_empty` yields an empty total map, given a default element; this map
always returns the default element when applied to any string.
-/

def t_empty {A : Type} (v : A) : TotalMap A :=
  fun _ => v

/-!
More interesting is the map-updating function, which (as always) takes a map `m`, a key `x`,
and a value `v` and returns a new map that takes `x` to `v` and takes every other key to
whatever `m` does. The novelty here is that we achieve this effect by wrapping a new
function around the old one.
-/

def t_update {A : Type} (m : TotalMap A) (x : String) (v : A) : TotalMap A :=
  fun x' => if x == x' then v else m x'

/-!
This definition is a nice example of higher-order programming: `t_update` takes a function
`m` and yields a new function `fun x' => ...` that behaves like the desired map.

For example, we can build a map taking strings to bools, where "foo" and "bar" are mapped
to true and every other key is mapped to false, like this:
-/

def examplemap : TotalMap Bool :=
  t_update (t_update (t_empty false) "foo" true) "bar" true

/-!
Next, let's introduce some notations to facilitate working with maps.

First, we use the following notation to represent an empty total map with a default value.
-/

notation "{ " "!->" v " }" => t_empty v

example : TotalMap Bool := { !-> false }

/-!
We next introduce a convenient notation for extending an existing map with a new binding.
-/

notation x " !-> " v " ; " m => t_update m x v

/-!
The `examplemap` above can now be defined as follows:
-/

def examplemap' : TotalMap Bool :=
  "bar" !-> true ; "foo" !-> true ; { !-> false }

/-!
This completes the definition of total maps. Note that we don't need to define a find
operation on this representation of maps because it is just function application!

When we use maps in later chapters, we'll need several fundamental facts about how they behave.

Even if you don't bother to work the following exercises, make sure you thoroughly understand
the statements of the lemmas!

(Some of the proofs require the functional extensionality axiom, which was discussed in
the Logic chapter.)

### Exercise: 1 star, standard, optional (t_apply_empty)

First, the empty map returns its default element for all keys:
-/

theorem t_apply_empty (A : Type) (x : String) (v : A) :
  ({ !-> v } : TotalMap A) x = v := rfl

/-!
### Exercise: 2 stars, standard, optional (t_update_eq)

Next, if we update a map `m` at a key `x` with a new value `v` and then look up `x` in
the map resulting from the update, we get back `v`:
-/

theorem t_update_eq (A : Type) (m : TotalMap A) (x : String) (v : A) :
  (x !-> v ; m) x = v := by simp [t_update]

/-!
### Exercise: 2 stars, standard, optional (t_update_neq)

On the other hand, if we update a map `m` at a key `x1` and then look up a different key
`x2` in the resulting map, we get the same result that `m` would have given:
-/

theorem t_update_neq (A : Type) (m : TotalMap A) (x1 x2 : String) (v : A) :
  x1 ≠ x2 →
  (x1 !-> v ; m) x2 = m x2 := by sorry

/-!
### Exercise: 2 stars, standard, optional (t_update_shadow)

If we update a map `m` at a key `x` with a value `v1` and then update again with the same
key `x` and another value `v2`, the resulting map behaves the same (gives the same result
when applied to any key) as the simpler map obtained by performing just the second update on `m`:
-/

theorem t_update_shadow (A : Type) (m : TotalMap A) (x : String) (v1 v2 : A) :
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m) := by sorry

/-!
### Exercise: 2 stars, standard (t_update_same)

Given strings `x1` and `x2`, we can use the tactic `by_cases` on `x1 == x2` to simultaneously
perform case analysis on the result of `String.beq x1 x2` and generate hypotheses about the
equality (in the sense of `=`) of `x1` and `x2`. Use this approach to prove the following
theorem, which states that if we update a map to assign key `x` the same value as it already
has in `m`, then the result is equal to `m`:
-/

theorem t_update_same (A : Type) (m : TotalMap A) (x : String) :
  (x !-> m x ; m) = m := by sorry

/-!
### Exercise: 3 stars, standard, especially useful (t_update_permute)

Similarly, use `by_cases` to prove one final property of the update function: If we update
a map `m` at two distinct keys, it doesn't matter in which order we do the updates.
-/

theorem t_update_permute (A : Type) (m : TotalMap A) (v1 v2 : A) (x1 x2 : String) :
  x2 ≠ x1 →
  (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m) := by sorry

/-!
## Partial Maps

Lastly, we define partial maps on top of total maps. A partial map with elements of type `A`
is simply a total map with elements of type `Option A` and default element `none`.
-/

def PartialMap (A : Type) := TotalMap (Option A)

def empty {A : Type} : PartialMap A :=
  { !-> none }

def update {A : Type} (m : PartialMap A) (x : String) (v : A) : PartialMap A :=
  x !-> some v ; m

/-!
We introduce a similar notation for partial maps:
-/

notation x " ⊢> " v " ; " m => update m x v

/-!
We can also hide the last case when it is empty.
-/

notation x " ⊢> " v => update empty x v

def examplepmap : PartialMap Bool :=
  "Church" ⊢> true ; "Turing" ⊢> false ; empty

/-!
We now straightforwardly lift all of the basic lemmas about total maps to partial maps.
-/

theorem apply_empty (A : Type) (x : String) :
  (empty : PartialMap A) x = none := rfl

theorem update_eq (A : Type) (m : PartialMap A) (x : String) (v : A) :
  (x ⊢> v ; m) x = some v := by
  simp [update]
  apply t_update_eq

/-!
The `update_eq` lemma is used very often in proofs. We can add it as a simp lemma.
-/

-- attribute [simp] update_eq

theorem update_neq (A : Type) (m : PartialMap A) (x1 x2 : String) (v : A) :
  x2 ≠ x1 →
  (x2 ⊢> v ; m) x1 = m x1 := by sorry

theorem update_shadow (A : Type) (m : PartialMap A) (x : String) (v1 v2 : A) :
  (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m) := by sorry

theorem update_same (A : Type) (m : PartialMap A) (x : String) (v : A) :
  m x = some v →
  (x ⊢> v ; m) = m := by sorry

theorem update_permute (A : Type) (m : PartialMap A) (x1 x2 : String) (v1 v2 : A) :
  x2 ≠ x1 →
  (x1 ⊢> v1 ; x2 ⊢> v2 ; m) = (x2 ⊢> v2 ; x1 ⊢> v1 ; m) := by sorry

/-!
One last thing: For partial maps, it's convenient to introduce a notion of map inclusion,
stating that all the entries in one map are also present in another:
-/

def includedin {A : Type} (m m' : PartialMap A) : Prop :=
  ∀ x v, m x = some v → m' x = some v

/-!
We can then show that map update preserves map inclusion -- that is:
-/

theorem includedin_update (A : Type) (m m' : PartialMap A) (x : String) (vx : A) :
  includedin m m' →
  includedin (x ⊢> vx ; m) (x ⊢> vx ; m') := by sorry

/-!
This property is quite useful for reasoning about languages with variable binding -- e.g.,
the Simply Typed Lambda Calculus, which we will see in Programming Language Foundations,
where maps are used to keep track of which program variables are defined in a given scope.

## Additional Useful Lemmas

Let's prove a few more useful properties of maps that will come in handy later.
-/

/-!
### Exercise: 2 stars, standard (includedin_refl)

Map inclusion is reflexive:
-/

theorem includedin_refl (A : Type) (m : PartialMap A) :
  includedin m m := by
  intro x v h
  exact h

/-!
### Exercise: 3 stars, standard (includedin_trans)

Map inclusion is transitive:
-/

theorem includedin_trans (A : Type) (m1 m2 m3 : PartialMap A) :
  includedin m1 m2 → includedin m2 m3 → includedin m1 m3 := by
  intro h12 h23
  intro x v h1
  apply h23
  apply h12
  exact h1

/-!
### Exercise: 2 stars, standard (includedin_empty)

The empty map is included in every map:
-/

theorem includedin_empty (A : Type) (m : PartialMap A) :
  includedin empty m := by sorry

/-!
### Exercise: 3 stars, standard (includedin_update_same)

If we update a map with a binding that's already present, inclusion is preserved:
-/

theorem includedin_update_same (A : Type) (m m' : PartialMap A) (x : String) (v : A) :
  includedin m m' →
  m' x = some v →
  includedin (x ⊢> v ; m) m' := by sorry

/-!
## Examples and Tests

Let's test our definitions with some examples:
-/

example : examplemap "foo" = true := by
  simp [examplemap, t_update]

example : examplemap "bar" = true := by
  simp [examplemap, t_update]

example : examplemap "baz" = false := by
  simp [examplemap, t_update, t_empty]

example : examplepmap "Church" = some true := by
  simp [examplepmap, update, t_update]

example : examplepmap "Turing" = some false := by
  simp [examplepmap, update, t_update]

example : examplepmap "Godel" = none := by
  simp [examplepmap, update, t_update, empty, t_empty]

/-!
## Summary

In this chapter, we've seen how to:

1. **Define total maps** as functions from strings to values, with a default value for missing keys
2. **Define partial maps** as total maps returning `Option` types
3. **Use higher-order functions** to implement map operations like update
4. **Prove fundamental properties** of maps using functional extensionality
5. **Work with map inclusion** as a useful relation between partial maps

The functional representation of maps offers several advantages:
- **Extensionality**: Maps that behave the same are definitionally equal
- **Simplicity**: No need for separate lookup operations - just function application
- **Compositionality**: Easy to build complex maps from simple operations

These maps will be essential tools in later chapters when we formalize programming languages
and their semantics.

## Exercises for the Reader

The following theorems are left as exercises. Try to prove them using the techniques
demonstrated in this chapter:

1. `t_update_neq`: Updating a map at one key doesn't affect lookups at different keys
2. `t_update_shadow`: Double updates with the same key shadow the first update
3. `t_update_same`: Updating with the same value is the identity
4. `t_update_permute`: Order of updates at different keys doesn't matter
5. `update_neq`, `update_shadow`, `update_same`, `update_permute`: Partial map versions
6. `includedin_update`: Map inclusion is preserved by consistent updates
7. `includedin_empty`: The empty map is included in all maps
8. `includedin_update_same`: Updating with existing bindings preserves inclusion

These exercises will help you understand the fundamental properties of functional maps
and prepare you for more advanced topics in programming language theory.
-/
