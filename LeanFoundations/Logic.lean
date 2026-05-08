/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/

import LeanFoundations.Logic.Basic
import LeanFoundations.Logic.Induction
import LeanFoundations.Logic.Lists
import LeanFoundations.Logic.Polymorphism
import LeanFoundations.Logic.Tactics
import LeanFoundations.Logic.IndProp
import LeanFoundations.Logic.FinMap
import LeanFoundations.Logic.PropLogic
import LeanFoundations.Logic.ProofObjects
import LeanFoundations.Logic.IndPrinciples
import LeanFoundations.Logic.Typeclass
import LeanFoundations.Logic.Rel


/-TOC-/
/-!
# Contents
- `LeanFoundations.Logic.Basic`: Functional programming in Lean
- `LeanFoundations.Logic.Induction`: Proof by induction
- `LeanFoundations.Logic.Lists`: Structured data
- `LeanFoundations.Logic.Polymorphism`: Polymorphism
- `LeanFoundations.Logic.Tactics`: More basic tactics and logic connectives
- `LeanFoundations.Logic.IndProp`: Inductively defined propositions
- `LeanFoundations.Logic.FinMap`: Finite maps
- `LeanFoundations.Logic.PropLogic`: Propositional Logic
- `LeanFoundations.Logic.ProofObjects`: The Curry-Howard correspondence
- `LeanFoundations.Logic.IndPrinciples`: Induction principles
- `LeanFoundations.Logic.Typeclass`: Syntactic sugar to describe common behavior
- `LeanFoundations.Logic.Rel`: Relations and their properties
- Make a small DSL for arithmetic and compile it to a stack calculator
- Monad and IO and generate some json representing the stack calculator
- Meta-programming: notation, syntax, macro, elaborations.
- Make our own tactics
-/
