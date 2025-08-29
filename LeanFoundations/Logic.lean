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
import LeanFoundations.Logic.PropLogic
import LeanFoundations.Logic.IndProp
import LeanFoundations.Logic.Maps
import LeanFoundations.Logic.ProofObjects
import LeanFoundations.Logic.IndPrinciples
import LeanFoundations.Logic.Typeclass
import LeanFoundations.Logic.Rel
import LeanFoundations.Logic.Imp
import LeanFoundations.Logic.ImpParser
import LeanFoundations.Logic.ImpCEvalFun


/-TOC-/
/-!
# Contents
- `LeanFoundations.Logic.Basic`: Functional programming in Lean
- `LeanFoundations.Logic.Induction`: Proof by induction
- `LeanFoundations.Logic.Lists`: Structured data
- `LeanFoundations.Logic.Polymorphism`: Polymorphism
- `LeanFoundations.Logic.Tactics`: More basic tactics
- `LeanFoundations.Logic.PropLogic`: Propositional Logic
- `LeanFoundations.Logic.IndProp`: Inductively defined propositions
- `LeanFoundations.Logic.Maps`: Total and partial maps
- `LeanFoundations.Logic.ProofObjects`: The Curry-Howard correspondence
- `LeanFoundations.Logic.IndPrinciples`: Induction principles
- `LeanFoundations.Logic.Typeclass`: Syntactic sugar to describe common behavior
- `LeanFoundations.Logic.Rel`: Relations and their properties
- `LeanFoundations.Logic.Imp`: Simple imperative programs
- `LeanFoundations.Logic.ImpParser`: Lexing and parsing in Lean
- `LeanFoundations.Logic.ImpCEvalFun`: Evaluation function for Imp
- Make a small DSL for arithmetic and compile it to a stack calculator
- Monad and IO and generate some json representing the stack calculator
- Meta-programming: notation, syntax, macro, elaborations.
- Make our own tactics
-/
