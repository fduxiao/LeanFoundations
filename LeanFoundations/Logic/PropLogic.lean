/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/

/-!
# Propositional Logic and More Tactics
We have already learned basic functional programming and simple propositions, and
have seen some tactics to prove those propositions. We are going to understand the
principles behind those tactics. To begin with, we mainly study logical connectives
now, i.e., propositional logic. We will use those functional programming concepts we
have learned to model those connectives.

> We was working on the `scratch` namespace in order to understand how Lean works.
> Now, we switch to the normal `Bool`, `Nat`, `List` predefined by Lean and those
> proved properties about them. Note that we also have some syntactic sugar about
> them. For example, you can write `1 * (2 + 3)` or `true || false`. You can also
> use the **ite** syntax (if-then-else) `if true then 1 else 2`.
-/


/-!
## Well-formed Formula
-/

abbrev PropVar := Nat


inductive Formula where
  | Top | Bot
  | Var: PropVar -> Formula
  | And: Formula -> Formula -> Formula
  | Or: Formula -> Formula -> Formula
  | Imp: Formula -> Formula -> Formula


def Formula.Not: Formula -> Formula := fun f => f.Imp .Bot

/-!
## Boolean Semantics
-/

abbrev Evaluation := PropVar -> Bool

def Evaluation.eval (v: Evaluation): Formula -> Bool
  | .Top => true
  | .Bot => false
  | .Var x => v x
  | .And a b => (v.eval a) && (v.eval b)
  | .Or a b => (v.eval a) || (v.eval b)
  | .Imp a b => (v.eval a).not || (v.eval b)

/-!
## Proof Tree
-/

abbrev Context := List Formula


inductive Proof: Context -> Formula -> Prop where
  | Truth {Γ: Context}: Proof Γ .Top
  | EFQ {Γ: Context} {φ: Formula}: Proof Γ .Bot -> Proof Γ φ
  | Axiom {Γ: Context} {φ: Formula}: Proof (φ :: Γ) φ
  | Weaken {Γ: Context} {α φ: Formula}: Proof Γ φ -> Proof (α :: Γ) φ
  | Conj {Γ: Context} {φ ψ}: Proof Γ φ -> Proof Γ ψ -> Proof Γ (φ.And ψ)
  | Pr1 {Γ: Context} {φ ψ: Formula}: Proof Γ (φ.And ψ) -> Proof Γ φ
  | Pr2 {Γ: Context} {φ ψ: Formula}: Proof Γ (φ.And ψ) -> Proof Γ ψ
  | In1 {Γ: Context} {φ ψ: Formula}: Proof Γ φ -> Proof Γ (φ.Or ψ)
  | In2 {Γ: Context} {φ ψ: Formula}: Proof Γ ψ -> Proof Γ (φ.Or ψ)
  | Case {Γ: Context} {φ ψ τ: Formula}:
    Proof Γ (φ.Or ψ) -> Proof (φ :: Γ) τ -> Proof (ψ :: Γ) τ -> Proof Γ τ
  | Abs {Γ: Context} {φ ψ: Formula}: Proof (φ :: Γ) ψ -> Proof Γ (φ.Imp ψ)
  | MP {Γ: Context} {φ ψ: Formula}: Proof Γ (φ.Imp ψ) -> Proof Γ φ -> Proof Γ ψ


/-!
## Reflection in Lean
-/
