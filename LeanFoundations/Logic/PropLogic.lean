/-
Copyright (c) 2026 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/

/-!
# Propositional Logic
Now, let's see how to study logic in with _the logic of Lean_.
-/

namespace PropLogic

inductive Proposition : Type where
  | var (name: String): Proposition
  | top : Proposition
  | and (p q : Proposition) : Proposition
  | imp (p q : Proposition) : Proposition
  | bot : Proposition
  | or (p q : Proposition) : Proposition


abbrev Context := List Proposition


inductive Context.provesC: Context -> Proposition -> Prop where
  | ax {Γ: Context} {p} : p ∈ Γ -> Γ.provesC p

end PropLogic
