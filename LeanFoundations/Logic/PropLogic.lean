/-
Copyright (c) 2026 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/

/-!
# Propositional Logic
Now, let's see how to study logic within _the logic of Lean_.
-/

namespace PropLogic

inductive Proposition : Type where
  | var (name: String): Proposition
  | top : Proposition
  | and (p q : Proposition) : Proposition
  | imp (p q : Proposition) : Proposition
  | bot : Proposition
  | or (p q : Proposition) : Proposition


def Proposition.not (p : Proposition) : Proposition := p.imp .bot


abbrev Context := List Proposition
abbrev Context.add (p : Proposition) (Γ : Context) : Context := p :: Γ


/-!
Classical provability relation.
-/
inductive Context.provesC: Context -> Proposition -> Prop where
  | ax {Γ: Context} {p} : p ∈ Γ -> Γ.provesC p
  | impI {Γ: Context} {p q} : (Γ.add p).provesC q -> Γ.provesC (Proposition.imp p q)
  | andI {Γ: Context} {p q} : Γ.provesC p -> Γ.provesC q -> Γ.provesC (Proposition.and p q)
  | andE1 {Γ: Context} {p q} : Γ.provesC (Proposition.and p q) -> Γ.provesC p
  | andE2 {Γ: Context} {p q} : Γ.provesC (Proposition.and p q) -> Γ.provesC q
  | orI1 {Γ: Context} {p q} : Γ.provesC p -> Γ.provesC (Proposition.or p q)
  | orI2 {Γ: Context} {p q} : Γ.provesC q -> Γ.provesC (Proposition.or p q)
  | orE {Γ: Context} {p q r} : Γ.provesC (Proposition.or p q) -> (Γ.add p).provesC r -> (Γ.add q).provesC r -> Γ.provesC r
  | botE {Γ: Context} {p} : Γ.provesC Proposition.bot -> Γ.provesC p
  | em {Γ: Context} {p} : Γ.provesC (Proposition.or p p.not)

end PropLogic
