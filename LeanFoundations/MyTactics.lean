import Lean

namespace MyDSimp

open Lean.Parser.Tactic
/-
Copied from lean source. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/simp.20without.20rfl
-/
syntax (name := compute) "compute" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

open Lean Elab Tactic Meta Simp

def dsimpGoal' (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Stats := {}) : MetaM (Option MVarId × Stats) := do
   mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut stats : Stats := stats
    for fvarId in fvarIdsToSimp do
      let type ← instantiateMVars (← fvarId.getType)
      let (typeNew, stats') ← dsimp type ctx simprocs
      stats := stats'
      if typeNew.isFalse then
        mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
        return (none, stats)
      if typeNew != type then
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId typeNew
    if simplifyTarget then
      let target ← mvarIdNew.getType
      let (targetNew, stats') ← dsimp target ctx simprocs stats
      stats := stats'
      -- if targetNew.isTrue then
      --   mvarIdNew.assign (mkConst ``True.intro)
      --   return (none, stats)
      -- if let some (_, lhs, rhs) := targetNew.consumeMData.eq? then
      --   if (← withReducible <| isDefEq lhs rhs) then
      --     mvarIdNew.assign (← mkEqRefl lhs)
      --     return (none, stats)
      if target != targetNew then
        mvarIdNew ← mvarIdNew.replaceTargetDefEq targetNew
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "dsimp made no progress"
    return (some mvarIdNew, stats)

def dsimpLocation' (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (loc : Location) : TacticM Unit := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := withSimpDiagnostics do
    let mvarId ← getMainGoal
    let (result?, stats) ← dsimpGoal' mvarId ctx simprocs (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    if tactic.simp.trace.get (← getOptions) then
      mvarId.withContext <| traceSimpCall (← getRef) stats.usedTheorems
    return stats.diag

@[tactic compute] def evalDSimp' : Tactic := fun stx => do
  let { ctx, simprocs, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  dsimpLocation' ctx simprocs (expandOptLocation stx[5])

end MyDSimp


namespace Solution

macro "solution" "[" x:term "]": term => `($x)

elab "solution" "[" x:tacticSeq "]": tactic => do
  Lean.Elab.Tactic.evalTactic x.raw


def add5: Nat -> Nat := solution[
  λ x => x + 5
]

example : add5 3 = 8 := by
  solution[
    simp [add5]
  ]

end Solution
