/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Types

open Lean Elab Meta Tactic

namespace Lean.Elab.Tactic.TacticM

def runWithInfoBefore {α : Type} (ci : ContextInfo) (ti : TacticInfo) (x : TacticM α) : IO α :=
  { ci with mctx := ti.mctxBefore }.runMetaM {} <|
    x { elaborator := .anonymous, recover := false } |>.run' { goals := ti.goalsBefore }
    |>.run'

def runWithInfoAfter {α : Type} (ci : ContextInfo) (ti : TacticInfo) (x : TacticM α) : IO α :=
  { ci with mctx := ti.mctxAfter }.runMetaM {} <|
    x { elaborator := .anonymous, recover := false } |>.run' { goals := ti.goalsAfter }
    |>.run'

def runWithInfo {α : Type} (useAfter : Bool) : ContextInfo → TacticInfo → TacticM α → IO α :=
  if useAfter then runWithInfoAfter else runWithInfoBefore

end Lean.Elab.Tactic.TacticM


namespace Analyzer.Goal

def getUsedVariables (e : Expr) : MetaM (Array Name) :=
  e.collectFVars.run default <&> fun s => s.2.fvarIds |>.map FVarId.name

-- see Meta.ppGoal
def fromMVar (finalCtx : MetavarContext) (goal : MVarId) : MetaM Goal :=
  withEnableInfoTree false <| goal.withContext do
    let lctx ← getLCtx
    let lctx : LocalContext := lctx.sanitizeNames.run' { options := ← getOptions }
    let mut context := Array.mkEmpty lctx.size
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      let var ← match ldecl with
      | .cdecl _ id name type .. => do
        let type ← instantiateMVars type
        let type ← ppExpr type
        pure {
          id := id.name,
          name := name.simpMacroScopes,
          type := type.pretty,
          value? := none
        }
      | .ldecl _ id name type value .. => do
        let type ← instantiateMVars type
        let type ← ppExpr type
        let value ← ppExpr value
        pure {
          id := id.name,
          name := name.simpMacroScopes,
          type := type.pretty,
          value? := value.pretty
        }
      context := context.push var
    let type := (← ppExpr (← goal.getType)).pretty
    let tag ← goal.getTag
    let (typeUses, valueUses) ← withMCtx finalCtx do
      pure (← getUsedVariables <| .mvar goal, ← getUsedVariables (← goal.getType))
    return {
      tag,
      context,
      type,
      typeUses,
      valueUses,
    }

def fromTactic (finalCtx : MetavarContext) : TacticM (Array Goal) := do
  (← getUnsolvedGoals).toArray.mapM fun mvar => Goal.fromMVar finalCtx mvar

end Analyzer.Goal
