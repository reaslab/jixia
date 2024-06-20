/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Types

open Lean Elab Meta

namespace Analyzer.Goal

-- see Meta.ppGoal
def fromMVar (goal : MVarId) : MetaM Goal :=
  goal.withContext do
    let lctx ← getLCtx
    let lctx : LocalContext := lctx.sanitizeNames.run' { options := ← getOptions }
    let mut context := Array.mkEmpty lctx.size
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      let var ← match ldecl with
      | .cdecl _ _ name type .. => do
        let type ← instantiateMVars type
        let type ← ppExpr type
        pure { name := name.simpMacroScopes.toString, type := type.pretty, value? := .none }
      | .ldecl _ _ name type value .. => do
        let type ← instantiateMVars type
        let type ← ppExpr type
        let value ← ppExpr value
        pure { name := name.simpMacroScopes.toString, type := type.pretty, value? := value.pretty }
      context := context.push var
    let type := (← ppExpr (← goal.getType)).pretty
    let tag ← goal.getTag
    return { tag, context, type }

def fromInfoBefore (ci : ContextInfo) (ti : TacticInfo) : IO (Array Goal) :=
  { ci with mctx := ti.mctxBefore }.runMetaM {} <| ti.goalsBefore.toArray.mapM Goal.fromMVar

def fromInfoAfter (ci : ContextInfo) (ti : TacticInfo) : IO (Array Goal) :=
  { ci with mctx := ti.mctxAfter }.runMetaM {} <| ti.goalsAfter.toArray.mapM Goal.fromMVar

def fromInfoBeforeOrAfter (useAfter : Bool) : ContextInfo → TacticInfo → IO (Array Goal) :=
  if useAfter then fromInfoAfter else fromInfoBefore

end Analyzer.Goal
