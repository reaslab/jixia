/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda, Kokic
-/
import Lean
import Analyzer.Types
import Analyzer.Goal

open Lean Elab Meta Command

namespace Analyzer.Process.Tactic

@[reducible]
def String.Range.lt (r : String.Range) (r' : String.Range) : Prop :=
  Prod.lexLt (r.start, r.stop) (r'.start, r'.stop)

def collectTacticInfo (ctx : ContextInfo) (info : Info) (a : Array (ContextInfo × TacticInfo)) : Array (ContextInfo × TacticInfo) :=
  match info with
  | .ofTacticInfo ti => a.push (ctx, ti)
  | _ => a

partial def references : Syntax → HashSet Name
  | .missing => .empty
  | .node _ _ args =>
    args.map references |>.foldl (init := .empty) fun s t =>
      HashSet.fold (fun s a => HashSet.insert s a) s t
  | .atom _ _ => .empty
  | .ident _ _ name _ => .empty |>.insert name

def onLoad : CommandElabM Unit :=
  enableInfoTree

open Elab.Tactic

namespace Simp

def getSimpStats (stx : Syntax) : TacticM Simp.Stats := withMainContext do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
  dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])

def getSimpAllStats (stx : Syntax) : TacticM Simp.Stats := withMainContext do
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (_, stats) ← simpAll (← getMainGoal) ctx (simprocs := simprocs)
  return stats

def getDSimpStats (stx : Syntax) : TacticM Simp.Stats := withMainContext do
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  let (_, stats) ← dsimpGoal (← getMainGoal) ctx (simprocs := simprocs)
  return stats

def getStats (stx : Syntax) : TacticM Simp.Stats :=
  match stx.getKind with
  | ``Parser.Tactic.simpAll => getSimpAllStats stx
  | ``Parser.Tactic.dsimp => getDSimpStats stx
  | _ => getSimpStats stx

def getUsedTheorems (ci : ContextInfo) (ti : TacticInfo) : CommandElabM Json := do
    if ti.stx.isOfKind |> List.any [
      ``Parser.Tactic.simp,
      ``Parser.Tactic.simpAll,
      ``Parser.Tactic.dsimp,
    ] then
      let simpStats ← { ci with mctx := ti.mctxBefore }.runMetaM {} <|
        getStats ti.stx
        { elaborator := .anonymous } |>.run' { goals := ti.goalsBefore }
        |>.run'
      let usedTheorems := simpStats.usedTheorems.foldl (init := #[]) fun a k _ => a.push k.key
      return json% {
        usedTheorems: $(usedTheorems)
      }
    else
      return .null

end Simp

def getResult : CommandElabM (Array TacticRunInfo) := do
  let info := (← getInfoTrees).foldl (init := #[]) fun info tree => tree.foldInfo collectTacticInfo info
  info.mapM fun (ci, ti) => do
    let mut extra : Json := .null
    extra := extra.mergeObj (← Simp.getUsedTheorems ci ti)

    return {
      tactic := ti.stx,
      references := references ti.stx,
      before := ← Goal.fromInfoBefore ci ti,
      after := ← Goal.fromInfoAfter ci ti,
      extra? := if extra.isNull then none else extra,
    }

end Analyzer.Process.Tactic
