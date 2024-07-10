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

def runCore (x : TacticM Simp.Stats)
            (ctx : Tactic.Context)
            (s : Tactic.State) : TermElabM (Simp.Stats × Tactic.State) :=
  x ctx |>.run s

def runCore' (x : TacticM Simp.Stats)
             (ctx : Tactic.Context)
             (s : Tactic.State) : TermElabM Simp.Stats := do
  Prod.fst <$> runCore x ctx s

def getSimpStats : Syntax → TacticM Simp.Stats := fun stx => withMainContext do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  return stats

def getSimpAllStats : Syntax → TacticM Simp.Stats := fun stx => withMainContext do
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (_, stats) ← simpAll (← getMainGoal) ctx (simprocs := simprocs)
  return stats

def getDSimp : Syntax → TacticM Simp.Stats := fun stx => do
  let { ctx, simprocs, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  let (_, stats) ← dsimpGoal (← getMainGoal) ctx (simprocs := simprocs)
  return stats

def getUsedTheorems (ci : ContextInfo) (ti : TacticInfo) : CommandElabM (Option Json) := do
    if ti.stx.isOfKind |> List.any [
      ``Parser.Tactic.simp,
      ``Parser.Tactic.simpAll,
      ``Parser.Tactic.dsimp,
      -- ``Parser.Tactic.simpa,
    ] then
      let tacticM := match ti.stx.getKind with
        | ``Parser.Tactic.simpAll => getSimpAllStats ti.stx
        | ``Parser.Tactic.dsimp => getDSimp ti.stx
        | _ => getSimpStats ti.stx
      let termElabM := runCore' tacticM { elaborator := .anonymous } { goals := ti.goalsBefore }
      let metaM := Term.TermElabM.run' termElabM
      let simpStats ← { ci with mctx := ti.mctxBefore }.runMetaM {} metaM
      let usedTheorems := simpStats.usedTheorems.foldl (init := #[]) fun ps k _ => ps.push k.key
      return json% { usedTheorems: $(usedTheorems) }
    else
      return none

end Simp

def mergeOptionJson : Option Json → Option Json → Option Json
  | fst, none => fst
  | none, snd => snd
  | some data, some append => some (data.mergeObj append)

def getResult : CommandElabM (Array TacticRunInfo) := do
  let info := (← getInfoTrees).foldl (init := #[]) fun info tree => tree.foldInfo collectTacticInfo info
  info.mapM fun (ci, ti) => do

    let mut extra : Option Json := none
    extra := mergeOptionJson extra (← Simp.getUsedTheorems ci ti)

    return {
      tactic := ti.stx,
      references := references ti.stx,
      before := ← Goal.fromInfoBefore ci ti,
      after := ← Goal.fromInfoAfter ci ti,
      extra? := extra
    }

end Analyzer.Process.Tactic
