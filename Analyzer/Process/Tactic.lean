/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
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

def getSimpStats := fun stx => withMainContext do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  return stats

def getSimpAllStats := fun stx => withMainContext do
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let (_, stats) ← simpAll (← getMainGoal) ctx (simprocs := simprocs)
  return stats

def ofSimpStats (stx : Syntax) : TacticM Simp.Stats :=
  match stx.getKind with
    | ``Parser.Tactic.simpAll => getSimpAllStats stx
    | _ => getSimpStats stx

def runCore (x : TacticM Simp.Stats)
            (ctx : Tactic.Context)
            (s : Tactic.State) : TermElabM (Simp.Stats × Tactic.State) :=
  x ctx |>.run s

def runCore' (x : TacticM Simp.Stats)
             (ctx : Tactic.Context)
             (s : Tactic.State) : TermElabM Simp.Stats := do
  Prod.fst <$> runCore x ctx s

def getResult : CommandElabM (Array TacticRunInfo) := do
  let info := (← getInfoTrees).foldl (init := #[]) fun info tree => tree.foldInfo collectTacticInfo info
  info.mapM fun (ci, ti) => do

    let mut extra : Option Json := none

    if ti.stx.isOfKind |> List.any [
      ``Parser.Tactic.simp,
      ``Parser.Tactic.simpAll,
    ] then
      let tacticM := ofSimpStats ti.stx
      let termElabM := runCore' tacticM { elaborator := .anonymous } { goals := ti.goalsBefore }
      let metaM := Term.TermElabM.run' termElabM
      let simpStats ← { ci with mctx := ti.mctxBefore }.runMetaM {} metaM
      let usedTheorems := simpStats.usedTheorems.foldl (init := #[]) fun ps k _ => ps.push k.key
      extra := json% { usedTheorems: $(usedTheorems) }

    return {
      tactic := ti.stx,
      references := references ti.stx,
      before := ← Goal.fromInfoBefore ci ti,
      after := ← Goal.fromInfoAfter ci ti,
      extra? := extra
    }

end Analyzer.Process.Tactic
