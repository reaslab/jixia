/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Basic
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

def getResult : CommandElabM (Array TacticRunInfo) := do
  let info := (← getInfoTrees).foldl (init := #[]) fun info tree => tree.foldInfo collectTacticInfo info
  info.mapM fun (ci, ti) => do
    return {
      tactic := ti.stx,
      references := references ti.stx,
      before := ← Goal.fromInfoBefore ci ti,
      after := ← Goal.fromInfoAfter ci ti,
    }

initialize registerPlugin `tactic ``getResult ``onLoad

end Analyzer.Process.Tactic
