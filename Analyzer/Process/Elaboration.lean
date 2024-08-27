/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda, Kokic
-/
import Lean
import Analyzer.Process.Tactic.Simp

open Lean Elab Meta Command

namespace Analyzer.Process.Elaboration
open Analyzer.Process.Tactic

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
    args.map references |>.foldl (init := .empty) fun s t => s.fold (fun s a => s.insert a) t
  | .atom _ _ => .empty
  | .ident _ _ name _ => .empty |>.insert name

def getUsedVariables (e : Expr) : MetaM (Array Name) :=
  e.collectFVars.run default <&> fun s => s.2.fvarIds |>.map FVarId.name

def onLoad : CommandElabM Unit :=
  enableInfoTree

def getResult : CommandElabM (Array TacticElabInfo) := do
  let trees ← getInfoTrees
  trees.toArray.concatMapM fun tree => do
    let info := tree.foldInfo (init := #[]) collectTacticInfo
    if let some (ci, _) := info[0]? then
      let mctx := ci.mctx
      let getUsedInfo (mvar : MVarId) : MetaM (Option Json) := do
        let typeUses ← getUsedVariables (← mvar.getType)
        let valueUses ← withMCtx mctx <| getUsedVariables <| .mvar mvar
        return json%{
          typeUses: $(typeUses),
          valueUses: $(valueUses)
        }

      info.mapM fun (ci, ti) => do
        let mut extra : Json := .null
        extra := extra.mergeObj (← Simp.getUsedTheorems ci ti)

        pure {
          tactic := ti.stx,
          references := references ti.stx,
          before := ← Goal.fromTactic (extraFun := getUsedInfo) |>.runWithInfoBefore ci ti,
          after := ← Goal.fromTactic (extraFun := getUsedInfo) |>.runWithInfoAfter ci ti,
          extra? := if extra.isNull then none else extra,
        : TacticElabInfo}
    else
      pure #[]

end Analyzer.Process.Elaboration
