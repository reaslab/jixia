/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda, Kokic, Znssong
-/
import Lean
import Analyzer.Process.Tactic.Simp

open Lean Elab Meta Command Tactic TacticM

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

def _root_.Lean.Meta.getFVars (e : Expr) : Array FVarId :=
  (collectFVars {} e).fvarIds

def getDependentsFromGoal (goal : MVarId) : MetaM (Array MVarId × Array FVarId) := do
  let mut visited : HashSet MVarId := {}
  let mut mvars := #[goal]
  let mut dependentMVars := #[]
  let mut dependentFVars := #[]
  while !mvars.isEmpty do
    let mvarId := mvars.back
    mvars := mvars.pop
    if visited.contains mvarId then continue
    visited := visited.insert mvarId
    match ← getDelayedMVarAssignment? mvarId with
    | none => do
      match ← getExprMVarAssignment? mvarId with
      | none => dependentMVars := dependentMVars.push mvarId
      | some expr => mvars := mvars.append (← getMVars expr)
    | some {fvars, mvarIdPending} => do
      dependentFVars := dependentFVars.append <| fvars.map Expr.fvarId!
      println! s!"{goal.name} {dependentFVars.map FVarId.name}"
      mvars := mvars.push mvarIdPending
  return (dependentMVars, dependentFVars)

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
        let goalsBefore ← runWithInfoBefore ci ti getUnsolvedGoals
        let dependencies ← runWithInfoAfter ci ti do
          goalsBefore.foldlM
            fun array goal => do
              match ← getExprMVarAssignment? goal with
              | some _ =>
                let (mvars, fvars) ← getDependentsFromGoal goal
                return array.push {
                  mvarId := goal.name,
                  mvarDependencies := mvars.map MVarId.name,
                  fvarDependencies := fvars.map FVarId.name
                }
              | none => return array
            #[]
        let typeDependencies ← runWithInfoAfter ci ti do
          (← getUnsolvedGoals).foldlM
            fun array goal => do
              return array.push {
                mvarId := goal.name,
                mvarDependencies := (← getMVars (← goal.getType)) |>.map MVarId.name,
                fvarDependencies := (getFVars (← goal.getType)) |>.map FVarId.name
              }
            #[]
        pure {
          tactic := ti.stx,
          references := references ti.stx,
          before := ← Goal.fromTactic (extraFun := getUsedInfo) |>.runWithInfoBefore ci ti,
          after := ← Goal.fromTactic (extraFun := getUsedInfo) |>.runWithInfoAfter ci ti,
          dependencies := dependencies,
          typeDependencies := typeDependencies,
          extra? := if extra.isNull then none else extra,
        : TacticElabInfo}
    else
      pure #[]

end Analyzer.Process.Elaboration
