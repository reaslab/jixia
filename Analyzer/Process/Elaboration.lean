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

def getUsedFVarIds (e : Expr) : MetaM (Array FVarId) :=
  e.collectFVars.run default <&> fun s => s.2.fvarIds

def getUsedVariables (e : Expr) : MetaM (Array Name) := do
  return (← getUsedFVarIds e).map FVarId.name

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
      mvars := mvars.push mvarIdPending
  return (dependentMVars, dependentFVars)


def getUsedInfo (mvar : MVarId) : MetaM (Option Json) := do
  let typeUses ← getUsedVariables (← mvar.getType)
  let valueUses ← getUsedVariables <| .mvar mvar
  let typeMVars := (← getMVars (← mvar.getType)).map MVarId.name
  return json%{
    typeUses: $(typeUses),
    typeMVars: $(typeMVars),
    valueUses: $(valueUses)
  }

def getTacticInfo (ci : ContextInfo) (ti : TacticInfo) : IO TacticElabInfo := do
    let mut extra : Json := .null
    extra := extra.mergeObj (← Simp.getUsedTheorems ci ti)
    let goalsBefore ← runWithInfoBefore ci ti getUnsolvedGoals
    let dependencies ← runWithInfoAfter ci ti do
      goalsBefore.foldlM
        fun map goal => do
          match ← getExprMVarAssignment? goal with
          | some _ =>
            let (mvars, fvars) ← getDependentsFromGoal goal
            let json := json%{
              newGoals: $(mvars.map MVarId.name),
              newHypotheses: $(fvars.map FVarId.name)
            }
            return HashMap.insert map goal json
          | none => return map
        ({} : HashMap MVarId Json)

    let getUsedInfo' (mvar : MVarId) : MetaM (Option Json) := do
      let extra ← getUsedInfo mvar
      return do return .mergeObj (← extra) (← dependencies.find? mvar)

    pure {
      tactic := ti.stx,
      references := references ti.stx,
      before := ← Goal.fromTactic (extraFun := getUsedInfo') |>.runWithInfoBefore ci ti,
      after := ← Goal.fromTactic (extraFun := getUsedInfo) |>.runWithInfoAfter ci ti,
      extra? := if extra.isNull then none else extra,
    : TacticElabInfo}

def getTermInfo (ci : ContextInfo) (ti : TermInfo) : IO TermElabInfo :=
  ti.runMetaM ci do pure {
    term := ti.stx,
    context := ← Goal.printContext,
    type := (← ppExpr (← inferType ti.expr)).pretty
    expectedType := ← ti.expectedType?.mapM fun type => do pure (← ppExpr type).pretty
    value := (← ppExpr ti.expr).pretty
  }


def onLoad : CommandElabM Unit :=
  enableInfoTree

def getResult : CommandElabM (Array ElaborationInfo) := do
  let trees := (← getInfoTrees).toArray
  trees.filterMapM fun tree => do
    tree.visitM (postNode := fun ci info _ children => do
      let children' := children.filterMap id |>.toArray
      match info with
      | .ofTacticInfo ti => .tactic (children := children') <$> getTacticInfo ci ti
      | .ofTermInfo ti => .term (children := children') <$> getTermInfo ci ti
      | _ => pure <| .other children'
    )


end Analyzer.Process.Elaboration
