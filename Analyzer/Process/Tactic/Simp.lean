import Lean
import Analyzer.Goal

open Lean Elab Meta Command Tactic

namespace Analyzer.Process.Tactic.Simp

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

def _root_.Lean.Meta.Origin.getName {m : Type → Type} [Monad m] [MonadLCtx m] : Origin → m Name
  | .decl declName _ _ => pure declName
  | .fvar fvarId => do return (← getLCtx).get! fvarId |>.userName
  | .stx id _ => pure id
  | .other name => pure name

def getUsedTheorems (ci : ContextInfo) (ti : TacticInfo) : CommandElabM Json := do
    if ti.stx.isOfKind |> List.any [
      ``Parser.Tactic.simp,
      ``Parser.Tactic.simpAll,
      ``Parser.Tactic.dsimp,
    ] then
      let usedTheorems ← TacticM.runWithInfoBefore ci ti <| withMainContext do
        let simpStats ← getStats ti.stx
        simpStats.usedTheorems.foldlM (init := #[]) fun a k _ => do return a.push (← k.getName)
      return json% {
        usedTheorems: $(usedTheorems)
      }
    else
      return .null

end Analyzer.Process.Tactic.Simp
