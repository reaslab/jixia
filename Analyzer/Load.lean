/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

open Lean Elab Parser System Frontend

namespace Analyzer

-- see Frontend.runFrontend
def loadFile (path : FilePath) : IO (Context × State) := do
  let input ← IO.FS.readFile path
  let inputCtx := mkInputContext input path.toString
  let (header, parserState, messages) ← parseHeader inputCtx
  initSearchPath (← findSysroot)
  let (env, messages) ← processHeader (leakEnv := true) header .empty messages inputCtx
  let commandState := Command.mkState env messages .empty
  return ({ inputCtx }, { commandState, parserState, cmdPos := parserState.pos, commands := #[] })

def withFile' {α : Type _} (path : FilePath) (m : FrontendM α) : IO α := do
  let (context, state) ← loadFile path
  m context |>.run' state

end Analyzer
