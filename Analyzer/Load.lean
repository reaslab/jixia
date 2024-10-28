/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Metalib.Load

open Lean Elab Parser System Frontend

namespace Analyzer

def loadFile (path : FilePath) : IO (Context × State) := do
  let input ← IO.FS.readFile path
  let inputCtx := mkInputContext input path.toString
  loadFrontend inputCtx

def withFile {α : Type _} (path : FilePath) (m : FrontendM α) : IO (α × State) := do
  let (context, state) ← loadFile path
  m context |>.run state

end Analyzer
