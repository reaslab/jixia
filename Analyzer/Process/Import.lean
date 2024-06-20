/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Basic

open Lean Elab Command

namespace Analyzer.Process.Import

def getResult : CommandElabM (Array Name) := do
  let env ← getEnv
  return env.header.imports.map Import.module

initialize registerPlugin `import ``getResult

end Analyzer.Process.Import
