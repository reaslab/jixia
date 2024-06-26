/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Types

open Lean Elab Frontend

namespace Analyzer.Process.AST

def getResult : FrontendM (Array Syntax) := do
  return (← get).commands

end Analyzer.Process.AST
