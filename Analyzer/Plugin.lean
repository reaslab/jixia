/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Process.Import
import Analyzer.Process.Declaration
import Analyzer.Process.Symbol
import Analyzer.Process.Tactic
import Analyzer.Process.Line
import Analyzer.Process.AST

open Lean

namespace Analyzer.Process

structure Plugin where
  getResult : Name
  onLoad : Option Name

protected def plugins : Array (Name × Plugin) := #[
  (`import, ⟨ ``Import.getResult, none ⟩),
  (`declaration, ⟨ ``Declaration.getResult, ``Declaration.onLoad ⟩),
  (`symbol, ⟨ ``Symbol.getResult, none ⟩),
  (`tactic, ⟨ ``Tactic.getResult, ``Tactic.onLoad ⟩),
  (`line, ⟨ ``Line.getResult, ``Line.onLoad ⟩),
  (`ast, ⟨ ``AST.getResult, none ⟩ )
]

end Analyzer.Process
