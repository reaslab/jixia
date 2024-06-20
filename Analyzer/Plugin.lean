/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

open Lean

namespace Analyzer

structure Plugin where
  getResult : Name
  onLoad : Option Name

initialize pluginRef : IO.Ref (NameMap Plugin) ← IO.mkRef .empty
def registerPlugin (name : Name) (getResult : Name) (onLoad : Option Name := .none) : IO Unit :=
  pluginRef.modify fun a => a.insert name { getResult, onLoad }
