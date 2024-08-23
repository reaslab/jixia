/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

/-!
Note on `Syntax` fields: by default, `Syntax` fields should be regarded as references to a part of source code.
Generated syntax nodes are serialized as `null`.

Note on source ranges: we encode all source positions/ranges by byte.
-/

open Lean Elab Term

namespace Analyzer

/-- Information about a declaration command in source file. -/
structure BaseDeclarationInfo where
  kind : String
  ref : Syntax
  /-- Syntax node corresponding to the name of this declaration. -/
  id : Syntax
  /-- The identifier contained in `id`, even if it is generated. -/
  name : Name
  fullname : Name
  modifiers : Modifiers
  params : Array BinderView
  type : Option Syntax
  value : Option Syntax
  /-- The tactic sequence when `value` consists of a single `by` node. -/
  tactics : Array Syntax

structure InductiveInfo extends BaseDeclarationInfo where
  constructors : Array BaseDeclarationInfo

inductive DeclarationInfo where
  | ofBase : BaseDeclarationInfo → DeclarationInfo
  | ofInductive : InductiveInfo → DeclarationInfo

def DeclarationInfo.toBaseDeclarationInfo : DeclarationInfo → BaseDeclarationInfo
  | .ofBase info => info
  | .ofInductive info => info.toBaseDeclarationInfo

structure SymbolInfo where
  kind : String
  name : Name
  type : String
  /-- Names of constants that the type of this symbol references.  Mathematically, this roughly means "notions
  needed to state the theorem". -/
  typeReferences : HashSet Name
  /-- In the same spirit as above, "notions used in the proof of the theorem". `null` if this symbol has no value. -/
  valueReferences : Option (HashSet Name)
  /-- Whether the type of this symbol is a proposition. -/
  isProp : Bool

structure Variable where
  id : Name
  name : Name
  type : String
  value? : Option String
  isProp : Bool

structure Goal where
  tag : Name
  context : Array Variable
  type : String
  isProp : Bool
  extra? : Option Json := none

structure TacticRunInfo where
  tactic : Syntax
  /-- Names referenced in this tactic, including constants and local hypotheses. -/
  references : HashSet Name
  before : Array Goal
  after : Array Goal
  extra? : Option Json := none

end Analyzer
