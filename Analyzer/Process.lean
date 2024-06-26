/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Types
import Analyzer.Plugin
import Analyzer.Output

open Lean Elab Meta
open Parser hiding mkIdent ident
open Command Term Frontend

namespace Analyzer

inductive PluginOption where
  | ignore : PluginOption
  | json : System.FilePath → PluginOption

def PluginOption.isPresent : PluginOption → Bool
  | .ignore => false
  | _ => true

def PluginOption.output {α : Type _} [ToJson α] (a : α) : PluginOption → IO Unit
  | .ignore => return ()
  | .json path =>
    IO.FS.withFile path .write fun h => h.putStrLn <| toJson a |>.compress

elab "define_options_structure%" structName:ident : command => do
  let fieldDecls ← Process.plugins.mapM fun (name, _) => do
    return (← `(structExplicitBinder| ($(mkIdent name) : PluginOption)))
  let body ← `(structFields| $fieldDecls*)
  let cmd ← `(structure $structName where $body:structFields)
  elabCommand cmd

define_options_structure% Options

elab "impl_onLoad" : term => do
  let param ← mkFreshBinderName
  let body ← Process.plugins.foldlM (init := #[]) fun a (name, plugin) => do
    if let some p := plugin.onLoad then do
      let cond := mkIdent (param ++ name ++ (Name.mkSimple "isPresent"))
      return a.push (← `(doSeqItem| if $cond then $(mkIdent p):term))
    else
      return a
  let term ← `(fun $(mkIdent param) => do $body*)
  let type ← `(Options → CommandElabM Unit)
  elabTerm term (← elabTerm type none)

def hasHead (expr : Expr) (name : Name) : MetaM Bool :=
  withNewMCtxDepth do
    let mvar ← mkFreshExprMVar (Expr.sort 1)
    isDefEq expr (← mkAppM name #[mvar])

elab "impl_process" : term => do
  let param ← mkFreshBinderName
  let body ← Process.plugins.mapM fun (name, plugin) => do
    let cond := mkIdent (param ++ name ++ (Name.mkSimple "isPresent"))
    let action := mkIdent (param ++ name ++ (Name.mkSimple "output"))
    let getResult := plugin.getResult
    let type := (← getEnv).find? getResult |>.get!.type
    let term ← if ← hasHead type ``CommandElabM then
      `(runCommandElabM $(mkIdent getResult))
    else if ← hasHead type ``FrontendM then
      `($(mkIdent getResult))
    else
      throwError "getResult must be either CommandElabM or FrontendM"
    return (← `(doSeqItem| if $cond then
      $action:term (← $term)
    ))
  let term ← `(fun $(mkIdent param) => do $body*)
  let type ← `(Options → FrontendM Unit)
  elabTerm term (← elabTerm type none)

def run (options : Options) : FrontendM Unit := do
  runCommandElabM <| impl_onLoad options
  processCommands
  impl_process options

end Analyzer
