/-
The reading of private .olean parts follows LeanChecker.lean.
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license.
Authors of LeanChecker: Kim Morrison, Sebastian Ullrich.
-/
import Lean.CoreM
import Lean.Replay

open Lean

private def sameTheoremSignature (first second : ConstantInfo) : Bool :=
  match first, second with
  | .thmInfo old, .thmInfo new =>
      old.name == new.name && old.type == new.type &&
        old.levelParams == new.levelParams && old.all == new.all
  | _, _ => false

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  if args.isEmpty then throw <| IO.userError "No project modules supplied"
  let wanted : NameSet := args.foldl (fun names arg => names.insert arg.toName) {}
  let mut imports : Array Import := #[]
  let mut importsSeen : NameSet := {}
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  for arg in args do
    let path ← findOLean arg.toName
    let mut paths := #[path]
    for level in [OLeanLevel.server, OLeanLevel.private] do
      let part := level.adjustFileName path
      if ← part.pathExists then paths := paths.push part
    let parts ← readModuleDataParts paths
    let some (publicPart, _) := parts[0]? | throw <| IO.userError s!"No data for {arg}"
    let some (fullPart, _) := parts.back? | throw <| IO.userError s!"No declarations for {arg}"
    for dep in publicPart.imports do
      if !wanted.contains dep.module && !importsSeen.contains dep.module then
        importsSeen := importsSeen.insert dep.module
        imports := imports.push { module := dep.module, importAll := true }
    for name in fullPart.constNames, info in fullPart.constants do
      if let some previous := declarations[name]? then
        -- The kernel's replay also coalesces generated theorems of identical signature.
        if sameTheoremSignature previous info then continue
        throw <| IO.userError s!"Conflicting project declaration: {name}"
      if info.isAxiom then
        throw <| IO.userError s!"Project declaration is an axiom: {name}"
      declarations := declarations.insert name info
    IO.println s!"collected {arg}: {fullPart.constNames.size} declarations"
  IO.println s!"loading {imports.size} external imports"
  let (_, state) ← (importModulesCore imports).run
  let env ← finalizeImport state imports {} 0 false false (isModule := true)
  for (name, info) in declarations.toList do
    if let some previous := env.toKernelEnv.find? name then
      unless sameTheoremSignature previous info do
        throw <| IO.userError s!"Conflicting declaration from the external environment: {name}"
  IO.println s!"replaying {declarations.size} declarations"
  let checked ← env.toKernelEnv.replay declarations
  let endpoint := `KqR75.PhysicalCompletion.eventually_designFibre_bilateral
  unless (checked.find? endpoint).isSome do
    throw <| IO.userError s!"Missing replayed theorem: {endpoint}"
  IO.println s!"PASS_KERNEL modules={args.length} declarations={declarations.size} endpoint={endpoint}"
