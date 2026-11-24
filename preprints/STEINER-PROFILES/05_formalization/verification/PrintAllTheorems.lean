import Reconstructed
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxHeartbeats 0
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 20000000
set_option maxRecDepth 20000

/-- Inventory the theorem records from the private parts of the exact
project-module objects. Definitions and dependency-only declarations are
outside the catalogue. Lean stores both `theorem` and `lemma` as thmInfo. -/
elab "#print_frozen_theorems" : command => do
  let modules ← IO.FS.readFile "MODULES.txt"
  let modules := modules.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let names : NameSet := modules.foldl (fun acc name => acc.insert name.toName) {}
  unless modules.length == names.size do
    throwError "duplicate modules in MODULES.txt"
  let env ← getEnv
  let statements ← IO.FS.Handle.mk "THEOREMS.txt" .write
  let index ← IO.FS.Handle.mk "THEOREMS.tsv" .write
  let proofSelection ← IO.getEnv "R75_PRINT_PROOFS"
  let proofs ← match proofSelection with
    | none => pure none
    | some _ => some <$> IO.FS.Handle.mk "PROOFS.txt" .write
  statements.putStrLn "R75 | Theorems and lemmas in the frozen project modules"
  index.putStrLn "module\tdeclaration\taxioms"
  let mut theoremCount := 0
  let mut distinct : NameSet := {}
  let mut proofCount := 0
  for moduleName in modules do
    let path ← findOLean moduleName.toName
    let mut paths := #[path]
    for level in [OLeanLevel.server, OLeanLevel.private] do
      let part := level.adjustFileName path
      if ← part.pathExists then paths := paths.push part
    let parts ← readModuleDataParts paths
    let some (data, _) := parts.back? | throwError "missing module data for {moduleName}"
    unless data.constNames.size == data.constants.size do
      throwError "inconsistent declaration arrays in {moduleName}"
    let mut moduleCount := 0
    for name in data.constNames, declaration in data.constants do
      if let .thmInfo info := declaration then
        unless (env.find? name).isSome do
          throwError "frozen declaration not visible from Reconstructed: {name}"
        let axioms := (← Lean.collectAxioms name).qsort Name.lt
        for axiomName in axioms do
          unless ["propext", "Classical.choice", "Quot.sound"].contains axiomName.toString do
            throwError "{name} uses an unexpected axiom: {axiomName}"
        let rendered ← liftTermElabM <| PrettyPrinter.ppSignature name
        let statement := rendered.fmt.pretty 108
        let axiomText := String.intercalate ", " (axioms.toList.map Name.toString)
        statements.putStrLn s!"\n[{moduleName}] {name}\n{statement}\nAxioms: [{axiomText}]"
        index.putStrLn s!"{moduleName}\t{name}\t{axiomText}"
        if let (some out, some selection) := (proofs, proofSelection) then
          if selection == "all" || selection == name.toString then
            let body ← liftTermElabM <| withOptions (·.setBool `pp.proofs true) <|
              Meta.ppExpr info.value
            out.putStrLn s!"\n[{moduleName}] {name}\n{statement} :=\n{body.pretty 108}"
            proofCount := proofCount + 1
        theoremCount := theoremCount + 1
        moduleCount := moduleCount + 1
        distinct := distinct.insert name
    liftIO <| IO.println s!"catalogued {moduleName}: {moduleCount}"
  unless distinct.contains `KqR75.PhysicalCompletion.eventually_designFibre_bilateral do
    throwError "the bilateral R75 theorem is missing"
  unless distinct.contains `KqR75.SlotPairMargins.round_quotas do
    throwError "the quota rounding theorem is missing"
  if proofSelection.isSome && proofCount == 0 then
    throwError "no proof matched the requested name"
  liftIO <| IO.println s!"PASS_CATALOGUE modules={modules.length} records={theoremCount} distinct={distinct.size} proofs={proofCount}"

#print_frozen_theorems

