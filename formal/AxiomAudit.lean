import SetStone
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Run with `lake env lean AxiomAudit.lean` after building.
Inspect all project declarations, including generated helpers, rather than
trusting a hand-maintained list of headline theorems. Declarations are selected
by their defining module, so private declarations (whose names do not start
with the `SetStone` namespace) are audited too. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut declarations := 0
  let mut theorems := 0
  let mut privates := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`SetStone).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    declarations := declarations + 1
    if isPrivateName name then
      privates := privates + 1
    if let .thmInfo _ := info then
      theorems := theorems + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Quot.sound do
        throwError "Forbidden axiom {ax} in {name}"
  if declarations == 0 || theorems == 0 then
    throwError "Empty project audit"
  logInfo m!"Audited {declarations} project declarations ({theorems} theorems, {privates} private); only propext and Quot.sound permitted."
