import PersistencePays
import Lean.Util.CollectAxioms

/-! Reject unproved or nonstandard proof axioms in every exported project declaration. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`PersistencePays).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} project declarations. Only propext, Classical.choice and Quot.sound are allowed."
