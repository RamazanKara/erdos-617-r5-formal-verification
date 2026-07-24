/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
import Erdos617.Sat.LRATStage

/-!
# Reification of a staged LRAT theorem

`LRATStage` deliberately keeps large proofs in the compact form
`Sat.Fmla.proof ctx []`.  This command reuses Mathlib's kernel-checked
reifier after the last stage and exports the corresponding ordinary
propositional theorem, with one `Prop` binder for every DIMACS variable.
-/

open Lean Elab Command

namespace Erdos617.LRATReify

def reifyStoredProof (outputName contextName proofName : Name)
    (variableCount : Nat) : MetaM Unit := do
  let environment ← getEnv
  let some (.defnInfo contextInfo) := environment.find? contextName
    | throwError m!"stored LRAT context is not a definition: {contextName}"
  let context := Lean.mkConst contextName
  let proof := Lean.mkConst proofName
  let actualType ← Meta.inferType proof
  let expectedType :=
    Lean.mkApp2 (Lean.mkConst ``Sat.Fmla.proof) context
      (Mathlib.Tactic.Sat.buildClause #[])
  unless ← Meta.isDefEq actualType expectedType do
    throwError m!"stored LRAT theorem has the wrong type: {proofName}"
  let (type, value) :=
    Mathlib.Tactic.Sat.buildReify
      context contextInfo.value proof variableCount
  addDecl <| Declaration.thmDecl {
    name := outputName
    levelParams := []
    type
    value
  }

end Erdos617.LRATReify

elab "lrat_reify_stored " output:ident ppSpace variableCount:num
    ppSpace context:ident ppSpace proof:ident : command => do
  let outputName := (← getCurrNamespace) ++ output.getId
  let contextName ← resolveGlobalConstNoOverload context
  let proofName ← resolveGlobalConstNoOverload proof
  Command.liftTermElabM do
    Erdos617.LRATReify.reifyStoredProof
      outputName contextName proofName variableCount.getNat
