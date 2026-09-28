/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
import FermatsLastTheorem
import Lean

/-! # Recursive dependency check for the final assembly

Check the names of the remaining arithmetic leaves, including theorem bodies
and types throughout the dependency graph.
-/

open Lean Elab Command

private partial def assemblyLeaves (env : Environment) (n : Name) :
    StateT NameSet TermElabM (Array Name) := do
  if (← get).contains n then return #[]
  modify (·.insert n)
  let some ci := env.find? n | throwError "Missing declaration: {n}"
  let deps := ci.type.getUsedConstants ++
    ((ci.value? true).map Expr.getUsedConstants).getD #[]
  let isArithmeticAxiom := match ci with
    | .axiomInfo _ => !(#[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains n)
    | _ => false
  let mut leaves := if isArithmeticAxiom || deps.contains ``sorryAx then #[n] else #[]
  for d in deps do
    leaves := leaves ++ (← assemblyLeaves env d)
  return leaves

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Traverse the entire proof dependency graph, including imported theorem bodies.
run_elab do
  let (leaves, visited) ←
    (assemblyLeaves (← getEnv) ``PNat.pow_add_pow_ne_pow).run {}
  let expected := #[``Mazur_statement,
    ``GaloisRepresentation.IsHardlyRamified.lifts,
    ``GaloisRepresentation.IsHardlyRamified.mem_isCompatible]
  unless leaves.size == expected.size && expected.all leaves.contains do
    throwError "Unexpected arithmetic leaves: {leaves}"
  if visited.contains ``GaloisRepresentation.IsHardlyRamified.three_adic then
    throwError "The final assembly still uses the old three-adic endpoint"
