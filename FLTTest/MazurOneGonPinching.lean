/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.OneGonLocalFactorization
import FLT.Mazur.OneGonMapGluing
import Mathlib.Algebra.Field.ZMod
import Lean

/-! # Trust audit for the ring-theoretic one-gon pinching -/

open Lean Elab Command

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every declaration and its transitive dependencies.
run_elab do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`FLT.Mazur.OneGonPinchingAlgebra).isPrefixOf n ||
        (`FLT.Mazur.OneGonAffineDescent).isPrefixOf n ||
        (`FLT.Mazur.OneGonDescentUniqueness).isPrefixOf n ||
        (`FLT.Mazur.OneGonLocalizedPinching).isPrefixOf n ||
        (`FLT.Mazur.OneGonLocalMaps).isPrefixOf n ||
        (`FLT.Mazur.OneGonMapGluing).isPrefixOf n ||
        (`FLT.Mazur.OneGonNodeFiber).isPrefixOf n ||
        (`FLT.Mazur.OneGonLocalFactorization).isPrefixOf n then
      let axioms ← Lean.collectAxioms n
      for a in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  unless count > 0 do
    throwError "No pinching declarations audited"

example : Function.Surjective (FLT.Mazur.OneGonPinchingAlgebra.endpoints (R := ZMod 2)) :=
  FLT.Mazur.OneGonPinchingAlgebra.endpoints_surjective

example : Function.Surjective (FLT.Mazur.OneGonPinchingAlgebra.endpoints (R := ℤ)) :=
  FLT.Mazur.OneGonPinchingAlgebra.endpoints_surjective

example : Module.Finite (FLT.Mazur.PolygonNodePresentation.B (R := ℤ)) (Polynomial ℤ) :=
  inferInstance

example : AlgebraicGeometry.IsFinite
    (FLT.Mazur.OneGonPinchingAlgebra.toPinching (R := ZMod 2)) :=
  inferInstance

example : CategoryTheory.Epi
    (FLT.Mazur.OneGonPinchingAlgebra.toPinching (R := ZMod 2)) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  infer_instance
