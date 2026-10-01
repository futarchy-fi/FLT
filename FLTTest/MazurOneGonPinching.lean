/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.OneGonPinchingAlgebra
import Mathlib.Data.ZMod.Basic
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
    if (`FLT.Mazur.OneGonPinchingAlgebra).isPrefixOf n then
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
