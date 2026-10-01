/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.OneGonGluing
import Mathlib.Data.ZMod.Basic
import Lean

/-! # Axiom audit and characteristic-two check for the one-gon charts -/

open Lean Elab Command

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Traverse every new declaration and its complete transitive axiom dependencies.
run_elab do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`FLT.Mazur.OneGonTransition).isPrefixOf n ||
        (`FLT.Mazur.OneGonGluing).isPrefixOf n then
      let axioms ← Lean.collectAxioms n
      for a in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  unless count > 0 do
    throwError "No one-gon declarations audited"

-- The transition does not require that two be invertible.
example : Function.Involutive (FLT.Mazur.OneGonTransition.transition (ZMod 2)) :=
  FLT.Mazur.OneGonTransition.transition_involutive (ZMod 2)

-- It is defined even over a coefficient ring that is not a field.
example : Function.Involutive (FLT.Mazur.OneGonTransition.transition ℤ) :=
  FLT.Mazur.OneGonTransition.transition_involutive ℤ
