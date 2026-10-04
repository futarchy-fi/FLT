/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.FormalImmersionLocal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Field.ZMod
import Lean

/-! # Trust audit and tangent-direction regression -/

open Lean Elab Command

run_elab do
  for n in #[``RingHom.map_maximalIdeal_eq_of_surjective_mod_sq,
      ``RingHom.surjective_of_surjective_mod_maximalIdeal_sq,
      ``RingHom.surjective_mod_sq_of_residue_and_cotangent,
      ``RingHom.surjective_of_residue_and_cotangent,
      ``RingHom.comp_injective_of_surjective_mod_maximalIdeal_sq] do
    for a in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {a} in {n}"

-- Constants already provide every constant coefficient, but miss the tangent
-- direction X. Residue surjectivity alone must not replace the cotangent input.
example : ¬ Function.Surjective
    (PowerSeries.C : ZMod 3 →+* PowerSeries (ZMod 3)) := by
  intro h
  obtain ⟨a, ha⟩ := h PowerSeries.X
  have heq := congrArg (fun f : PowerSeries (ZMod 3) ↦ f.coeff 1) ha
  simp at heq
