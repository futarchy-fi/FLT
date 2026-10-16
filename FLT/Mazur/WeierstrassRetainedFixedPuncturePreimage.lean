/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedSmoothing
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Exact puncture preimages for full retained corrections

The original retained comparison multiplies the two coordinates by units.
It therefore preserves the full outgoing and incoming opens at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ : R) (q : Rˣ) (hq : π * ↑q = τ)
  (V : (ChartRing π)ˣ)
local notation "F" => retainedFixedSmoothingChart π τ (q : R) hq V
local notation "E" => retainedFixedSmoothingEvaluation π τ (q : R) hq V

/-- The complete corrected outgoing puncture has precisely its original full preimage. -/
theorem retainedFixedSmoothingChart_left_preimage :
    F ⁻¹' Set.range (leftBranchOpen R τ) = Set.range (leftBranchOpen R π) := by
  rw [leftBranchOpen_range, leftBranchOpen_range]
  ext z
  change E (leftCoordinate τ) ∉ z.asIdeal ↔ leftCoordinate π ∉ z.asIdeal
  rw [retainedFixedSmoothingEvaluation_left]
  exact not_congr ((z.asIdeal.mul_unit_mem_iff_mem (V⁻¹).isUnit).trans
    (z.asIdeal.unit_mul_mem_iff_mem (q.isUnit.map (algebraMap R (ChartRing π)))))

/-- The complete corrected incoming puncture also retains precisely its original preimage. -/
theorem retainedFixedSmoothingChart_right_preimage :
    F ⁻¹' Set.range (rightBranchOpen R τ) = Set.range (rightBranchOpen R π) := by
  rw [rightBranchOpen_range, rightBranchOpen_range]
  ext z
  change E (rightCoordinate τ) ∉ z.asIdeal ↔ rightCoordinate π ∉ z.asIdeal
  rw [retainedFixedSmoothingEvaluation_right]
  exact not_congr (z.asIdeal.mul_unit_mem_iff_mem V.isUnit)

end FLT.Mazur.WeierstrassModificationX
