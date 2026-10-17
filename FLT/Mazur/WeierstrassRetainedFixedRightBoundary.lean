/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedBoundary

/-!
# The full right parameter of a fixed-smoothing retained chart

This boundary needs no predecessor. In particular it applies to the first
retained node where the incoming edge comes from an original initial chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ : R) (q : Rˣ) (hq : π * (q : R) = τ)
  (U : (ChartRing π)ˣ)
local notation "L" => R[T;T⁻¹]
local notation "F" => AlgHom.comp (leftLaurentMap π) (branchSwapMap π)

/-- The original right coordinate multiplied by the entire retained root correction. -/
def retainedFixedRightUnit : Lˣ :=
  LaurentUnitPoints.pointUnit (AlgHom.id R L) * Units.map (F).toMonoidHom U

/-- The full right evaluation has precisely this unit coordinate. -/
theorem retainedFixedSmoothingEvaluation_right_unit :
    F (retainedFixedSmoothingEvaluation π τ (q : R) hq U (rightCoordinate τ)) =
      (retainedFixedRightUnit π U : L) := by
  rw [retainedFixedSmoothingEvaluation_right, map_mul]
  change (leftLaurentMap π) (branchSwapMap π (rightCoordinate π)) * _ = _
  rw [branchSwapMap_right, leftLaurentMap_left]
  rfl

/-- The full first incoming puncture factors through its exact right parameter. -/
@[reassoc] theorem retainedFixedSmoothingChart_right :
    rightBranchOpen R π ≫ retainedFixedSmoothingChart π τ (q : R) hq U =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := R) (retainedFixedRightUnit π U)).toRingHom) ≫
          rightBranchOpen R τ := by
  rw [rightBranchOpen_eq_spec, retainedFixedSmoothingChart, ← Spec.map_comp]
  exact boundary_rightBranchOpen τ
    ((F).comp (retainedFixedSmoothingEvaluation π τ (q : R) hq U))
    (retainedFixedRightUnit π U) (retainedFixedSmoothingEvaluation_right_unit π τ q hq U)

end FLT.Mazur.WeierstrassModificationX
