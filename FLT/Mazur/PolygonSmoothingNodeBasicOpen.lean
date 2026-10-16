/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingMarkedSection
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# An explicit arithmetic node open avoiding the two unit markings

The denominator (1-x)(1-y) excludes the unit marking on either incident
branch, using the original inverse Laurent transition on the incoming branch.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R] (t : R)

/-- The same polynomial denominator on the full arithmetic node chart. -/
def nodeMarkingDenominator : ChartRing t :=
  (1 - leftCoordinate t) * (1 - rightCoordinate t)

/-- The explicit neighborhood excludes both incident unit markings. -/
def nodeMarkingBasicOpen : (chart R t).Opens :=
  PrimeSpectrum.basicOpen (nodeMarkingDenominator t)

/-- The denominator vanishes on the original outgoing unit marking. -/
theorem nodeMarkingDenominator_marked :
    markedEvaluation t 1 (nodeMarkingDenominator t) = 0 := by
  simp [nodeMarkingDenominator]

/-- The incoming inverse Laurent coordinate still evaluates to one at the unit marking. -/
theorem precedingLaurentMap_unit_right :
    LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)
      (precedingLaurentMap R t (rightCoordinate t)) = 1 := by
  rw [precedingLaurentMap_right, LaurentUnitPoints.evalUnit_T]
  simp

/-- The same denominator vanishes after the actual incoming transition at the unit marking. -/
theorem nodeMarkingDenominator_preceding_marked :
    LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)
      (precedingLaurentMap R t (nodeMarkingDenominator t)) = 0 := by
  simp only [nodeMarkingDenominator, map_mul, map_sub, map_one,
    precedingLaurentMap_unit_right, sub_self, mul_zero]

/-- The outgoing unit marking is absent from this explicit arithmetic open. -/
theorem markedSection_not_nodeMarkingBasicOpen (z : Spec (.of R)) :
    markedSection t 1 z ∉ nodeMarkingBasicOpen t := by
  change ¬ markedEvaluation t 1 (nodeMarkingDenominator t) ∉ z.asIdeal
  rw [nodeMarkingDenominator_marked]
  exact not_not.mpr z.asIdeal.zero_mem

/-- The incoming copy of the same unit marking is absent from the same open. -/
theorem preceding_markedSection_not_nodeMarkingBasicOpen (z : Spec (.of R)) :
    precedingBranch R t (markedTorusSection (1 : Rˣ) z) ∉ nodeMarkingBasicOpen t := by
  rw [precedingBranch_eq_spec]
  change ¬ LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)
    (precedingLaurentMap R t (nodeMarkingDenominator t)) ∉ z.asIdeal
  rw [nodeMarkingDenominator_preceding_marked]
  exact not_not.mpr z.asIdeal.zero_mem

end FLT.Mazur.PolygonSmoothing
