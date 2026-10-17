/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentShear
public import FLT.Mazur.PolygonSmoothingLaurentFactorization

/-!
# The full puncture substitutions of a nilpotent node shear

The outgoing puncture sees the prescribed unit multiplier. The opposite
puncture sees the scalar smoothing drift divided by its own full multiplier.
These formulas retain the inverse terms needed at higher arithmetic orders.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : IsNilpotent e)
local notation "L" => R[T;T⁻¹]
local notation "l" => leftLaurentMap t
local notation "r" => AlgHom.comp (leftLaurentMap t) (branchSwapMap t)

/-- The complete outgoing coordinate unit, retaining the full polynomial multiplier. -/
def nilpotentShearLeftUnit (p : ChartRing t) : Lˣ :=
  pointUnit (AlgHom.id R L) *
    Units.map (l).toMonoidHom (nilpotentChartMultiplier t e he p)

/-- The full opposite coordinate unit includes the compensating inverse and scalar drift. -/
def nilpotentShearRightUnit (c : R) (p : ChartRing t) : Lˣ :=
  Units.map (algebraMap R L).toMonoidHom (nilpotentMultiplier e he c) *
    (pointUnit (AlgHom.id R L) *
      (Units.map (r).toMonoidHom (nilpotentChartMultiplier t e he p))⁻¹)

/-- The outgoing unit has exactly the prescribed full nilpotent increment. -/
theorem nilpotentShearLeftUnit_val (p : ChartRing t) :
    (nilpotentShearLeftUnit t e he p : L) = T 1 * (1 + C e * l p) := by
  change T 1 * l (nilpotentChartMultiplier t e he p : ChartRing t) = _
  rw [nilpotentChartMultiplier_val, map_add, map_one, map_mul, AlgHom.commutes]
  rfl

/-- The opposite unit keeps the entire inverse, rather than only its constant term. -/
theorem nilpotentShearRightUnit_val (c : R) (p : ChartRing t) :
    (nilpotentShearRightUnit t e he c p : L) =
      C (1 + e * c) * (T 1 * r (↑(nilpotentChartMultiplier t e he p)⁻¹)) := by
  change C (nilpotentMultiplier e he c : R) *
    (T 1 * r (↑(nilpotentChartMultiplier t e he p)⁻¹)) = _
  rw [nilpotentMultiplier_val]

/-- Every function on the outgoing puncture follows the constructed full Laurent substitution. -/
theorem nilpotentShear_left_puncture (c : R) (p : ChartRing t) :
    (l).comp (nilpotentShearEquiv t e he c p).toAlgHom =
      (evalUnit (nilpotentShearLeftUnit t e he p)).comp
        (leftLaurentMap ((1 + e * c) * t)) := by
  apply nodeMap_factor_left
  change l (nilpotentShearEquiv t e he c p (leftCoordinate _)) = _
  rw [nilpotentShearEquiv_left, map_mul, leftLaurentMap_left, map_add, map_one,
    map_mul, AlgHom.commutes, nilpotentShearLeftUnit_val]
  rfl

/-- The entire opposite puncture follows its compensating inverse Laurent substitution. -/
theorem nilpotentShear_right_puncture (c : R) (p : ChartRing t) :
    (r).comp (nilpotentShearEquiv t e he c p).toAlgHom =
      (evalUnit (nilpotentShearRightUnit t e he c p)).comp
        ((leftLaurentMap ((1 + e * c) * t)).comp (branchSwapMap ((1 + e * c) * t))) := by
  apply nodeMap_factor_right
  change r (nilpotentShearEquiv t e he c p (rightCoordinate _)) = _
  rw [nilpotentShearEquiv_right, map_mul, map_mul, AlgHom.commutes,
    nilpotentShearRightUnit_val]
  change C (1 + e * c) * (leftLaurentMap t (branchSwapMap t (rightCoordinate t)) * _) = _
  rw [branchSwapMap_right, leftLaurentMap_left]

end FLT.Mazur.PolygonSmoothing
