/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalAffineUnits
public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization

/-!
# Input maps and scalar relations on reciprocal addition charts

Expose the actual affine inputs, reciprocal line relation, and normalized
homogeneous output after arbitrary algebra specialization.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- First affine input of a reciprocal chart. -/
def reciprocalInputLeft (b : Bool) : Coordinate W 2 →ₐ[R]
    additionChartRing W (reciprocalIndex b) :=
  (additionChartAlgRestriction W (reciprocalIndex b)).comp (productLeft W)

/-- Second affine input of a reciprocal chart. -/
def reciprocalInputRight (b : Bool) : Coordinate W 2 →ₐ[R]
    additionChartRing W (reciprocalIndex b) :=
  (additionChartAlgRestriction W (reciprocalIndex b)).comp (productRight W)

/-- The reciprocal line relation survives arbitrary algebra specialization. -/
theorem reciprocalSpecialization_line (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) :
    f (reciprocalChartSlope W b) *
        (f (reciprocalInputLeft W b (coord W 2 1)) -
          f (reciprocalInputRight W b (coord W 2 1))) =
      f (reciprocalInputLeft W b (coord W 2 0)) -
        f (reciprocalInputRight W b (coord W 2 0)) := by
  simpa only [reciprocalInputLeft, reciprocalInputRight, AlgHom.comp_apply,
    productX₁, productX₂, productY₁, productY₂, secantDenominator,
    verticalSecantDenominator, map_sub, map_mul] using
    congrArg f (reciprocalChartSlope_line W b)

/-- The actual reciprocal coordinates retain their unit normalization. -/
theorem reciprocalSpecialization_coord (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) (i : Fin 3) :
    f (reciprocalChartAddition W b (coord W 1 i)) =
      f (reciprocalChartInverse W b) *
        reciprocalXYZ (W.map (algebraMap R S))
          (f (reciprocalInputLeft W b (coord W 2 0)))
          (f (reciprocalInputRight W b (coord W 2 0)))
          (f (reciprocalInputLeft W b (coord W 2 1)))
          (f (reciprocalChartSlope W b)) i := by
  rw [reciprocalChartAddition_coord, map_mul, reciprocalCoordinates_map]
  rfl

/-- The reversed secant denominator is a unit on the actual reciprocal secant domain. -/
theorem reciprocalSpecialization_secant_unit
    (f : additionChartRing W (reciprocalIndex false) →ₐ[R] S) :
    IsUnit (f (reciprocalInputLeft W false (coord W 2 1)) -
      f (reciprocalInputRight W false (coord W 2 1))) := by
  simpa only [reciprocalInputLeft, reciprocalInputRight, AlgHom.comp_apply,
    productY₁, productY₂, Bool.false_eq_true, ite_false, verticalSecantDenominator,
    map_sub] using (reciprocalChartDenominator_isUnit W false).map f

end FLT.Mazur.WeierstrassIntegralChart
