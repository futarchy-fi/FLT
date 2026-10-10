/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalOrdinaryUnits
public import FLT.Mazur.WeierstrassSplitNodalAffineParameters
public import FLT.Mazur.WeierstrassOrdinarySpecializationUnits

/-!
# The actual ordinary output parameter over every coefficient algebra

The original ordinary chart relations imply multiplication of the Laurent
parameter as an equality in the target ring, including rings with nilpotents.
The actual output Y coordinate is a unit for smooth affine inputs.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (a : Rˣ) (b : Bool)
  (f : additionChartRing (splitNodalEquation a) (ordinaryIndex b) →ₐ[R] S)
  (r s : S)
  (hx₁ : f (ordinaryInputLeft (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 0)) = r * (r + algebraMap R S a))
  (hy₁ : f (ordinaryInputLeft (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 1)) = r ^ 2 * (r + algebraMap R S a))
  (hx₂ : f (ordinaryInputRight (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 0)) = s * (s + algebraMap R S a))
  (hy₂ : f (ordinaryInputRight (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 1)) = s ^ 2 * (s + algebraMap R S a))

include hx₁ hy₁ hx₂ hy₂

/-- The original chart's ordinary slope satisfies the nodal parameter relation. -/
theorem splitNodalOrdinary_specialized_slope :
    f (ordinaryChartSlope (splitNodalEquation a) b) * (r + s + algebraMap R S a) =
      r ^ 2 + r * s + s ^ 2 + algebraMap R S a * (r + s) := by
  apply splitNodalOrdinary_slope_relation
  · simpa only [hx₁, hx₂, hy₁, hy₂] using
      ordinarySpecialization_line (splitNodalEquation a) b f
  · have h := ordinarySpecialization_cubic (splitNodalEquation a) b f
    dsimp only at h
    rw [hx₁, hx₂, hy₁, hy₂] at h
    simpa only [splitNodalEquation, WeierstrassCurve.map,
      toAffine, map_zero, zero_mul, add_zero] using h
  · have h := ordinarySpecialization_denominator_unit (splitNodalEquation a) b f
    rw [hx₁, hx₂, hy₁, hy₂] at h
    simpa only [splitNodalEquation, WeierstrassCurve.map,
      toAffine, map_zero, zero_mul, add_zero] using h

/-- The original ordinary output lies in the smooth Y chart for unit slope inputs. -/
theorem splitNodalOrdinary_specialized_y_isUnit
    (hr : IsUnit r) (hs : IsUnit s)
    (hra : IsUnit (r + algebraMap R S a)) (hsa : IsUnit (s + algebraMap R S a)) :
    IsUnit (f (ordinaryChartAddition (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 1))) := by
  have h := splitNodalOrdinary_y_isUnit
    (splitNodalOrdinary_specialized_slope a b f r s hx₁ hy₁ hx₂ hy₂) hr hs hra hsa
  simp only [ordinarySpecialization_coord, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [hx₁, hx₂, hy₁]
  simpa only [splitNodalEquation, WeierstrassCurve.map, toAffine, map_zero] using h

/-- The actual ordinary output satisfies the homogeneous tangent multiplication identity. -/
theorem splitNodalOrdinary_specialized_parameter :
    r * s * (f (ordinaryChartAddition (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 1)) + algebraMap R S a *
      f (ordinaryChartAddition (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 0))) =
      (r + algebraMap R S a) * (s + algebraMap R S a) *
        f (ordinaryChartAddition (splitNodalEquation a) b
          (coord (splitNodalEquation a) 2 1)) := by
  have h := splitNodalOrdinary_parameter_identity
    (splitNodalOrdinary_specialized_slope a b f r s hx₁ hy₁ hx₂ hy₂)
  simp only [ordinarySpecialization_coord, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hx₁, hx₂, hy₁]
  simpa only [splitNodalEquation, WeierstrassCurve.map, toAffine, map_zero] using h

end FLT.Mazur.WeierstrassIntegralChart
