/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalSlopeRelations
public import FLT.Mazur.WeierstrassSplitNodalAffineParameters
public import FLT.Mazur.WeierstrassReciprocalCubicSpecialization

/-!
# The actual reciprocal output parameter over every coefficient algebra

The original reciprocal chart relations imply multiplication of the Laurent
parameter as an equality in the target ring, including rings with nilpotents.
The normalization inverse is retained throughout the calculation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (a : Rˣ) (b : Bool)
  (f : additionChartRing (splitNodalEquation a) (reciprocalIndex b) →ₐ[R] S)
  (r s : S)
  (hx₁ : f (reciprocalInputLeft (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 0)) = r * (r + algebraMap R S a))
  (hy₁ : f (reciprocalInputLeft (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 1)) = r ^ 2 * (r + algebraMap R S a))
  (hx₂ : f (reciprocalInputRight (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 0)) = s * (s + algebraMap R S a))
  (hy₂ : f (reciprocalInputRight (splitNodalEquation a) b
    (coord (splitNodalEquation a) 2 1)) = s ^ 2 * (s + algebraMap R S a))

include hx₁ hy₁ hx₂ hy₂

/-- The original chart's reciprocal slope satisfies the nodal parameter relation. -/
theorem splitNodalReciprocal_specialized_slope :
    f (reciprocalChartSlope (splitNodalEquation a) b) *
        (r ^ 2 + r * s + s ^ 2 + algebraMap R S a * (r + s)) =
      r + s + algebraMap R S a := by
  apply splitNodalReciprocal_slope_relation
  · simpa only [hx₁, hx₂, hy₁, hy₂] using
      reciprocalSpecialization_line (splitNodalEquation a) b f
  · have h := reciprocalSpecialization_cubic (splitNodalEquation a) b f
    dsimp only at h
    rw [hx₁, hx₂, hy₁, hy₂] at h
    simpa only [splitNodalEquation, WeierstrassCurve.map,
      toAffine, map_zero, zero_mul, add_zero] using h
  · have h := reciprocalSpecialization_denominator_unit (splitNodalEquation a) b f
    dsimp only at h
    rw [hx₁, hx₂, hy₁, hy₂] at h
    simpa only [splitNodalEquation, WeierstrassCurve.map,
      toAffine, map_zero, zero_mul, add_zero] using h

/-- The normalized output tangent parameter is the product of the input tangent parameters. -/
theorem splitNodalReciprocal_specialized_parameter :
    r * s * (1 + algebraMap R S a *
        f (reciprocalChartAddition (splitNodalEquation a) b
          (coord (splitNodalEquation a) 1 0))) =
      (r + algebraMap R S a) * (s + algebraMap R S a) := by
  let m := f (reciprocalChartSlope (splitNodalEquation a) b)
  let c := f (reciprocalChartInverse (splitNodalEquation a) b)
  let v := reciprocalXYZ (⟨algebraMap R S a, 0, 0, 0, 0⟩ : WeierstrassCurve S)
    (r * (r + algebraMap R S a)) (s * (s + algebraMap R S a))
    (r ^ 2 * (r + algebraMap R S a)) m
  have he : (splitNodalEquation a).map (algebraMap R S) =
      (⟨algebraMap R S a, 0, 0, 0, 0⟩ : WeierstrassCurve S) := by
    ext <;> simp [splitNodalEquation, WeierstrassCurve.map]
  have hv := splitNodalReciprocal_parameter_identity
    (splitNodalReciprocal_specialized_slope a b f r s hx₁ hy₁ hx₂ hy₂)
  have h0 : f (reciprocalChartAddition (splitNodalEquation a) b
      (coord (splitNodalEquation a) 1 0)) = c * v 0 := by
    simpa only [he, hx₁, hx₂, hy₁] using
      reciprocalSpecialization_coord (splitNodalEquation a) b f 0
  have h1 : c * v 1 = 1 := by
    have h := reciprocalSpecialization_coord (splitNodalEquation a) b f 1
    simpa only [he, hx₁, hx₂, hy₁, coord_self, map_one] using h.symm
  rw [h0]
  change r * s * (v 1 + algebraMap R S a * v 0) =
    (r + algebraMap R S a) * (s + algebraMap R S a) * v 1 at hv
  linear_combination c * hv +
    ((r + algebraMap R S a) * (s + algebraMap R S a) - r * s) * h1

end FLT.Mazur.WeierstrassIntegralChart
