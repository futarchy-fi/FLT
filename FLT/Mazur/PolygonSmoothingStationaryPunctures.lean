/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureCalculus

/-!
# Stationary full punctures of a nilpotent shear

An annihilated chart increment and scalar drift make both full substitutions
identity, including the inverse multiplier on the opposite branch.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : IsNilpotent e)

/-- An annihilated chart increment makes the complete multiplier the unit one. -/
theorem nilpotentChartMultiplier_eq_one (p : ChartRing t)
    (hp : algebraMap R (ChartRing t) e * p = 0) :
    nilpotentChartMultiplier t e he p = 1 := by
  apply Units.ext
  simp only [nilpotentChartMultiplier_val, hp, add_zero, Units.val_one]

/-- Both original punctures are stationary when the chart and scalar increments vanish. -/
theorem nilpotentShearPunctureEquiv_eq_refl (c : R) (p : ChartRing t)
    (hc : e * c = 0) (hp : algebraMap R (ChartRing t) e * p = 0) (b : Bool) :
    nilpotentShearPunctureEquiv t e he c p b = AlgEquiv.refl := by
  have hu := nilpotentChartMultiplier_eq_one t e he p hp
  have hv : nilpotentMultiplier e he c = 1 := by
    apply Units.ext
    simp only [nilpotentMultiplier_val, hc, add_zero, Units.val_one]
  cases b
  · have h : nilpotentShearRightUnit t e he c p = pointUnit (AlgHom.id R _) := by
      simp only [nilpotentShearRightUnit, hu, hv, map_one, inv_one, mul_one, one_mul]
    ext z : 1
    change evalUnit (nilpotentShearRightUnit t e he c p) z = z
    rw [h, evalUnit_pointUnit, AlgHom.id_apply]
  · have h : nilpotentShearLeftUnit t e he p = pointUnit (AlgHom.id R _) := by
      simp only [nilpotentShearLeftUnit, hu, map_one, mul_one]
    ext z : 1
    change evalUnit (nilpotentShearLeftUnit t e he p) z = z
    rw [h, evalUnit_pointUnit, AlgHom.id_apply]

end FLT.Mazur.PolygonSmoothing
