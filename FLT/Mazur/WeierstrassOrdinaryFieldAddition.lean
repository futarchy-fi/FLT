/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinarySpecializationUnits
public import FLT.Mazur.WeierstrassAdditionChartCompatibility
public import FLT.Mazur.WeierstrassProjectivePointNegation

/-!
# Ordinary integral charts give the classical field point sum

Both ordinary slope charts specialize to Mathlib's slope. Their denominator
units exclude opposite inputs, and the actual output vector therefore
represents the classical projective sum of their two affine inputs.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R) (b : Bool)
  (f : additionChartRing W (ordinaryIndex b) →ₐ[R] K)

/-- The universal ordinary slope becomes the actual field point slope. -/
theorem ordinarySpecialization_field_slope [DecidableEq K] :
    f (ordinaryChartSlope W b) = (W.map (algebraMap R K)).toAffine.slope
      (f (ordinaryInputLeft W b (coord W 2 0)))
      (f (ordinaryInputRight W b (coord W 2 0)))
      (f (ordinaryInputLeft W b (coord W 2 1)))
      (f (ordinaryInputRight W b (coord W 2 1))) := by
  cases b
  · exact secantSlope_field W f
  · exact tangentSlope_field W f

/-- The actual ordinary chart denominators exclude opposite affine inputs. -/
theorem ordinarySpecialization_not_opposite :
    ¬(f (ordinaryInputLeft W b (coord W 2 0)) =
        f (ordinaryInputRight W b (coord W 2 0)) ∧
      f (ordinaryInputLeft W b (coord W 2 1)) =
        (W.map (algebraMap R K)).toAffine.negY
          (f (ordinaryInputRight W b (coord W 2 0)))
          (f (ordinaryInputRight W b (coord W 2 1)))) := by
  rintro ⟨hx, hy⟩
  rcases ordinarySpecialization_denominator_unit W b f with hd | hd
  · exact hd.ne_zero (sub_eq_zero.mpr hx)
  · apply hd.ne_zero
    simp only [Affine.negY, map_a₁, map_a₃] at hy
    linear_combination hy

/-- The actual ordinary output vector represents the classical projective sum. -/
theorem ordinarySpecialization_projective_sum
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputLeft W b (coord W 2 0))) (f (ordinaryInputLeft W b (coord W 2 1))))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputRight W b (coord W 2 0))) (f (ordinaryInputRight W b (coord W 2 1)))) :
    (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)).point =
      (⟦fun i => f (ordinaryChartAddition W b (coord W 2 i))⟧ : PointClass K) := by
  classical
  have ha := (Point.toAffineAddEquiv (W.map (algebraMap R K)).toProjective).symm.map_add
    (.some _ _ h₁) (.some _ _ h₂)
  change Point.fromAffine (Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂) =
    Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂) at ha
  rw [← ha, Affine.Point.add_some (ordinarySpecialization_not_opposite W b f)]
  apply congrArg (fun v : Fin 3 → K => (⟦v⟧ : PointClass K))
  funext i
  exact ((ordinarySpecialization_coord W b f i).trans (by
    rw [ordinarySpecialization_field_slope])).symm

end FLT.Mazur.WeierstrassIntegralChart
