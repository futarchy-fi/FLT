/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassTriangularCoordinates
public import FLT.Mazur.WeierstrassAffineVariableChangeMap

/-!
# The original affine map uniquely determines its admissible change

Normal-form coefficient uniqueness recovers translations, both powers of the
unit scale, and the shear. This works over arbitrary commutative rings.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)

/-- Admissible changes inducing the same actual affine map coincide. -/
theorem affineVariableChangeMap_injective (C D : VariableChange R)
    (hC : C • V = W) (hD : D • V = W)
    (he : affineVariableChangeMap V W C hC = affineVariableChangeMap V W D hD) : C = D := by
  have hx := DFunLike.congr_fun he (coord V 2 0)
  have hy := DFunLike.congr_fun he (coord V 2 1)
  rw [affineVariableChangeMap_x, affineVariableChangeMap_x] at hx
  rw [affineVariableChangeMap_y, affineVariableChangeMap_y] at hy
  have hxx : algebraMap R _ C.r + algebraMap R _ ((C.u : R) ^ 2) * coord W 2 0 +
        algebraMap R _ 0 * coord W 2 1 =
      algebraMap R _ D.r + algebraMap R _ ((D.u : R) ^ 2) * coord W 2 0 +
        algebraMap R _ 0 * coord W 2 1 := by
    simp only [map_pow, map_zero, zero_mul, add_zero]
    linear_combination hx
  have hyy : algebraMap R _ C.t +
        algebraMap R _ ((C.u : R) ^ 2 * C.s) * coord W 2 0 +
        algebraMap R _ ((C.u : R) ^ 3) * coord W 2 1 =
      algebraMap R _ D.t + algebraMap R _ ((D.u : R) ^ 2 * D.s) * coord W 2 0 +
        algebraMap R _ ((D.u : R) ^ 3) * coord W 2 1 := by
    simp only [map_pow, map_mul]
    linear_combination hy
  obtain ⟨hr, hs₂, _⟩ := lowCoordinate_injective W hxx
  obtain ⟨ht, hs, hs₃⟩ := lowCoordinate_injective W hyy
  have hu₂ : C.u ^ 2 = D.u ^ 2 := Units.ext hs₂
  have hu₃ : C.u ^ 3 = D.u ^ 3 := Units.ext hs₃
  have hu : C.u = D.u := by
    calc
      C.u = C.u ^ 3 / C.u ^ 2 := by rw [pow_succ, mul_comm, mul_div_cancel_right]
      _ = D.u ^ 3 / D.u ^ 2 := by rw [hu₂, hu₃]
      _ = D.u := by rw [pow_succ, mul_comm, mul_div_cancel_right]
  have hshear : C.s = D.s := by
    rw [hu] at hs
    exact (D.u.isUnit.pow 2).mul_left_cancel hs
  exact VariableChange.ext hu hr hshear ht

end FLT.Mazur.WeierstrassIntegralChart
