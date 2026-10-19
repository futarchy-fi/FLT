/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityScaledCoordinates

/-!
# Generic identification of the regular scaled Vélu formulas

The regular finite sums are precisely the original rational x and slope sums.
In particular, the construction retains the original map rather than a new one.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

omit [DecidableEq K] in
/-- The original generic pole term written using its reciprocal denominator. -/
theorem infinity_lift_polePart (a b c : K) :
    liftX E (polePart (C a) (C b) (C c) RatFunc.X) =
      algebraMap K (FunctionField E) b *
          (liftX E RatFunc.X - algebraMap K _ c)⁻¹ +
        algebraMap K _ a * (liftX E RatFunc.X - algebraMap K _ c)⁻¹ ^ 2 := by
  simp only [polePart, liftX, map_add, map_div₀, map_sub, map_pow]
  simp only [div_eq_mul_inv, inv_pow]
  rfl

omit [DecidableEq K] in
/-- The original generic slope term written using its reciprocal denominator. -/
theorem infinity_lift_poleSlope (a b c : K) :
    liftX E (poleSlope (C a) (C b) (C c) RatFunc.X) =
      -algebraMap K (FunctionField E) b *
          (liftX E RatFunc.X - algebraMap K _ c)⁻¹ ^ 2 -
        2 * algebraMap K _ a * (liftX E RatFunc.X - algebraMap K _ c)⁻¹ ^ 3 := by
  simp only [poleSlope, liftX, map_sub, map_div₀, map_neg, map_mul, map_ofNat, map_pow]
  simp only [div_eq_mul_inv, inv_pow]
  rfl

/-- The regular scaled x-coordinate is exactly the original image divided by source y. -/
theorem infinityScaledX_generic :
    infinityKernelHom E G (infinityScaledX E G) =
      liftX E (xFunction E G) / liftY E E RatFunc.X 1 := by
  simp only [infinityScaledX, map_add, map_mul, map_sum, map_pow, AlgHom.commutes,
    infinityU_generic, infinityV_generic, infinityPoleReciprocal_generic]
  have hx : liftX E (xFunction E G) = liftX E RatFunc.X +
      ∑ c ∈ kernelAbscissae E G,
        liftX E (polePart (C (4 * c ^ 3 + E.b₂ * c ^ 2 + 2 * E.b₄ * c + E.b₆))
          (C (6 * c ^ 2 + E.b₂ * c + E.b₄)) (C c) RatFunc.X) := by
    simp only [xFunction, liftX, map_add, map_sum]
  rw [hx]
  simp only [infinity_lift_polePart]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [← Finset.sum_attach (kernelAbscissae E G)]
  ring

/-- The regular slope is exactly the original generic slope factor. -/
theorem infinitySlope_generic :
    infinityKernelHom E G (infinitySlope E G) = liftX E (slopeFunction E G) := by
  simp only [infinitySlope, map_add, map_one, map_sum, map_sub, map_mul, map_neg,
    map_pow, map_ofNat, AlgHom.commutes, infinityPoleReciprocal_generic]
  have hs : liftX E (slopeFunction E G) = 1 +
      ∑ c ∈ kernelAbscissae E G,
        liftX E (poleSlope (C (4 * c ^ 3 + E.b₂ * c ^ 2 + 2 * E.b₄ * c + E.b₆))
          (C (6 * c ^ 2 + E.b₂ * c + E.b₄)) (C c) RatFunc.X) := by
    simp only [slopeFunction, liftX, map_add, map_one, map_sum]
  rw [hs]
  simp only [infinity_lift_poleSlope]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [← Finset.sum_attach (kernelAbscissae E G)]

end WeierstrassCurve.Velu
