/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassTriangularRelation

/-!
# The original affine coordinates determine the Weierstrass equation

If the universal affine point satisfies a second monic Weierstrass equation,
normal-form uniqueness identifies all five coefficients integrally.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)

/-- A second equation on the same universal affine coordinates equals the original. -/
theorem affineEquation_curve_eq
    (h : (V.map (algebraMap R (Coordinate W 2))).toAffine.Equation
      (coord W 2 0) (coord W 2 1)) : V = W := by
  let f : Coordinate V 2 →ₐ[R] Coordinate W 2 := evaluation V 2
    ![coord W 2 0, coord W 2 1, 1] ((Projective.equation_some ..).mpr h) rfl
  have hx : f (coord V 2 0) = coord W 2 0 := evaluation_coord ..
  have hy : f (coord V 2 1) = coord W 2 1 := evaluation_coord ..
  have he := triangular_coordinate_relations W V f 0 1 0 0 1
    (by simpa using hx) (by simpa using hy)
  simp only [mul_zero, one_mul, mul_one, one_pow, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), add_zero, zero_add, sub_zero] at he
  ext
  · linear_combination he.2.1
  · linear_combination -he.2.2.2.1
  · linear_combination he.2.2.1
  · linear_combination -he.2.2.2.2.1
  · linear_combination -he.2.2.2.2.2

end FLT.Mazur.WeierstrassIntegralChart
