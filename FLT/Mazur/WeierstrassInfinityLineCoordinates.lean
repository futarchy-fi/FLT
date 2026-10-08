/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Compact line coordinates for the infinity law

Keep the leading and quadratic line coefficients explicit. This gives short
homogeneous formulas and a normalized collinearity identity for the negated
sum, without cancelling an input difference or assuming a field.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Leading coefficient of the cubic on a line of slope dz/dx. -/
def infinityLineLeading (m : R) : R :=
  -1 - W.a₂ * m - W.a₄ * m ^ 2 - W.a₆ * m ^ 3

/-- Quadratic coefficient of the same cubic through the first Y-chart input. -/
def infinityLineQuadratic (x z m : R) : R :=
  W.a₁ * m + W.a₃ * m ^ 2 - 3 * x - W.a₂ * (z + 2 * x * m) -
    W.a₄ * (x * m ^ 2 + 2 * m * z) - 3 * W.a₆ * m ^ 2 * z

/-- The direction vector evaluates to the displayed leading coefficient. -/
theorem infinityLineLeading_eq (m : R) :
    MvPolynomial.eval ![1, 0, m] W.toProjective.polynomial = infinityLineLeading W m := by
  simp only [Projective.eval_polynomial, Projective.fin3_def_ext, infinityLineLeading]
  ring

/-- Polarization evaluates to the displayed quadratic coefficient. -/
theorem infinityLineQuadratic_eq (x z m : R) :
    cubicPolar W ![1, 0, m] ![x, 1, z] = infinityLineQuadratic W x z m := by
  simp only [cubicPolar, Projective.fin3_def_ext, infinityLineQuadratic]
  ring

/-- The homogeneous X-coordinate is Vieta's third root with its leading coefficient. -/
theorem infinityAdditionXYZ_x (x₁ x₂ z m : R) :
    infinityAdditionXYZ W x₁ x₂ z m 0 =
      infinityLineLeading W m * (2 * x₁ - x₂) - infinityLineQuadratic W x₁ z m := by
  simp only [infinityAdditionXYZ, lineThird, Projective.fin3_def_ext,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, infinityLineLeading_eq,
    infinityLineQuadratic_eq]
  ring

/-- The homogeneous Z-coordinate retains the original line intercept. -/
theorem infinityAdditionXYZ_line (x₁ x₂ z m : R) :
    infinityAdditionXYZ W x₁ x₂ z m 2 - m * infinityAdditionXYZ W x₁ x₂ z m 0 =
      infinityLineLeading W m * (z - m * x₁) := by
  simp only [infinityAdditionXYZ, lineThird, Projective.fin3_def_ext,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, infinityLineLeading_eq]
  ring

/-- Negating the homogeneous output recovers the leading line coefficient as Y. -/
theorem infinityAdditionXYZ_negY (x₁ x₂ z m : R) :
    -infinityAdditionXYZ W x₁ x₂ z m 1 -
        W.a₁ * infinityAdditionXYZ W x₁ x₂ z m 0 -
        W.a₃ * infinityAdditionXYZ W x₁ x₂ z m 2 = infinityLineLeading W m := by
  simp only [infinityAdditionXYZ, Projective.negY, lineThird, Projective.fin3_def_ext,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, infinityLineLeading_eq]
  ring

/-- Homogeneous collinearity of the two inputs and the negated output. -/
theorem infinityAdditionXYZ_collinear (x₁ x₂ z m : R) :
    (1 + W.a₃ * (z - m * x₁)) * infinityAdditionXYZ W x₁ x₂ z m 2 +
        (W.a₁ * (z - m * x₁) - m) * infinityAdditionXYZ W x₁ x₂ z m 0 +
        (z - m * x₁) * infinityAdditionXYZ W x₁ x₂ z m 1 = 0 := by
  linear_combination infinityAdditionXYZ_line W x₁ x₂ z m -
    (z - m * x₁) * infinityAdditionXYZ_negY W x₁ x₂ z m

/-- The normalized negated sum stays on the original line over every commutative ring. -/
theorem infinityAdditionXYZ_normalized_line {x₁ x₂ z m x' z' : R}
    (hu : IsUnit (infinityAdditionXYZ W x₁ x₂ z m 1))
    (hx : x' * infinityAdditionXYZ W x₁ x₂ z m 1 = infinityAdditionXYZ W x₁ x₂ z m 0)
    (hz : z' * infinityAdditionXYZ W x₁ x₂ z m 1 = infinityAdditionXYZ W x₁ x₂ z m 2) :
    (1 + W.a₃ * (z - m * x₁)) * z' + (W.a₁ * (z - m * x₁) - m) * x' +
      (z - m * x₁) = 0 := by
  apply hu.mul_left_inj.mp
  linear_combination (1 + W.a₃ * (z - m * x₁)) * hz +
    (W.a₁ * (z - m * x₁) - m) * hx + infinityAdditionXYZ_collinear W x₁ x₂ z m

end FLT.Mazur.WeierstrassIntegralChart
