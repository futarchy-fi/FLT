/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# The infinity addition formula on a point and its normalized negation

The normalized negation has coordinates (u x, 1, u z). On the open where
1 + u + u² is invertible, the divided-difference formula has zero X and Z
coordinates. This extra open contains the entire zero section, since u = -1 there.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity slope on the negation pair is the slope of the line through zero. -/
theorem infinityNegationSlope_mul_x {x z u m : R}
    (hP : W.toProjective.Equation ![x, 1, z])
    (hn : u * (-1 - W.a₁ * x - W.a₃ * z) = 1)
    (hu : IsUnit (infinitySlopeDenominator W (u * x) z (u * z)))
    (hc : m * infinitySlopeDenominator W (u * x) z (u * z) =
      infinitySlopeNumerator W x (u * x) z) : m * x = z := by
  apply hu.mul_left_inj.mp
  rw [Projective.equation_iff] at hP
  simp only [Projective.fin3_def_ext] at hP
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator] at hc ⊢
  linear_combination x * hc - (1 + u + u ^ 2) * hP - u * z * hn

/-- The divided quadratic relation vanishes on a neighborhood of the inverse pair. -/
theorem infinityNegationSlope_cubic {x z u m : R}
    (hl : m * x = z)
    (hn : u * (-1 - W.a₁ * x - W.a₃ * z) = 1)
    (hu : IsUnit (1 + u + u ^ 2))
    (hc : m * infinitySlopeDenominator W (u * x) z (u * z) =
      infinitySlopeNumerator W x (u * x) z) :
    m + u * (1 + W.a₂ * m + W.a₄ * m ^ 2 + W.a₆ * m ^ 3) * x ^ 2 = 0 := by
  subst z
  apply hu.mul_left_inj.mp
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator] at hc
  linear_combination -u * hc - m * (1 + u) * hn

/-- The homogeneous infinity output on the inverse pair is proportional to zero. -/
theorem infinityAdditionXYZ_negation {x z u m : R}
    (hl : m * x = z)
    (hn : u * (-1 - W.a₁ * x - W.a₃ * z) = 1)
    (hu : IsUnit (1 + u + u ^ 2))
    (hc : m * infinitySlopeDenominator W (u * x) z (u * z) =
      infinitySlopeNumerator W x (u * x) z) (i : Fin 3) :
    infinityAdditionXYZ W x (u * x) z m i =
      ![0, 1, 0] i * infinityAdditionXYZ W x (u * x) z m 1 := by
  have hk := infinityNegationSlope_cubic W hl hn hu hc
  subst z
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.eval_polynomial,
      Projective.negY]
  · linear_combination -(W.a₁ + W.a₃ * m) * hk -
      (1 + W.a₂ * m + W.a₄ * m ^ 2 + W.a₆ * m ^ 3) * x * hn
  · linear_combination -m * (W.a₁ + W.a₃ * m) * hk -
      m * (1 + W.a₂ * m + W.a₄ * m ^ 2 + W.a₆ * m ^ 3) * x * hn

end FLT.Mazur.WeierstrassIntegralChart
