/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Identity formulas throughout the infinity addition neighborhood

When one input is infinity, the divided-difference relations imply that the
homogeneous output is proportional to the other input. No coordinate or
difference is cancelled, so these equations hold over arbitrary rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity law with zero on the left has the other input's projective coordinates. -/
theorem infinityAdditionXYZ_left_identity {x z m : R}
    (hl : m * x = z)
    (hc : m * infinitySlopeDenominator W x 0 z = infinitySlopeNumerator W 0 x 0)
    (i : Fin 3) :
    infinityAdditionXYZ W 0 x 0 m i =
      ![x, 1, z] i * infinityAdditionXYZ W 0 x 0 m 1 := by
  subst z
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator] at hc
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.eval_polynomial,
      Projective.negY]
  · linear_combination -(W.a₁ + W.a₃ * m) * hc
  · linear_combination -m * (W.a₁ + W.a₃ * m) * hc

/-- The same integral identity holds with zero on the right. -/
theorem infinityAdditionXYZ_right_identity {x z m : R}
    (hl : m * x = z)
    (hc : m * infinitySlopeDenominator W 0 z 0 = infinitySlopeNumerator W x 0 z)
    (i : Fin 3) :
    infinityAdditionXYZ W x 0 z m i =
      ![x, 1, z] i * infinityAdditionXYZ W x 0 z m 1 := by
  subst z
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator] at hc
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.eval_polynomial,
      Projective.negY]
  · linear_combination -(W.a₁ + W.a₃ * m) * hc
  · linear_combination -m * (W.a₁ + W.a₃ * m) * hc

end FLT.Mazur.WeierstrassIntegralChart
