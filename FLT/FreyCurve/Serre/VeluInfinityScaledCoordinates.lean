/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityPoleReciprocal

/-!
# Scaled original Vélu coordinates regular near infinity

The original x-image divided by source y and the slope factor are finite sums
of regular pole reciprocals. Their values at source infinity are zero and one.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The source homogeneous u coordinate restricted to the explicit neighborhood. -/
def infinityU : InfinityKernelRing E G :=
  algebraMap (InfinityParameterRing E) _ (algebraMap _ _ (coord E 1 0))

/-- The source homogeneous v coordinate restricted to the explicit neighborhood. -/
def infinityV : InfinityKernelRing E G :=
  algebraMap (InfinityParameterRing E) _ (algebraMap _ _ (coord E 1 2))

@[simp] theorem infinityU_value : infinityKernelEvaluation E G (infinityU E G) = 0 := by
  simp [infinityU]

@[simp] theorem infinityV_value : infinityKernelEvaluation E G (infinityV E G) = 0 := by
  simp [infinityV]

/-- The original x-image scaled by source y, expressed in regular functions. -/
def infinityScaledX : InfinityKernelRing E G :=
  infinityU E G + infinityV E G * ∑ c ∈ (kernelAbscissae E G).attach,
    (algebraMap K _ (6 * c.1 ^ 2 + E.b₂ * c.1 + E.b₄) *
        infinityPoleReciprocal E G c.1 c.2 +
      algebraMap K _ (4 * c.1 ^ 3 + E.b₂ * c.1 ^ 2 + 2 * E.b₄ * c.1 + E.b₆) *
        infinityPoleReciprocal E G c.1 c.2 ^ 2)

/-- The original slope factor, expressed in regular functions near infinity. -/
def infinitySlope : InfinityKernelRing E G :=
  1 + ∑ c ∈ (kernelAbscissae E G).attach,
    (-algebraMap K _ (6 * c.1 ^ 2 + E.b₂ * c.1 + E.b₄) *
        infinityPoleReciprocal E G c.1 c.2 ^ 2 -
      2 * algebraMap K _ (4 * c.1 ^ 3 + E.b₂ * c.1 ^ 2 + 2 * E.b₄ * c.1 + E.b₆) *
        infinityPoleReciprocal E G c.1 c.2 ^ 3)

/-- The scaled x-image vanishes at the original infinity point. -/
@[simp] theorem infinityScaledX_value :
    infinityKernelEvaluation E G (infinityScaledX E G) = 0 := by
  simp [infinityScaledX]

/-- The slope has value one at the original infinity point. -/
@[simp] theorem infinitySlope_value :
    infinityKernelEvaluation E G (infinitySlope E G) = 1 := by
  simp [infinitySlope]

variable [CharZero K]

@[simp] theorem infinityU_generic :
    infinityKernelHom E G (infinityU E G) = liftX E RatFunc.X / liftY E E RatFunc.X 1 := by
  simp [infinityU]

@[simp] theorem infinityV_generic :
    infinityKernelHom E G (infinityV E G) = (liftY E E RatFunc.X 1)⁻¹ := by
  simp [infinityV]

end WeierstrassCurve.Velu
