/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityScaledCoordinates

/-!
# The simple zero of the original scaled Vélu abscissa

The scaled target abscissa is the original source parameter times a regular
factor with value one. This explicit factor will define a neighborhood on
which the original identity fiber has no infinitesimal thickening.
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The regular factor of the original scaled target abscissa. -/
def infinityXFactor : InfinityKernelRing E G :=
  1 + algebraMap (InfinityParameterRing E) _ (infinityReciprocal E) *
    ∑ c ∈ (kernelAbscissae E G).attach,
      (algebraMap K _ (6 * c.1 ^ 2 + E.b₂ * c.1 + E.b₄) *
          infinityPoleReciprocal E G c.1 c.2 +
        algebraMap K _ (4 * c.1 ^ 3 + E.b₂ * c.1 ^ 2 + 2 * E.b₄ * c.1 + E.b₆) *
          infinityPoleReciprocal E G c.1 c.2 ^ 2)

/-- The original source v-coordinate remains divisible by u on the kernel neighborhood. -/
theorem infinityV_eq_u_mul :
    infinityV E G = infinityU E G *
      algebraMap (InfinityParameterRing E) _ (infinityReciprocal E) := by
  rw [infinityV, ← infinityReciprocal_relation, map_mul]
  rfl

/-- Exact first-order factorization, before passing to a stalk or completion. -/
theorem infinityScaledX_eq_u_mul :
    infinityScaledX E G = infinityU E G * infinityXFactor E G := by
  rw [infinityScaledX, infinityV_eq_u_mul, infinityXFactor]
  ring

/-- The factor has residue one at the original identity. -/
@[simp] theorem infinityXFactor_value :
    infinityKernelEvaluation E G (infinityXFactor E G) = 1 := by
  simp [infinityXFactor]

/-- Inverting this factor retains the original identity point. -/
theorem infinityXFactor_ne_zero : infinityXFactor E G ≠ 0 := by
  intro h
  have := congrArg (infinityKernelEvaluation E G) h
  simp at this

end WeierstrassCurve.Velu
