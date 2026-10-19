/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceChart

/-!
# Faithfulness of the original source chart evaluation

The quadratic component detects the y coefficient of a polynomial normal form.
The real component then detects its remaining x polynomial.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The quadratic component reads off half the original y coefficient. -/
theorem sourceGenericChart_normalForm_im (p q : K[X]) :
    (sourceGenericChart E (affineNormalForm E p q)).im =
      algebraMap K[X] K⟮X⟯ q / 2 := by
  rw [sourceGenericChart_normalForm]
  simp [liftX, liftY, div_eq_mul_inv]

/-- The real component records the completed-square correction. -/
theorem sourceGenericChart_normalForm_re (p q : K[X]) :
    (sourceGenericChart E (affineNormalForm E p q)).re =
      algebraMap K[X] K⟮X⟯ p + algebraMap K[X] K⟮X⟯ q *
        ((-C E.a₁ * RatFunc.X - C E.a₃) / 2) := by
  rw [sourceGenericChart_normalForm]
  simp [liftX, liftY]

/-- Evaluating the actual affine chart in the quadratic field loses no functions. -/
theorem sourceGenericChart_injective : Function.Injective (sourceGenericChart E) := by
  apply (injective_iff_map_eq_zero (sourceGenericChart E)).mpr
  intro a ha
  obtain ⟨p, q, rfl⟩ := exists_affineNormalForm E a
  have hi := congrArg QuadraticAlgebra.im ha
  rw [sourceGenericChart_normalForm_im] at hi
  have hq : q = 0 := (RatFunc.algebraMap_injective K) <| by
    simpa using (div_eq_zero_iff.mp hi).resolve_right (by norm_num)
  have hr := congrArg QuadraticAlgebra.re ha
  rw [sourceGenericChart_normalForm_re, hq, map_zero, zero_mul, add_zero] at hr
  have hp : p = 0 := (RatFunc.algebraMap_injective K) (by simpa using hr)
  exact (affineNormalForm_eq_zero E p q).mpr ⟨hp, hq⟩

end WeierstrassCurve.Velu
