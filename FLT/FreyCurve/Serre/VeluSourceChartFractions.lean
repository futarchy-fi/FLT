/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceChartInjective

/-!
# Clearing denominators in the original source chart

Every quadratic field element is a rational linear combination of 1 and the
original y-coordinate. Clearing the two rational denominators writes it as a
quotient of actual affine chart functions.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The original y-coordinate and 1 span the quadratic model over the rational x-line. -/
theorem sourceGeneric_rational_normalForm (z : FunctionField E) :
    ∃ f g : K⟮X⟯, z = liftX E f + liftX E g * liftY E E RatFunc.X 1 := by
  refine ⟨z.re + z.im * (C E.a₁ * RatFunc.X + C E.a₃), 2 * z.im, ?_⟩
  apply QuadraticAlgebra.ext
  all_goals simp [liftX, liftY]; ring

/-- Clearing both denominators gives a quotient of original polynomial normal forms. -/
theorem sourceGeneric_rational_quotient (f g : K⟮X⟯) :
    liftX E f + liftX E g * liftY E E RatFunc.X 1 =
      sourceGenericChart E
        (affineNormalForm E (f.num * g.denom) (g.num * f.denom)) /
      sourceGenericChart E (Polynomial.aeval (coord E 2 0) (f.denom * g.denom)) := by
  rw [sourceGenericChart_normalForm, sourceGenericChart_polynomial]
  simp only [map_mul, liftX, map_mul]
  have hf : algebraMap K[X] (FunctionField E) f.denom ≠ 0 :=
    (IsScalarTower.toAlgHom K[X] K⟮X⟯ (FunctionField E)).injective.ne
      (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
  have hg : algebraMap K[X] (FunctionField E) g.denom ≠ 0 :=
    (IsScalarTower.toAlgHom K[X] K⟮X⟯ (FunctionField E)).injective.ne
      (RatFunc.algebraMap_ne_zero g.denom_ne_zero)
  have h (a : K⟮X⟯) : algebraMap K⟮X⟯ (FunctionField E) a =
      algebraMap K[X] (FunctionField E) a.num /
        algebraMap K[X] (FunctionField E) a.denom := by
    simpa only [map_div₀, ← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ (FunctionField E)]
      using congrArg (algebraMap K⟮X⟯ (FunctionField E)) a.num_div_denom.symm
  rw [h f, h g]
  simp only [← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ (FunctionField E)]
  field_simp

/-- Every element of the quadratic model is a fraction of actual affine functions. -/
theorem sourceGenericChart_fraction_surjective (z : FunctionField E) :
    ∃ a b : Coordinate E 2, z = sourceGenericChart E a / sourceGenericChart E b := by
  obtain ⟨f, g, rfl⟩ := sourceGeneric_rational_normalForm E z
  exact ⟨_, _, sourceGeneric_rational_quotient E f g⟩

end WeierstrassCurve.Velu
