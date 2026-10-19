/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluFunctionField
public import FLT.Mazur.WeierstrassAffineNormalForm

/-!
# The original source chart in the quadratic function field

Evaluate the actual affine chart at X and the original uncompleted y-coordinate.
Polynomial normal forms retain both rational components explicitly.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The original generic source coordinates satisfy the source equation. -/
theorem sourceGeneric_equation :
    (E.map (algebraMap K (FunctionField E))).toAffine.Equation
      (liftX E RatFunc.X) (liftY E E RatFunc.X 1) := by
  apply lift_equation
  simpa only [one_pow, mul_one] using cubicFunction_eq E

/-- Evaluate the actual source affine chart in its quadratic field model. -/
def sourceGenericChart : Coordinate E 2 →ₐ[K] FunctionField E :=
  evaluation E 2 ![liftX E RatFunc.X, liftY E E RatFunc.X 1, 1]
    ((Projective.equation_some _ _).mpr (sourceGeneric_equation E)) rfl

/-- The original x-coordinate becomes the rational variable. -/
@[simp] theorem sourceGenericChart_x :
    sourceGenericChart E (coord E 2 0) = liftX E RatFunc.X :=
  evaluation_coord _ _ _ _ _ _

/-- The original y-coordinate becomes the original uncompleted quadratic coordinate. -/
@[simp] theorem sourceGenericChart_y :
    sourceGenericChart E (coord E 2 1) = liftY E E RatFunc.X 1 :=
  evaluation_coord _ _ _ _ _ _

/-- Polynomial functions in x map by the canonical polynomial inclusion. -/
theorem sourceGenericChart_polynomial (p : K[X]) :
    sourceGenericChart E (Polynomial.aeval (coord E 2 0) p) =
      liftX E (algebraMap K[X] K⟮X⟯ p) := by
  have h : (sourceGenericChart E).comp (Polynomial.aeval (coord E 2 0)) =
      (IsScalarTower.toAlgHom K K⟮X⟯ (FunctionField E)).comp
        (IsScalarTower.toAlgHom K K[X] K⟮X⟯) := by
    apply Polynomial.algHom_ext
    simp [liftX, RatFunc.algebraMap_X]
  exact DFunLike.congr_fun h p

/-- Normal forms retain their two original polynomial coefficients. -/
theorem sourceGenericChart_normalForm (p q : K[X]) :
    sourceGenericChart E (affineNormalForm E p q) =
      liftX E (algebraMap K[X] K⟮X⟯ p) +
        liftX E (algebraMap K[X] K⟮X⟯ q) * liftY E E RatFunc.X 1 := by
  simp only [affineNormalForm, map_add, map_mul, sourceGenericChart_polynomial,
    sourceGenericChart_y]

end WeierstrassCurve.Velu
