/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineVariableChangeMap
public import FLT.Mazur.WeierstrassProjectiveChartProduct
public import FLT.Mazur.WeierstrassIntegralAdditionCharts

/-!
# Admissible changes on the original affine input product

The two original affine substitutions induce the product map. Its secant
denominator is multiplied by a unit square, so the secant open is preserved.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- Apply the actual affine substitution to both universal inputs. -/
def affineProductVariableChange : AffineProduct W →ₐ[R] AffineProduct V :=
  chartProductEvaluation W 2 2
    ((productLeft V).comp (affineVariableChangeMap W V C h))
    ((productRight V).comp (affineVariableChangeMap W V C h))

/-- The product change retains the first affine substitution. -/
theorem affineProductVariableChange_left :
    (affineProductVariableChange W V C h).comp (productLeft W) =
      (productLeft V).comp (affineVariableChangeMap W V C h) :=
  chartProductEvaluation_left W 2 2 _ _

/-- The product change retains the second affine substitution. -/
theorem affineProductVariableChange_right :
    (affineProductVariableChange W V C h).comp (productRight W) =
      (productRight V).comp (affineVariableChangeMap W V C h) :=
  chartProductEvaluation_right W 2 2 _ _

/-- The first X coordinate has the original affine formula. -/
theorem affineProductVariableChange_x₁ :
    affineProductVariableChange W V C h (productX₁ W) =
      algebraMap R _ (C.u : R) ^ 2 * productX₁ V + algebraMap R _ C.r := by
  have he := DFunLike.congr_fun (affineProductVariableChange_left W V C h) (coord W 2 0)
  simpa only [AlgHom.comp_apply, affineVariableChangeMap_x, map_add, map_mul,
    map_pow, AlgHom.commutes, productX₁, productX₂, productY₁, productY₂] using he

/-- The second X coordinate has the original affine formula. -/
theorem affineProductVariableChange_x₂ :
    affineProductVariableChange W V C h (productX₂ W) =
      algebraMap R _ (C.u : R) ^ 2 * productX₂ V + algebraMap R _ C.r := by
  have he := DFunLike.congr_fun (affineProductVariableChange_right W V C h) (coord W 2 0)
  simpa only [AlgHom.comp_apply, affineVariableChangeMap_x, map_add, map_mul,
    map_pow, AlgHom.commutes, productX₁, productX₂, productY₁, productY₂] using he

/-- The first Y coordinate has the original affine formula. -/
theorem affineProductVariableChange_y₁ :
    affineProductVariableChange W V C h (productY₁ W) =
      algebraMap R _ (C.u : R) ^ 3 * productY₁ V +
        algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s * productX₁ V +
        algebraMap R _ C.t := by
  have he := DFunLike.congr_fun (affineProductVariableChange_left W V C h) (coord W 2 1)
  simpa only [AlgHom.comp_apply, affineVariableChangeMap_y, map_add, map_mul,
    map_pow, AlgHom.commutes, productX₁, productX₂, productY₁, productY₂] using he

/-- The second Y coordinate has the original affine formula. -/
theorem affineProductVariableChange_y₂ :
    affineProductVariableChange W V C h (productY₂ W) =
      algebraMap R _ (C.u : R) ^ 3 * productY₂ V +
        algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s * productX₂ V +
        algebraMap R _ C.t := by
  have he := DFunLike.congr_fun (affineProductVariableChange_right W V C h) (coord W 2 1)
  simpa only [AlgHom.comp_apply, affineVariableChangeMap_y, map_add, map_mul,
    map_pow, AlgHom.commutes, productX₁, productX₂, productY₁, productY₂] using he

/-- The actual secant denominator changes by a unit square. -/
theorem affineProductVariableChange_denominator :
    affineProductVariableChange W V C h (secantDenominator W) =
      algebraMap R _ (C.u : R) ^ 2 * secantDenominator V := by
  rw [secantDenominator, map_sub, affineProductVariableChange_x₁,
    affineProductVariableChange_x₂, secantDenominator]
  ring

end FLT.Mazur.WeierstrassIntegralChart
