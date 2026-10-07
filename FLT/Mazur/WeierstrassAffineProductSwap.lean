/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInputSwap
public import FLT.Mazur.WeierstrassVerticalAdditionCharts

/-!
# Input interchange on the affine product and its slope denominators

The secant differences change sign. The tangent denominator and numerator
acquire explicit multiples of the two differences, accounting for the
asymmetry of their chosen divided-difference presentations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The concrete tensor interchange on the original affine input algebra. -/
def affineProductSwap : AffineProduct W →ₐ[R] AffineProduct W := chartProductSwap W 2 2

/-- First x-coordinate after input interchange. -/
@[simp] theorem affineProductSwap_x₁ : affineProductSwap W (productX₁ W) = productX₂ W :=
  DFunLike.congr_fun (chartProductSwap_left W 2 2) (coord W 2 0)

/-- Second x-coordinate after input interchange. -/
@[simp] theorem affineProductSwap_x₂ : affineProductSwap W (productX₂ W) = productX₁ W :=
  DFunLike.congr_fun (chartProductSwap_right W 2 2) (coord W 2 0)

/-- First y-coordinate after input interchange. -/
@[simp] theorem affineProductSwap_y₁ : affineProductSwap W (productY₁ W) = productY₂ W :=
  DFunLike.congr_fun (chartProductSwap_left W 2 2) (coord W 2 1)

/-- Second y-coordinate after input interchange. -/
@[simp] theorem affineProductSwap_y₂ : affineProductSwap W (productY₂ W) = productY₁ W :=
  DFunLike.congr_fun (chartProductSwap_right W 2 2) (coord W 2 1)

/-- The affine input interchange is involutive. -/
theorem affineProductSwap_swap :
    (affineProductSwap W).comp (affineProductSwap W) = AlgHom.id R _ :=
  chartProductSwap_swap W 2 2

/-- The ordinary secant denominator changes sign. -/
theorem affineProductSwap_secantDenominator :
    affineProductSwap W (secantDenominator W) = -secantDenominator W := by
  simp only [secantDenominator, map_sub, affineProductSwap_x₁, affineProductSwap_x₂]
  ring

/-- The reciprocal secant denominator changes sign. -/
theorem affineProductSwap_verticalSecantDenominator :
    affineProductSwap W (verticalSecantDenominator W) = -verticalSecantDenominator W := by
  simp only [verticalSecantDenominator, map_sub, affineProductSwap_y₁, affineProductSwap_y₂]
  ring

/-- The tangent denominator changes by a multiple of the secant difference. -/
theorem affineProductSwap_tangentDenominator :
    affineProductSwap W (tangentDenominator W) =
      tangentDenominator W + algebraMap R (AffineProduct W) W.a₁ * secantDenominator W := by
  simp only [tangentDenominator, secantDenominator, map_add, map_mul, AlgHom.commutes,
    affineProductSwap_y₁, affineProductSwap_y₂, affineProductSwap_x₂]
  ring

/-- The tangent numerator changes by the corresponding reciprocal secant difference. -/
theorem affineProductSwap_tangentNumerator :
    affineProductSwap W (tangentNumerator W) = tangentNumerator W +
      algebraMap R (AffineProduct W) W.a₁ * verticalSecantDenominator W := by
  simp only [tangentNumerator, verticalSecantDenominator, map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes, affineProductSwap_x₁, affineProductSwap_x₂, affineProductSwap_y₁]
  ring

end FLT.Mazur.WeierstrassIntegralChart
