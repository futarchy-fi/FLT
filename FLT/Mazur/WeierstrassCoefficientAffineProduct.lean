/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientMap
public import FLT.Mazur.WeierstrassIntegralAdditionCharts

/-!
# Coefficient extension on the actual affine input product

Both universal inputs retain their coordinates under arbitrary coefficient
extension. In particular, the secant denominator is preserved exactly.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

open scoped TensorProduct

instance affineProductScalarAlgebra (V : WeierstrassCurve S) : Algebra R (AffineProduct V) :=
  inferInstanceAs (Algebra R (Coordinate V 2 ⊗[S] Coordinate V 2))

instance affineProductScalarTower (V : WeierstrassCurve S) :
    IsScalarTower R S (AffineProduct V) :=
  inferInstanceAs (IsScalarTower R S (Coordinate V 2 ⊗[S] Coordinate V 2))

/-- Extend the coefficients of both actual affine inputs. -/
def affineProductCoefficientMap :
    AffineProduct W →ₐ[R] AffineProduct (W.map (algebraMap R S)) :=
  chartProductEvaluation W 2 2
    (((productLeft (W.map (algebraMap R S))).restrictScalars R).comp
      (chartCoefficientMap W 2))
    (((productRight (W.map (algebraMap R S))).restrictScalars R).comp
      (chartCoefficientMap W 2))

/-- The coefficient map retains the first input. -/
theorem affineProductCoefficientMap_left :
    (affineProductCoefficientMap (S := S) W).comp (productLeft W) =
      ((productLeft (W.map (algebraMap R S))).restrictScalars R).comp
        (chartCoefficientMap W 2) :=
  chartProductEvaluation_left W 2 2 _ _

/-- The coefficient map retains the second input. -/
theorem affineProductCoefficientMap_right :
    (affineProductCoefficientMap (S := S) W).comp (productRight W) =
      ((productRight (W.map (algebraMap R S))).restrictScalars R).comp
        (chartCoefficientMap W 2) :=
  chartProductEvaluation_right W 2 2 _ _

/-- The original x₁ coordinate survives coefficient extension. -/
@[simp] theorem affineProductCoefficientMap_x₁ :
    affineProductCoefficientMap (S := S) W (productX₁ W) =
      productX₁ (W.map (algebraMap R S)) := by
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
    productX₁, productX₂, productY₁, productY₂] using
    DFunLike.congr_fun (affineProductCoefficientMap_left (S := S) W) (coord W 2 0)

/-- The original x₂ coordinate survives coefficient extension. -/
@[simp] theorem affineProductCoefficientMap_x₂ :
    affineProductCoefficientMap (S := S) W (productX₂ W) =
      productX₂ (W.map (algebraMap R S)) := by
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
    productX₁, productX₂, productY₁, productY₂] using
    DFunLike.congr_fun (affineProductCoefficientMap_right (S := S) W) (coord W 2 0)

/-- The original y₁ coordinate survives coefficient extension. -/
@[simp] theorem affineProductCoefficientMap_y₁ :
    affineProductCoefficientMap (S := S) W (productY₁ W) =
      productY₁ (W.map (algebraMap R S)) := by
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
    productX₁, productX₂, productY₁, productY₂] using
    DFunLike.congr_fun (affineProductCoefficientMap_left (S := S) W) (coord W 2 1)

/-- The original y₂ coordinate survives coefficient extension. -/
@[simp] theorem affineProductCoefficientMap_y₂ :
    affineProductCoefficientMap (S := S) W (productY₂ W) =
      productY₂ (W.map (algebraMap R S)) := by
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
    productX₁, productX₂, productY₁, productY₂] using
    DFunLike.congr_fun (affineProductCoefficientMap_right (S := S) W) (coord W 2 1)

/-- The actual secant denominator survives arbitrary coefficient extension. -/
@[simp] theorem affineProductCoefficientMap_denominator :
    affineProductCoefficientMap (S := S) W (secantDenominator W) =
      secantDenominator (W.map (algebraMap R S)) := by
  rw [secantDenominator, map_sub, affineProductCoefficientMap_x₁,
    affineProductCoefficientMap_x₂, secantDenominator]

end FLT.Mazur.WeierstrassIntegralChart
