/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineCoordinateFlat
public import FLT.Mazur.WeierstrassProjectiveChartProduct
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Regularity of the difference of the actual affine input coordinates

Base change of the flat affine X projection to the first chart makes the second
X coordinate a flat polynomial variable. Subtracting the first X coordinate is
therefore the image of a monic linear polynomial over the first chart.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Base change of the second affine X projection to the first affine chart. -/
def affineProductPolynomialMap : (Coordinate W 2)[X] →ₐ[R] ChartProduct W 2 2 :=
  (Algebra.TensorProduct.map (AlgHom.id R (Coordinate W 2))
    (aeval (coord W 2 0))).comp (polyEquivTensor R (Coordinate W 2)).toAlgHom

/-- The base changed X projection is flat. -/
theorem affineProductPolynomialMap_flat :
    RingHom.Flat (R := (Coordinate W 2)[X]) (S := ChartProduct W 2 2)
      (affineProductPolynomialMap W).toRingHom := by
  have h : RingHom.Flat (R := Coordinate W 2 ⊗[R] R[X])
      (S := Coordinate W 2 ⊗[R] Coordinate W 2)
      (Algebra.TensorProduct.map (AlgHom.id R (Coordinate W 2))
        (aeval (coord W 2 0))).toRingHom :=
    (RingHom.Flat.of_bijective (f := (AlgHom.id R (Coordinate W 2)).toRingHom)
      Function.bijective_id).tensorProductMap (affineChart_x_flat W)
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (R := (Coordinate W 2)[X])
      (S := Coordinate W 2 ⊗[R] R[X]) (polyEquivTensor R (Coordinate W 2)).bijective) h

/-- The polynomial variable is the second actual affine X coordinate. -/
@[simp] theorem affineProductPolynomialMap_X :
    affineProductPolynomialMap W X = chartProductRight W 2 2 (coord W 2 0) := by
  change (Algebra.TensorProduct.map _ _)
    ((polyEquivTensor R (Coordinate W 2)) X) = 1 ⊗ₜ[R] coord W 2 0
  simp [polyEquivTensor_apply]

/-- Coefficients are the first actual affine input. -/
@[simp] theorem affineProductPolynomialMap_C (a : Coordinate W 2) :
    affineProductPolynomialMap W (C a) = chartProductLeft W 2 2 a := by
  change (Algebra.TensorProduct.map _ _)
    ((polyEquivTensor R (Coordinate W 2)) (C a)) = a ⊗ₜ[R] 1
  simp [polyEquivTensor_apply]

/-- The difference of the two genuine affine X coordinates is regular over any base. -/
theorem affineProduct_x_right_sub_left_regular :
    IsRegular (chartProductRight W 2 2 (coord W 2 0) -
      chartProductLeft W 2 2 (coord W 2 0)) := by
  have h := flatRingHom_isRegular (A := (Coordinate W 2)[X])
    (B := ChartProduct W 2 2) (affineProductPolynomialMap W).toRingHom
    (affineProductPolynomialMap_flat W) (monic_X_sub_C (coord W 2 0)).isRegular
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub,
    affineProductPolynomialMap_X, affineProductPolynomialMap_C] using h

end FLT.Mazur.WeierstrassIntegralChart
