/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AffineRationalGroupSection
public import FLT.Mazur.WeierstrassCoefficientZero

/-!
# Explicit affine sections under coefficient projection

The original affine-point group section has its original normalized coordinates.
These formulas retain the actual scheme morphism under coefficient extension.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- An original affine section is the evaluation of its original homogeneous coordinates. -/
theorem affineRationalGroupSection_some (x y : K) (h : W.toAffine.Nonsingular x y) :
    ((affineRationalGroupSectionAddHom W (.some x y h)).toMul).left =
      Spec.map (CommRingCat.ofHom
        (evaluation W 2 ![x, y, 1] ((WeierstrassCurve.Projective.equation_some x y).mpr
          h.left) rfl).toRingHom) ≫ integralCurveChart W 2 := by
  change 𝟙 _ ≫ (projectiveToIntegral W
    (WeierstrassCurve.Projective.Point.fromAffine (.some x y h))).left = _
  rw [Category.id_comp]
  exact projectiveToIntegral_chart W _ 2 ![x, y, 1]
    ((WeierstrassCurve.Projective.equation_some x y).mpr h.left) rfl rfl

/-- The original zero point is exactly the actual zero section. -/
theorem affineRationalGroupSection_zero :
    ((affineRationalGroupSectionAddHom W 0).toMul).left = integralCurveZero W := by
  change 𝟙 _ ≫ (projectiveToIntegral W 0).left = _
  rw [Category.id_comp, projectiveToIntegral_zero]
  change Spec.map (𝟙 (CommRingCat.of K)) ≫ _ = _
  rw [Spec.map_id, Category.id_comp]

end FLT.Mazur.WeierstrassIntegralChart
