/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateSections

/-!
# Inverse labels retain the integral coordinate formulas

These are equalities of actual scheme maps and global functions over the
whole auxiliary base, derived from the constructed group inversion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry WeierstrassCurve MonObj

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

/-- Inverse labels agree with the original global curve negation. -/
theorem auxiliaryMarking_inverse_curve (a : Labels 4) :
    (auxiliaryMarking 4 a⁻¹).left =
      (auxiliaryMarking 4 a).left ≫ integralCurveNegation smoothEquation := by
  rw [map_inv]
  rfl

/-- The affine lift of an inverse label is the original integral affine negation. -/
theorem auxiliaryAffineSection_inverse (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryAffineSection a⁻¹ (inv_ne_one.mpr ha) =
      auxiliaryAffineSection a ha ≫
        Spec.map (CommRingCat.ofHom (affineNegation smoothEquation).toRingHom) := by
  apply (cancel_mono (integralCurveChart smoothEquation 2)).mp
  rw [auxiliaryAffineSection_inclusion, Category.assoc,
    ← integralCurveChart_negation_affine, ← Category.assoc, auxiliaryAffineSection_inclusion]
  exact auxiliaryMarking_inverse_curve a

/-- The inverse-label functions come from the actual affine negation algebra map. -/
theorem auxiliaryCoordinateSections_inverse (a : Labels 4) (ha : a ≠ 1)
    (r : Coordinate smoothEquation 2) :
    auxiliaryCoordinateSections a⁻¹ (inv_ne_one.mpr ha) r =
      auxiliaryCoordinateSections a ha (affineNegation smoothEquation r) := by
  change ((Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv ≫
    (auxiliaryAffineSection a⁻¹ (inv_ne_one.mpr ha)).appTop) r = _
  rw [auxiliaryAffineSection_inverse, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Negation fixes the actual global abscissa. -/
theorem auxiliaryCoordinate_inverse_x (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryCoordinate a⁻¹ (inv_ne_one.mpr ha) 0 = auxiliaryCoordinate a ha 0 := by
  exact (auxiliaryCoordinateSections_inverse a ha _).trans
    (congrArg (auxiliaryCoordinateSections a ha) (affineNegation_x smoothEquation))

/-- Negation has the usual integral ordinate formula on the original marked sections. -/
theorem auxiliaryCoordinate_inverse_y (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryCoordinate a⁻¹ (inv_ne_one.mpr ha) 1 =
      auxiliarySectionEquation.toAffine.negY
        (auxiliaryCoordinate a ha 0) (auxiliaryCoordinate a ha 1) := by
  rw [auxiliaryCoordinate, auxiliaryCoordinateSections_inverse a ha, affineNegation_y]
  rw [(auxiliaryCoordinateSections a ha).map_sub,
    (auxiliaryCoordinateSections a ha).map_sub, (auxiliaryCoordinateSections a ha).map_neg,
    (auxiliaryCoordinateSections a ha).map_mul, auxiliaryCoordinateSections_coeff a ha,
    auxiliaryCoordinateSections_coeff a ha]
  rfl

end FLT.Mazur.UniversalWeierstrass
