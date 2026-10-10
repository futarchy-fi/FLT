/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricSectionUnits
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateSections

/-!
# Unit coordinate differences on the actual auxiliary cover

The coordinates are global functions pulled from the original affine marked
sections. Universal faithfulness makes the required horizontal and vertical
differences units over the entire auxiliary scheme, including nilpotents.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

/-- Two nonopposite labels have unit-separated abscissas on the original auxiliary cover. -/
theorem auxiliaryCoordinate_x_sub_isUnit (a b : Labels 4) (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a ≠ b) (hab' : a ≠ b⁻¹) :
    IsUnit (auxiliaryCoordinate a ha 0 - auxiliaryCoordinate b hb 0) := by
  apply GeometricSectionUnits.isUnit_of_geometric
  intro K _ _ p
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ levelFour.hom)
  let _ : Algebra ParameterRing K := r.hom.toAlgebra
  let f : fieldTest K ⟶ levelFour := Over.homMk p hr.symm
  change IsUnit (f.left.appTop _)
  rw [map_sub, auxiliaryCoordinate_field K f, auxiliaryCoordinate_field K f]
  simpa only [map_sub] using
    ((sub_ne_zero.mpr (auxiliaryFieldChart_x_ne K f a ha b hb hab hab')).isUnit).map
      (Scheme.ΓSpecIso (.of K)).inv.hom

/-- An order-four section is separated from its inverse by a unit vertical difference. -/
theorem auxiliaryCoordinate_y_sub_neg_isUnit (a : Labels 4) (ha : a ≠ 1) (han : a ≠ a⁻¹) :
    IsUnit (auxiliaryCoordinate a ha 1 - auxiliarySectionEquation.toAffine.negY
      (auxiliaryCoordinate a ha 0) (auxiliaryCoordinate a ha 1)) := by
  apply GeometricSectionUnits.isUnit_of_geometric
  intro K _ _ p
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ levelFour.hom)
  let _ : Algebra ParameterRing K := r.hom.toAlgebra
  let f : fieldTest K ⟶ levelFour := Over.homMk p hr.symm
  have hn := ((sub_ne_zero.mpr (auxiliaryFieldChart_y_ne_neg K f a ha han)).isUnit).map
    (Scheme.ΓSpecIso (.of K)).inv.hom
  change IsUnit (f.left.appTop _)
  simpa only [Affine.negY, auxiliarySectionEquation, WeierstrassCurve.map,
    map_sub, map_neg, map_mul, auxiliaryCoordinate_field K f,
    auxiliaryCoefficientSections_field K f] using hn

end FLT.Mazur.UniversalWeierstrass
