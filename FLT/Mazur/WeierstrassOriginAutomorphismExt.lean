/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineMorphismExt
public import FLT.Mazur.WeierstrassIntegralSeparated
public import FLT.Mazur.WeierstrassOriginAutomorphismCoordinates

/-!
# Coordinate pullback faithfully detects the original automorphism

An origin-preserving automorphism is the identity as soon as its actual
coordinate pullback fixes x and y. Schematic density retains the full
nonreduced base, so no equality is inferred merely from field points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

/-- Fixing the actual x and y functions fixes the whole original affine algebra. -/
theorem originAutCoordinateHom_eq_id
    (hx : originAutCoordinateHom W hΔ e hb hz (coord W 2 0) = coord W 2 0)
    (hy : originAutCoordinateHom W hΔ e hb hz (coord W 2 1) = coord W 2 1) :
    originAutCoordinateHom W hΔ e hb hz = AlgHom.id R (Coordinate W 2) := by
  apply hom_ext
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · change originAutCoordinateHom W hΔ e hb hz (coord W 2 2) = coord W 2 2
    rw [coord_self, map_one]

/-- Identity coordinate pullback makes the actual affine restriction the identity. -/
theorem originAutAffineHom_eq_id
    (hc : originAutCoordinateHom W hΔ e hb hz = AlgHom.id R (Coordinate W 2)) :
    originAutAffineHom W hΔ e hb hz = 𝟙 _ := by
  rw [← originAutCoordinateHom_spec, hc]
  exact Spec.map_id _

/-- Equality of the original two coordinate functions forces identity of the entire scheme map. -/
theorem originAut_eq_id_of_coordinates
    (hx : originAutCoordinateHom W hΔ e hb hz (coord W 2 0) = coord W 2 0)
    (hy : originAutCoordinateHom W hΔ e hb hz (coord W 2 1) = coord W 2 1) :
    e.hom = 𝟙 _ := by
  apply integralCurve_hom_ext_affine W (integralCurveStructure W) _ _
    (by simpa only [Category.id_comp] using hb)
  rw [← originAutAffineHom_inclusion W hΔ e hb hz,
    originAutAffineHom_eq_id W hΔ e hb hz (originAutCoordinateHom_eq_id W hΔ e hb hz hx hy),
    Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassIntegralChart
