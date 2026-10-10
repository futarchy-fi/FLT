/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryActualNormalizationIso

/-!
# Relabeling retains the original auxiliary equation and coordinates

The existing action on the faithful marking scheme permutes the actual affine
sections. Its pullback on global functions therefore permutes every named
coordinate, over arbitrary coefficient rings including nonreduced rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open AuxiliaryLevel WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (e : MulAut (Labels 4))

/-- An inverse relabeling preserves nonidentity labels. -/
theorem auxiliaryRelabel_ne_one (a : Labels 4) (ha : a ≠ 1) : e.symm a ≠ 1 := by
  intro h
  exact ha (e.symm.injective (h.trans (map_one e.symm).symm))

/-- The original action permutes the original universal marked sections. -/
@[reassoc] theorem auxiliaryAction_mark (a : Labels 4) :
    (auxiliaryAction 4 e).hom ≫ (auxiliaryMarking 4 a).left =
      (auxiliaryMarking 4 (e.symm a)).left := by
  change (faithfulAction universalGroup (Labels 4) e).hom ≫
    (faithfulInclusion universalGroup (Labels 4)).left ≫
      (value universalGroup (Labels 4) a).left = _
  rw [← Category.assoc, faithfulAction_inclusion, Category.assoc]
  have h := congrArg Over.Hom.left (relabelAction_value universalGroup e a)
  change (relabelSchemeAction universalGroup e).hom ≫
    (value universalGroup (Labels 4) a).left = _ at h
  rw [h]
  rfl

/-- Relabeling commutes with the original affine lifts of nonidentity sections. -/
@[reassoc] theorem auxiliaryAction_affine (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryAction 4 e).hom ≫ auxiliaryAffineSection a ha =
      auxiliaryAffineSection (e.symm a) (auxiliaryRelabel_ne_one e a ha) := by
  apply (cancel_mono (integralCurveChart smoothEquation 2)).mp
  rw [Category.assoc, auxiliaryAffineSection_inclusion, auxiliaryAction_mark,
    auxiliaryAffineSection_inclusion]

/-- The action pulls each actual coordinate back to its relabeled coordinate. -/
theorem auxiliaryAction_coordinate (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    (auxiliaryAction 4 e).hom.appTop (auxiliaryCoordinate a ha i) =
      auxiliaryCoordinate (e.symm a) (auxiliaryRelabel_ne_one e a ha) i := by
  change ((Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv ≫
    (auxiliaryAffineSection a ha).appTop ≫ (auxiliaryAction 4 e).hom.appTop)
      (coord smoothEquation 2 i) = _
  rw [← Scheme.Hom.comp_appTop, auxiliaryAction_affine]
  rfl

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

/-- The original affine family retains all coordinate values after relabeling. -/
theorem auxiliaryPointSections_relabel_coordinate (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom) (auxiliaryCoordinate a ha i) =
      auxiliaryPointSections f
        (auxiliaryCoordinate (e.symm a) (auxiliaryRelabel_ne_one e a ha) i) := by
  change (Scheme.ΓSpecIso (.of R)).hom
    ((f ≫ (auxiliaryAction 4 e).hom).appTop (auxiliaryCoordinate a ha i)) = _
  rw [Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (.of R)).hom
    (f.appTop ((auxiliaryAction 4 e).hom.appTop (auxiliaryCoordinate a ha i))) = _
  rw [auxiliaryAction_coordinate]
  rfl

/-- Relabeling leaves the actual coefficient homomorphism unchanged. -/
theorem auxiliaryPointSections_relabel_coefficients :
    auxiliaryCoefficientHom (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom)) =
      auxiliaryCoefficientHom (auxiliaryPointSections f) := by
  have h : auxiliaryCoefficientBase
      (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom)) =
        auxiliaryCoefficientBase (auxiliaryPointSections f) := by
    rw [auxiliaryPointSections_base, auxiliaryPointSections_base, Category.assoc]
    exact congrArg (f ≫ ·) (auxiliaryAction_base 4 e)
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The actual original cubic equation is unchanged by relabeling its sections. -/
theorem auxiliaryPointSections_relabel_equation :
    auxiliaryPullbackEquation (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom)) =
      auxiliaryPullbackEquation (auxiliaryPointSections f) := by
  rw [auxiliaryPullbackEquation_coefficient, auxiliaryPullbackEquation_coefficient,
    auxiliaryPointSections_relabel_coefficients]

end FLT.Mazur.UniversalWeierstrass
