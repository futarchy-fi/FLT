/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryFieldCoordinates

/-!
# Global coordinates of the actual auxiliary marked sections

The affine lifts supply functions on the whole auxiliary base. Their
pullbacks to every coefficient-field test are the previously computed chart
coordinates. No reduction of the auxiliary base is involved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

/-- Global functions on the original auxiliary cover. -/
abbrev AuxiliarySectionRing := Γ(levelFour.left, ⊤)

/-- The coefficient map on global functions of the auxiliary cover. -/
def auxiliaryCoefficientSections : ParameterRing →+* AuxiliarySectionRing :=
  levelFour.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of ParameterRing)).inv.hom

/-- The original marked affine chart induces its actual map on global functions. -/
def auxiliaryCoordinateSections (a : Labels 4) (ha : a ≠ 1) :
    Coordinate smoothEquation 2 →+* AuxiliarySectionRing :=
  (auxiliaryAffineSection a ha).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv.hom

/-- The affine coordinate map retains the original coefficient functions. -/
theorem auxiliaryCoordinateSections_coeff (a : Labels 4) (ha : a ≠ 1) (r : ParameterRing) :
    auxiliaryCoordinateSections a ha (algebraMap ParameterRing _ r) =
      auxiliaryCoefficientSections r := by
  change ((CommRingCat.ofHom (algebraMap ParameterRing (Coordinate smoothEquation 2)) ≫
    (Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv) ≫
      (auxiliaryAffineSection a ha).appTop) r = _
  rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso (.of ParameterRing)).inv ≫
    (auxiliaryAffineSection a ha ≫ chartStructure smoothEquation 2).appTop) r = _
  rw [auxiliaryAffineSection_base]
  rfl

/-- The coordinate functions of the original affine lift, including its normalized Z coordinate. -/
def auxiliaryCoordinate (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) : AuxiliarySectionRing :=
  auxiliaryCoordinateSections a ha (coord smoothEquation 2 i)

/-- The equation with coefficients in global functions of the original auxiliary cover. -/
def auxiliarySectionEquation : WeierstrassCurve AuxiliarySectionRing :=
  smoothEquation.map auxiliaryCoefficientSections

variable (K : Type) [Field K] [Algebra ParameterRing K] (f : fieldTest K ⟶ levelFour)

/-- Coefficient pullback is the original field coefficient map. -/
theorem auxiliaryCoefficientSections_field (r : ParameterRing) :
    f.left.appTop (auxiliaryCoefficientSections r) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap ParameterRing K r) := by
  have hn := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap ParameterRing K))
  change ((Scheme.ΓSpecIso (.of ParameterRing)).inv ≫
    levelFour.hom.appTop ≫ f.left.appTop) r = _
  rw [← Scheme.Hom.comp_appTop, f.w]
  exact congrArg (fun k : CommRingCat.of ParameterRing ⟶ Γ(Spec (.of K), ⊤) ↦ k r) hn.symm

/-- Pulling back global coordinate functions gives the actual field chart algebra map. -/
theorem auxiliaryCoordinateSections_field (a : Labels 4) (ha : a ≠ 1)
    (r : Coordinate smoothEquation 2) :
    f.left.appTop (auxiliaryCoordinateSections a ha r) =
      (Scheme.ΓSpecIso (.of K)).inv (auxiliaryFieldChart K f a ha r) := by
  change ((Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv ≫
    (auxiliaryAffineSection a ha).appTop ≫ f.left.appTop) r = _
  rw [← Scheme.Hom.comp_appTop, ← auxiliaryFieldChart_spec K f a ha,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Every coordinate retains its scheme-level origin after a field specialization. -/
theorem auxiliaryCoordinate_field (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    f.left.appTop (auxiliaryCoordinate a ha i) =
      (Scheme.ΓSpecIso (.of K)).inv (auxiliaryFieldChart K f a ha (coord smoothEquation 2 i)) :=
  auxiliaryCoordinateSections_field K f a ha _

end FLT.Mazur.UniversalWeierstrass
