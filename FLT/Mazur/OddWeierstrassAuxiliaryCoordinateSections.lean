/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryFieldCoordinates

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

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)

open WeierstrassIntegralChart

/-- Global functions on the original auxiliary cover. -/
abbrev AuxiliarySectionRing := Γ(levelThree.left, ⊤)

/-- The coefficient map on global functions of the auxiliary cover. -/
def auxiliaryCoefficientSections : OddChartRing →+* AuxiliarySectionRing :=
  levelThree.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of OddChartRing)).inv.hom

/-- The original marked affine chart induces its actual map on global functions. -/
def auxiliaryCoordinateSections (a : Labels 3) (ha : a ≠ 1) :
    Coordinate oddChartEquation 2 →+* AuxiliarySectionRing :=
  (auxiliaryAffineSection a ha).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Coordinate oddChartEquation 2))).inv.hom

/-- The affine coordinate map retains the original coefficient functions. -/
theorem auxiliaryCoordinateSections_coeff (a : Labels 3) (ha : a ≠ 1) (r : OddChartRing) :
    auxiliaryCoordinateSections a ha (algebraMap OddChartRing _ r) =
      auxiliaryCoefficientSections r := by
  change ((CommRingCat.ofHom (algebraMap OddChartRing (Coordinate oddChartEquation 2)) ≫
    (Scheme.ΓSpecIso (.of (Coordinate oddChartEquation 2))).inv) ≫
      (auxiliaryAffineSection a ha).appTop) r = _
  rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso (.of OddChartRing)).inv ≫
    (auxiliaryAffineSection a ha ≫ chartStructure oddChartEquation 2).appTop) r = _
  rw [auxiliaryAffineSection_base]
  rfl

/-- The coordinate functions of the original affine lift, including its normalized Z coordinate. -/
def auxiliaryCoordinate (a : Labels 3) (ha : a ≠ 1) (i : Fin 3) : AuxiliarySectionRing :=
  auxiliaryCoordinateSections a ha (coord oddChartEquation 2 i)

/-- The equation with coefficients in global functions of the original auxiliary cover. -/
def auxiliarySectionEquation : WeierstrassCurve AuxiliarySectionRing :=
  oddChartEquation.map auxiliaryCoefficientSections

variable (K : Type) [Field K] [Algebra OddChartRing K] (f : fieldTest K ⟶ levelThree)

/-- Coefficient pullback is the original field coefficient map. -/
theorem auxiliaryCoefficientSections_field (r : OddChartRing) :
    f.left.appTop (auxiliaryCoefficientSections r) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap OddChartRing K r) := by
  have hn := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap OddChartRing K))
  change ((Scheme.ΓSpecIso (.of OddChartRing)).inv ≫
    levelThree.hom.appTop ≫ f.left.appTop) r = _
  rw [← Scheme.Hom.comp_appTop, f.w]
  exact congrArg (fun k : CommRingCat.of OddChartRing ⟶ Γ(Spec (.of K), ⊤) ↦ k r) hn.symm

/-- Pulling back global coordinate functions gives the actual field chart algebra map. -/
theorem auxiliaryCoordinateSections_field (a : Labels 3) (ha : a ≠ 1)
    (r : Coordinate oddChartEquation 2) :
    f.left.appTop (auxiliaryCoordinateSections a ha r) =
      (Scheme.ΓSpecIso (.of K)).inv (auxiliaryFieldChart K f a ha r) := by
  change ((Scheme.ΓSpecIso (.of (Coordinate oddChartEquation 2))).inv ≫
    (auxiliaryAffineSection a ha).appTop ≫ f.left.appTop) r = _
  rw [← Scheme.Hom.comp_appTop, ← auxiliaryFieldChart_spec K f a ha,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Every coordinate retains its scheme-level origin after a field specialization. -/
theorem auxiliaryCoordinate_field (a : Labels 3) (ha : a ≠ 1) (i : Fin 3) :
    f.left.appTop (auxiliaryCoordinate a ha i) =
      (Scheme.ΓSpecIso (.of K)).inv (auxiliaryFieldChart K f a ha (coord oddChartEquation 2 i)) :=
  auxiliaryCoordinateSections_field K f a ha _

end FLT.Mazur.OddWeierstrassParameter
