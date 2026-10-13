/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedMarking

/-!
# The original coefficient parameter of an actual affine auxiliary family

An actual auxiliary morphism supplies its map on global functions and the
original coefficient morphism. This constructs the relative auxiliary point
without assuming the auxiliary scheme is affine.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (OddChartRing)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelThree.left)

/-- Pull back original auxiliary functions along the actual family. -/
def auxiliaryPointSections : AuxiliarySectionRing →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp f.appTop.hom

/-- The global-functions map retains the actual original auxiliary morphism. -/
theorem auxiliaryPointSections_spec :
    Spec.map (CommRingCat.ofHom (auxiliaryPointSections f)) = f ≫ levelThree.left.toSpecΓ := by
  change Spec.map (f.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom) = _
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom]
  exact (Scheme.toSpecΓ_naturality f).symm

/-- Its coefficient map is exactly the parameter of the original auxiliary family. -/
theorem auxiliaryPointSections_base :
    auxiliaryCoefficientBase (auxiliaryPointSections f) = f ≫ levelThree.hom := by
  change Spec.map ((Scheme.ΓSpecIso (.of OddChartRing)).inv ≫
    levelThree.hom.appTop ≫ f.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom) = _
  rw [← Category.assoc levelThree.hom.appTop f.appTop,
    ← Scheme.Hom.comp_appTop, Spec.map_comp, Spec.map_comp,
    SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality,
    Category.assoc]
  change (f ≫ levelThree.hom) ≫ (Spec (.of OddChartRing)).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (.of OddChartRing)).inv = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
  exact Category.comp_id _

/-- The original auxiliary morphism as a relative point over its actual coefficient map. -/
def auxiliaryRelativePoint :
    (Over.map (auxiliaryCoefficientBase (auxiliaryPointSections f))).obj
      (𝟙_ (Over (Spec (.of R)))) ⟶ levelThree :=
  Over.homMk f (by
    change f ≫ levelThree.hom = 𝟙 _ ≫ auxiliaryCoefficientBase (auxiliaryPointSections f)
    rw [Category.id_comp, auxiliaryPointSections_base])

/-- The relative point retains the actual original auxiliary morphism. -/
theorem auxiliaryRelativePoint_left : (auxiliaryRelativePoint f).left = f := rfl

/-- An actual affine auxiliary family determines its normalized odd level point. -/
irreducible_def auxiliaryFamilyNormalizedPoint : Spec (.of R) ⟶ levelThree.left :=
  (auxiliaryNormalizedLevelPoint (auxiliaryPointSections f) (auxiliaryRelativePoint f)).left

/-- The normalized full marking retains precisely its normalized coefficient map. -/
@[reassoc] theorem auxiliaryFamilyNormalizedPoint_base :
    auxiliaryFamilyNormalizedPoint f ≫ levelThree.hom =
      auxiliaryNormalizedCoefficientBase (auxiliaryPointSections f) := by
  rw [auxiliaryFamilyNormalizedPoint_def]
  exact (auxiliaryNormalizedLevelPoint
    (auxiliaryPointSections f) (auxiliaryRelativePoint f)).w.trans (Category.id_comp _)

end FLT.Mazur.OddWeierstrassParameter
