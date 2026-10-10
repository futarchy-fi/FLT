/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedSections
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassVariableChangeZero

/-!
# Canonical normalization of the original marked proper auxiliary cubic

The affine normalization extends to the original integral cubic, fixes its
original zero section, and retains every original auxiliary marked section.
-/

@[expose] public noncomputable section

open WeierstrassCurve AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The canonical normalization as an actual isomorphism of the original proper cubic. -/
def auxiliaryProperNormalization :
    integralCurve (auxiliaryNormalizedEquation g) ≅ integralCurve (auxiliaryPullbackEquation g) :=
  integralVariableChangeIso _ _ (auxiliaryFrameChange g) rfl

/-- The proper normalization extends the exact original affine normalization. -/
@[reassoc] theorem auxiliaryProperNormalization_affine :
    integralCurveChart (auxiliaryNormalizedEquation g) 2 ≫
        (auxiliaryProperNormalization g).hom =
      (affineVariableChangeIso _ _ (auxiliaryFrameChange g) rfl).hom ≫
        integralCurveChart (auxiliaryPullbackEquation g) 2 :=
  integralVariableChangeIso_affine _ _ _ rfl

/-- The original zero section is retained over every coefficient ring. -/
@[reassoc] theorem auxiliaryProperNormalization_zero :
    integralCurveZero (auxiliaryNormalizedEquation g) ≫ (auxiliaryProperNormalization g).hom =
      integralCurveZero (auxiliaryPullbackEquation g) :=
  integralVariableChangeIso_zero _ _ _ rfl

/-- Each normalized nonidentity label is now a section of the entire proper cubic. -/
def auxiliaryNormalizedSection (a : Labels 4) (ha : a ≠ 1) :
    Spec (.of R) ⟶ integralCurve (auxiliaryNormalizedEquation g) :=
  auxiliaryNormalizedAffineSection g a ha ≫ integralCurveChart (auxiliaryNormalizedEquation g) 2

/-- Proper normalization returns each full original auxiliary scheme section. -/
@[reassoc] theorem auxiliaryNormalizedSection_original (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryNormalizedSection g a ha ≫ (auxiliaryProperNormalization g).hom =
      auxiliaryPullbackSection g a ha := by
  rw [auxiliaryNormalizedSection, Category.assoc, auxiliaryProperNormalization_affine]
  exact auxiliaryNormalizedAffineSection_original g a ha

/-- The normalized proper marking is a section over the unchanged coefficient spectrum. -/
theorem auxiliaryNormalizedSection_base (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryNormalizedSection g a ha ≫ integralCurveStructure (auxiliaryNormalizedEquation g) =
      𝟙 _ := by
  rw [auxiliaryNormalizedSection, Category.assoc, integralCurveChart_structure]
  exact auxiliaryNormalizedAffineSection_base g a ha

end FLT.Mazur.UniversalWeierstrass
