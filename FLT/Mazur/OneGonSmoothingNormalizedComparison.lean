/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingUniversalComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliaryActualNormalizationIso

/-!
# The actual smooth boundary family compares with its normalized auxiliary family

For an actual level-four point over the original boundary coefficient map,
the original auxiliary cubic is exactly the boundary equation. Composing
this equality comparison with the constructed proper normalization retains
the original base, infinity, and each nonidentity auxiliary label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  (f : Spec (.of R) ⟶ levelFour.left)
  (hb : f ≫ levelFour.hom = Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))

include hb in
/-- The actual auxiliary point has the original boundary coefficient homomorphism. -/
theorem smoothAuxiliary_coefficient :
    auxiliaryCoefficientHom (auxiliaryPointSections f) = smoothParameter t h₂ ht hf := by
  exact congrArg CommRingCat.Hom.hom
    (Spec.map_injective ((auxiliaryPointSections_base f).trans hb))

include hb in
/-- The actual auxiliary cubic is precisely the original boundary equation. -/
theorem smoothAuxiliary_equation :
    auxiliaryPullbackEquation (auxiliaryPointSections f) = equation t := by
  rw [auxiliaryPullbackEquation_coefficient, smoothAuxiliary_coefficient t h₂ ht hf f hb,
    smoothParameter_equation]

/-- The original auxiliary family is the original boundary cubic, with no changed model. -/
def smoothAuxiliaryIso :
    integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≅ (family t).left :=
  eqToIso (congrArg integralCurve (smoothAuxiliary_equation t h₂ ht hf f hb))

/-- The auxiliary comparison is over the unchanged original boundary coefficient ring. -/
@[reassoc] theorem smoothAuxiliaryIso_base :
    (smoothAuxiliaryIso t h₂ ht hf f hb).hom ≫ (family t).hom =
      integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f)) :=
  equationTransport_structure (smoothAuxiliary_equation t h₂ ht hf f hb)

/-- The actual auxiliary origin is exactly the original boundary infinity. -/
@[reassoc] theorem smoothAuxiliaryIso_zero :
    integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≫
      (smoothAuxiliaryIso t h₂ ht hf f hb).hom = marking t :=
  equationTransport_zero (smoothAuxiliary_equation t h₂ ht hf f hb)

/-- The original auxiliary sections as actual sections of the boundary cubic. -/
def smoothAuxiliarySection (a : Labels 4) (ha : a ≠ 1) :
    Spec (.of R) ⟶ (family t).left :=
  auxiliaryPullbackSection (auxiliaryPointSections f) a ha ≫
    (smoothAuxiliaryIso t h₂ ht hf f hb).hom

/-- The actual family at the normalized auxiliary point compares to the boundary family. -/
def smoothNormalizedIso :
    integralCurve (auxiliaryPullbackEquation
      (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) ≅ (family t).left :=
  auxiliaryFamilyNormalizationIso f ≪≫ smoothAuxiliaryIso t h₂ ht hf f hb

/-- The normalized comparison keeps the original boundary base. -/
@[reassoc] theorem smoothNormalizedIso_base :
    (smoothNormalizedIso t h₂ ht hf f hb).hom ≫ (family t).hom =
      integralCurveStructure (auxiliaryPullbackEquation
        (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) := by
  rw [smoothNormalizedIso, Iso.trans_hom, Category.assoc, smoothAuxiliaryIso_base]
  exact auxiliaryFamilyNormalizationIso_base f

/-- Normalization retains infinity as the original boundary marking. -/
@[reassoc] theorem smoothNormalizedIso_zero :
    integralCurveZero (auxiliaryPullbackEquation
      (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) ≫
        (smoothNormalizedIso t h₂ ht hf f hb).hom = marking t := by
  rw [smoothNormalizedIso, Iso.trans_hom, ← Category.assoc,
    auxiliaryFamilyNormalizationIso_zero, smoothAuxiliaryIso_zero]

/-- Every original nonidentity auxiliary marking is retained on the boundary cubic. -/
@[reassoc] theorem smoothNormalizedIso_mark (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryPullbackSection (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) a ha ≫
      (smoothNormalizedIso t h₂ ht hf f hb).hom = smoothAuxiliarySection t h₂ ht hf f hb a ha := by
  rw [smoothNormalizedIso, Iso.trans_hom, ← Category.assoc,
    auxiliaryFamilyNormalizationIso_mark]
  rfl

end FLT.Mazur.OneGonSmoothing
