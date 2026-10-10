/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalEquation
public import FLT.Mazur.WeierstrassAffineVariableChangeSections

/-!
# The original auxiliary marking on the normalized affine scheme

Transport every original nonidentity label through the constructed algebra
isomorphism. The resulting evaluations are actual sections and return to
the original markings under the actual affine scheme isomorphism.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- Every original auxiliary marking defines an actual evaluation on the normalized chart. -/
def auxiliaryNormalizedEvaluation (a : Labels 4) (ha : a ≠ 1) :
    Coordinate (auxiliaryNormalizedEquation g) 2 →ₐ[R] R :=
  (auxiliaryPullbackEvaluation g a ha).comp
    (affineVariableChangeEquiv (auxiliaryPullbackEquation g) (auxiliaryNormalizedEquation g)
      (auxiliaryFrameChange g) rfl).symm.toAlgHom

/-- Transport back recovers the entire original evaluation, not just its coordinates. -/
theorem auxiliaryNormalizedEvaluation_comp (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryNormalizedEvaluation g a ha).comp
      (affineVariableChangeMap (auxiliaryPullbackEquation g) (auxiliaryNormalizedEquation g)
        (auxiliaryFrameChange g) rfl) = auxiliaryPullbackEvaluation g a ha := by
  apply AlgHom.ext
  intro r
  change auxiliaryPullbackEvaluation g a ha
    ((affineVariableChangeEquiv _ _ _ rfl).symm (affineVariableChangeEquiv _ _ _ rfl r)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- The normalized marking is an actual ring-valued affine section. -/
def auxiliaryNormalizedAffineSection (a : Labels 4) (ha : a ≠ 1) :
    Spec (.of R) ⟶ chartScheme (auxiliaryNormalizedEquation g) 2 :=
  Spec.map (CommRingCat.ofHom (auxiliaryNormalizedEvaluation g a ha).toRingHom)

/-- The actual affine scheme isomorphism returns every normalized marking to its original. -/
theorem auxiliaryNormalizedAffineSection_original (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryNormalizedAffineSection g a ha ≫
      (affineVariableChangeIso (auxiliaryPullbackEquation g) (auxiliaryNormalizedEquation g)
        (auxiliaryFrameChange g) rfl).hom ≫ integralCurveChart (auxiliaryPullbackEquation g) 2 =
      auxiliaryPullbackSection g a ha := by
  have he : auxiliaryNormalizedAffineSection g a ha ≫
      (affineVariableChangeIso (auxiliaryPullbackEquation g) (auxiliaryNormalizedEquation g)
        (auxiliaryFrameChange g) rfl).hom =
      Spec.map (CommRingCat.ofHom (auxiliaryPullbackEvaluation g a ha).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (auxiliaryNormalizedEvaluation_comp g a ha)
  rw [← Category.assoc, he]
  rfl

/-- The normalized marking retains the original base section property. -/
theorem auxiliaryNormalizedAffineSection_base (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryNormalizedAffineSection g a ha ≫ chartStructure (auxiliaryNormalizedEquation g) 2 =
      𝟙 _ := by
  rw [auxiliaryNormalizedAffineSection, chartStructure, specAlgHom_structure]
  exact Spec.map_id _

end FLT.Mazur.UniversalWeierstrass
