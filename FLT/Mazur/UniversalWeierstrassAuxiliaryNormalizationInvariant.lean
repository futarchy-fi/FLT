/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedIsomorphism
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedFrame
public import FLT.Mazur.WeierstrassNormalizedOriginIsomorphism

/-!
# Canonical auxiliary normalization is invariant under actual marked isomorphisms

The equation and unit separation do not depend on the original Weierstrass
presentation. The hypothesis is an actual isomorphism of marked proper cubics.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

/-- The three original normalized evaluations, indexed in frame order. -/
def auxiliaryNormalizedFrameEvaluations (g : AuxiliarySectionRing →+* R) :
    Fin 3 → Coordinate (auxiliaryNormalizedEquation g) 2 →ₐ[R] R :=
  ![auxiliaryNormalizedEvaluation g frameLabelFirst frameLabelFirst_ne,
    auxiliaryNormalizedEvaluation g frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne),
    auxiliaryNormalizedEvaluation g frameLabelThird frameLabelThird_ne]

/-- These are the actual normalized frame evaluations with the constructed unit separation. -/
theorem auxiliaryNormalizedFrameEvaluations_frame (g : AuxiliarySectionRing →+* R) :
    IsNormalizedEvaluationFrame (auxiliaryNormalizedEquation g) (auxiliaryFrameSeparation g)
      (auxiliaryNormalizedFrameEvaluations g) :=
  ⟨auxiliaryNormalizedEvaluation_first g, auxiliaryNormalizedEvaluation_inverse g,
    auxiliaryNormalizedEvaluation_third g⟩

/-- The canonical normalized equation and separation are invariant under marked isomorphism. -/
theorem auxiliaryNormalization_invariant (g k : AuxiliarySectionRing →+* R)
    (e : integralCurve (auxiliaryPullbackEquation g) ≅ integralCurve (auxiliaryPullbackEquation k))
    (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation k) =
      integralCurveStructure (auxiliaryPullbackEquation g))
    (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation k))
    (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
      auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection k a ha) :
    auxiliaryNormalizedEquation g = auxiliaryNormalizedEquation k ∧
      auxiliaryFrameSeparation g = auxiliaryFrameSeparation k := by
  apply normalizedOriginIso_equation_eq _ _ (auxiliaryNormalizedEquation_discriminant g)
    (auxiliaryNormalizedEquation_discriminant k) (auxiliaryNormalizedIso g k e)
    (auxiliaryNormalizedIso_base g k e hb) (auxiliaryNormalizedIso_zero g k e hz)
    _ _ (auxiliaryNormalizedFrameEvaluations g) (auxiliaryNormalizedFrameEvaluations k)
    (auxiliaryNormalizedFrameEvaluations_frame g) (auxiliaryNormalizedFrameEvaluations_frame k)
  intro i
  fin_cases i
  · simpa [auxiliaryNormalizedSection, auxiliaryNormalizedAffineSection,
      auxiliaryNormalizedFrameEvaluations, Category.assoc] using
      auxiliaryNormalizedIso_mark g k e frameLabelFirst frameLabelFirst_ne (hm _ _)
  · simpa [auxiliaryNormalizedSection, auxiliaryNormalizedAffineSection,
      auxiliaryNormalizedFrameEvaluations, Category.assoc] using
      auxiliaryNormalizedIso_mark g k e frameLabelFirst⁻¹
        (inv_ne_one.mpr frameLabelFirst_ne) (hm _ _)
  · simpa [auxiliaryNormalizedSection, auxiliaryNormalizedAffineSection,
      auxiliaryNormalizedFrameEvaluations, Category.assoc] using
      auxiliaryNormalizedIso_mark g k e frameLabelThird frameLabelThird_ne (hm _ _)

end FLT.Mazur.UniversalWeierstrass
