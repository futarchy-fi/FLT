/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationInvariant

/-!
# Every normalized auxiliary marking is invariant under actual marked isomorphisms

Equality of the normalized equations extends to all coordinates of every
original nonidentity label, not just the three labels used for normalization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g k : AuxiliarySectionRing →+* R)
  (e : integralCurve (auxiliaryPullbackEquation g) ≅ integralCurve (auxiliaryPullbackEquation k))
  (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation k) =
    integralCurveStructure (auxiliaryPullbackEquation g))
  (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
    integralCurveZero (auxiliaryPullbackEquation k))
  (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
    auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection k a ha)

include hm in
/-- The three actual normalized frame sections are preserved. -/
theorem auxiliaryNormalizedIso_frame (i : Fin 3) :
    Spec.map (CommRingCat.ofHom (auxiliaryNormalizedFrameEvaluations g i).toRingHom) ≫
        integralCurveChart (auxiliaryNormalizedEquation g) 2 ≫
          (auxiliaryNormalizedIso g k e).hom =
      Spec.map (CommRingCat.ofHom (auxiliaryNormalizedFrameEvaluations k i).toRingHom) ≫
        integralCurveChart (auxiliaryNormalizedEquation k) 2 := by
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

include hb hz hm in
/-- All normalized marked coordinates are intrinsic to the original marked proper cubic. -/
theorem auxiliaryNormalizedMarking_invariant (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 i) =
      auxiliaryNormalizedEvaluation k a ha (coord (auxiliaryNormalizedEquation k) 2 i) := by
  let f := originIsoCoordinateHom (auxiliaryNormalizedEquation g) (auxiliaryNormalizedEquation k)
    (auxiliaryNormalizedEquation_discriminant k)
    (auxiliaryNormalizedIso g k e) (auxiliaryNormalizedIso_base g k e hb)
    (auxiliaryNormalizedIso_zero g k e hz)
  have hf : f (coord (auxiliaryNormalizedEquation k) 2 i) =
      coord (auxiliaryNormalizedEquation g) 2 i :=
    normalizedOriginIso_coordinates (auxiliaryNormalizedEquation g) (auxiliaryNormalizedEquation k)
      (auxiliaryNormalizedEquation_discriminant g)
      (auxiliaryNormalizedEquation_discriminant k) (auxiliaryNormalizedIso g k e)
      (auxiliaryNormalizedIso_base g k e hb) (auxiliaryNormalizedIso_zero g k e hz)
      _ _ (auxiliaryNormalizedFrameEvaluations g) (auxiliaryNormalizedFrameEvaluations k)
      (auxiliaryNormalizedFrameEvaluations_frame g) (auxiliaryNormalizedFrameEvaluations_frame k)
      (auxiliaryNormalizedIso_frame g k e hm) i
  have he : (auxiliaryNormalizedEvaluation g a ha).comp f =
      auxiliaryNormalizedEvaluation k a ha :=
    originIsoCoordinateHom_evaluation
      (auxiliaryNormalizedEquation g) (auxiliaryNormalizedEquation k)
      (auxiliaryNormalizedEquation_discriminant k)
      (auxiliaryNormalizedIso g k e) (auxiliaryNormalizedIso_base g k e hb)
      (auxiliaryNormalizedIso_zero g k e hz)
      (auxiliaryNormalizedEvaluation g a ha) (auxiliaryNormalizedEvaluation k a ha) (by
        simpa only [auxiliaryNormalizedSection, auxiliaryNormalizedAffineSection, Category.assoc]
          using auxiliaryNormalizedIso_mark g k e a ha (hm a ha))
  rw [← hf]
  exact DFunLike.congr_fun he (coord (auxiliaryNormalizedEquation k) 2 i)

end FLT.Mazur.UniversalWeierstrass
