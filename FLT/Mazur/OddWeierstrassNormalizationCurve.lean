/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedMarking
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# The full original curve under odd auxiliary normalization

The proper group comparison extends to the entire smooth generalized curve,
including characteristic two and nonreduced coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original generalized curve of the pulled auxiliary equation. -/
def auxiliaryPullbackCurve : GeneralizedEllipticCurve (Spec (.of R)) :=
  integralGeneralizedEllipticCurve _ (auxiliaryPullbackEquation_discriminant g)

/-- The entire normalized generalized curve with its original regular action. -/
def auxiliaryNormalizedCurve : GeneralizedEllipticCurve (Spec (.of R)) :=
  integralGeneralizedEllipticCurve _ (auxiliaryNormalizedEquation_discriminant g)

instance auxiliaryPullbackCurve_smooth : Smooth (auxiliaryPullbackCurve g).curve.hom :=
  integralCurveStructure_smooth _ (auxiliaryPullbackEquation_discriminant g)

instance auxiliaryNormalizedCurve_smooth : Smooth (auxiliaryNormalizedCurve g).curve.hom :=
  integralCurveStructure_smooth _ (auxiliaryNormalizedEquation_discriminant g)

/-- Normalization compares full families, including their actions and zero sections. -/
irreducible_def auxiliaryNormalizationCurveIso :
    auxiliaryNormalizedCurve g ≅ auxiliaryPullbackCurve g := by
  let e : (auxiliaryNormalizedCurve g).group ≅ (auxiliaryPullbackCurve g).group :=
    (CommGrp.forget _).mapIso (auxiliaryNormalizationGroupIso g)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ e

/-- The full comparison retains exactly the constructed normalization group map. -/
theorem auxiliaryNormalizationCurveIso_group :
    (auxiliaryNormalizationCurveIso g).hom.group =
      (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom := by
  rw [auxiliaryNormalizationCurveIso_def]
  rfl

/-- Its inverse retains the original inverse group normalization. -/
theorem auxiliaryNormalizationCurveIso_inv_group :
    (auxiliaryNormalizationCurveIso g).inv.group =
      (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom := by
  rw [auxiliaryNormalizationCurveIso_def]
  rfl

end FLT.Mazur.OddWeierstrassParameter
