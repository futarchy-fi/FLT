/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# The original cubic as the pushout of its Y/Z charts

The actual coordinate transition identifies their complete intersection.
Together with the proved two-chart coverage, this realizes the entire
projective cubic as the open pushout used for a global replacement.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The affine chart's Y-invertible boundary, mapped into the original Y-chart. -/
def affineBoundaryToY : overlapScheme W 2 1 ⟶ chartScheme W 1 :=
  chartTransition W 2 1 ≫ overlapInclusion W 1 2

instance affineBoundaryToY_isOpenImmersion : IsOpenImmersion (affineBoundaryToY W) := by
  unfold affineBoundaryToY
  let _ : IsIso (chartTransition W 2 1) :=
    inferInstanceAs (IsIso ((integralCurveGlueData W).t ⟨2⟩ ⟨1⟩))
  infer_instance

/-- The actual Y/Z overlap is the full intersection in the original projective cubic. -/
theorem yz_isPullback :
    IsPullback (affineBoundaryToY W) (overlapInclusion W 2 1)
      (integralCurveChart W 1) (integralCurveChart W 2) := by
  exact (IsPullback.of_isLimit ((integralCurveGlueData W).vPullbackConeIsLimit ⟨2⟩ ⟨1⟩)).flip

/-- The entire original projective cubic is the pushout of its Y/Z overlap. -/
def yzPushoutIso : pushout (affineBoundaryToY W) (overlapInclusion W 2 1) ≅ integralCurve W :=
  SchemeOpenPushout.coverIso _ _ _ _ (yz_isPullback W) (integralCurve_yz_cover W)

/-- The pushout comparison retains the original chart at infinity. -/
@[reassoc (attr := simp)] theorem inl_yzPushoutIso :
    pushout.inl (affineBoundaryToY W) (overlapInclusion W 2 1) ≫ (yzPushoutIso W).hom =
      integralCurveChart W 1 := SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The pushout comparison retains the original affine cubic chart. -/
@[reassoc (attr := simp)] theorem inr_yzPushoutIso :
    pushout.inr (affineBoundaryToY W) (overlapInclusion W 2 1) ≫ (yzPushoutIso W).hom =
      integralCurveChart W 2 := SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassIntegralChart
