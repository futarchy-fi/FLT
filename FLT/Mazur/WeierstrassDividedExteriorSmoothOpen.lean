/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthCenterSmooth
public import FLT.Mazur.WeierstrassDividedExteriorOriginalOpen
public import FLT.Mazur.WeierstrassDividedFiniteExteriorPullback
public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Whole divided steps preserve the full original smooth open

The retained exterior is unchanged. Every divided-chart point over the
original smooth locus avoids the next center, so the full principal-open
pullbacks cover that entire inverse image.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))

/-- A whole step is unchanged over all points mapping to the original affine smooth locus. -/
theorem Exterior.step_originalSmooth_isIso
    (g : E.whole ⟶ Spec (.of (WeierstrassIntegralChart.Coordinate W 2)))
    (hg : E.dividedChart ≫ g = toAffine d) :
    IsIso (E.stepContraction hπ e ∣_
      g ⁻¹ᵁ (WeierstrassIntegralChart.chartStructure W 2).smoothLocus) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  rcases E.charts_cover z with ⟨p, hp⟩ | ⟨p, hp⟩
  · refine ⟨E.exteriorChart.opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (E.step_exterior_isPullback hπ e)
  · have hp' : toAffine d p ∈ (WeierstrassIntegralChart.chartStructure W 2).smoothLocus := by
      rw [← hg, Scheme.Hom.comp_apply, hp]
      exact hz
    obtain ⟨f, hf, q, hq⟩ := mem_originalSmoothTarget hπ d e p hp'
    refine ⟨(originalTarget hπ d e f ≫ E.dividedChart).opensRange, ⟨q, ?_⟩, ?_⟩
    · simpa only [Scheme.Hom.comp_apply, hq] using hp
    · exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
        (E.stepOriginal_isPullback hπ e f hf)

end FLT.Mazur.WeierstrassDividedDepth
