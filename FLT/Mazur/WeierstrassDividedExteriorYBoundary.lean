/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthYBoundary
public import FLT.Mazur.WeierstrassDividedExteriorOriginalOpen
public import FLT.Mazur.WeierstrassDividedFiniteExteriorPullback
public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Each whole divided step is unchanged over the original Y-boundary

The old exterior has its identity pullback. On the divided chart, original
Y-boundary points avoid the actual successive center. These full local
comparisons give an isomorphism over the complete original-boundary preimage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))

/-- The full whole step is unchanged wherever the original affine y coordinate is invertible. -/
theorem Exterior.step_originalY_isIso
    (g : E.whole ⟶ Spec (.of (WeierstrassIntegralChart.Coordinate W 2)))
    (hg : E.dividedChart ≫ g = toAffine d) :
    IsIso (E.stepContraction hπ e ∣_
      g ⁻¹ᵁ PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 1)) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  rcases E.charts_cover z with ⟨p, hp⟩ | ⟨p, hp⟩
  · refine ⟨E.exteriorChart.opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (E.step_exterior_isPullback hπ e)
  · have hp' : toAffine d p ∈
        PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 1) := by
      rw [← hg, Scheme.Hom.comp_apply, hp]
      exact hz
    obtain ⟨q, hq⟩ := mem_previousYTarget hπ d e p hp'
    refine ⟨(originalTarget hπ d e (previousY e) ≫ E.dividedChart).opensRange,
      ⟨q, ?_⟩, ?_⟩
    · simpa only [Scheme.Hom.comp_apply, hq] using hp
    · exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
        (E.stepOriginal_isPullback hπ e (previousY e) (previousY_mem_center e))

end FLT.Mazur.WeierstrassDividedDepth
