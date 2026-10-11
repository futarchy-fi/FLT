/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthOriginalOpen
public import FLT.Mazur.WeierstrassDividedDepthAffine
public import FLT.Mazur.WeierstrassDividedExteriorOriginalOpen
public import FLT.Mazur.WeierstrassDividedFiniteExteriorPullback
public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Original X-open points avoid every normalized successive center

The original affine x coordinate pulls back to the scale times the divided
x coordinate. A point over D(x) therefore lies in the unchanged principal
x open of the actual preceding equation, after coefficient normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

/-- The actual preceding divided x coordinate before parameter normalization. -/
abbrev previousX :=
  WeierstrassDilatation.x W (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)

omit [IsDomain R] in
/-- This x coordinate belongs to the actual center of the successive modification. -/
theorem previousX_mem_center :
    previousX e ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6 :=
  Ideal.subset_span (by simp [previousX])

/-- Every divided-chart point over the original D(x) lies in an unchanged target open. -/
theorem mem_previousXTarget (p : chart d)
    (hp : toAffine d p ∈ PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 0)) :
    p ∈ Set.range (originalTarget hπ d e (previousX e)) := by
  let q := (previousChartIso hπ d e).inv p
  have hq : (previousChartIso hπ d e).hom q = p := by
    dsimp only [q]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hn : previousX e ∉ q.asIdeal := by
    intro hx
    apply hp
    change (WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6) (WeierstrassIntegralChart.coord W 2 0) ∈ p.asIdeal
    rw [WeierstrassDilatation.fromOriginal_x, ← hq]
    change (WeierstrassSuccessiveX.previousDepthEquiv π k hπ W d.b3 d.b4 d.b6
      e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6)
      (algebraMap R _ (π ^ k) * WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6) ∈ q.asIdeal
    simpa [WeierstrassSuccessiveX.previousDepthEquiv, previousX] using
      q.asIdeal.mul_mem_left (algebraMap R _ (π ^ k)) hx
  have hr : q ∈ Set.range (PrincipalAffineRefinement.inclusion (previousX e)) := by
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hn
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, by simpa only [originalTarget, Scheme.Hom.comp_apply, ha] using hq⟩

variable (E : Exterior d)

/-- The full whole step is unchanged wherever the original affine x coordinate is invertible. -/
theorem Exterior.step_originalX_isIso
    (g : E.whole ⟶ Spec (.of (WeierstrassIntegralChart.Coordinate W 2)))
    (hg : E.dividedChart ≫ g = toAffine d) :
    IsIso (E.stepContraction hπ e ∣_
      g ⁻¹ᵁ PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 0)) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  rcases E.charts_cover z with ⟨p, hp⟩ | ⟨p, hp⟩
  · refine ⟨E.exteriorChart.opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (E.step_exterior_isPullback hπ e)
  · have hp' : toAffine d p ∈
        PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 0) := by
      rw [← hg, Scheme.Hom.comp_apply, hp]
      exact hz
    obtain ⟨q, hq⟩ := mem_previousXTarget hπ d e p hp'
    refine ⟨(originalTarget hπ d e (previousX e) ≫ E.dividedChart).opensRange,
      ⟨q, ?_⟩, ?_⟩
    · simpa only [Scheme.Hom.comp_apply, hq] using hp
    · exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
        (E.stepOriginal_isPullback hπ e (previousX e) (previousX_mem_center e))

end FLT.Mazur.WeierstrassDividedDepth
