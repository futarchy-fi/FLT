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
# Original scale-open points avoid every normalized successive center

The original uniformizer is retained by every coefficient normalization.
A point over its principal open lies in the unchanged scale open of every
actual preceding equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

/-- The actual preceding coefficient scale before parameter normalization. -/
abbrev previousScale :=
  algebraMap R
    (WeierstrassDilatation.Coordinate W (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)) π

omit [IsDomain R] in
/-- This scale belongs to the actual center of the successive modification. -/
theorem previousScale_mem_center :
    previousScale e ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6 :=
  Ideal.subset_span (by simp [previousScale])

/-- Every divided-chart point over the original D(π) lies in an unchanged target open. -/
theorem mem_previousScaleTarget (p : chart d)
    (hp : toAffine d p ∈ PrimeSpectrum.basicOpen
      (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) π)) :
    p ∈ Set.range (originalTarget hπ d e (previousScale e)) := by
  let q := (previousChartIso hπ d e).inv p
  have hq : (previousChartIso hπ d e).hom q = p := by
    dsimp only [q]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hn : previousScale e ∉ q.asIdeal := by
    intro hx
    apply hp
    change (WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6)
      (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) π) ∈ p.asIdeal
    rw [AlgHom.commutes, ← hq]
    change (WeierstrassSuccessiveX.previousDepthEquiv π k hπ W d.b3 d.b4 d.b6
      e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6)
      (algebraMap R _ π) ∈ q.asIdeal
    rw [AlgEquiv.commutes]
    exact hx
  have hr : q ∈ Set.range (PrincipalAffineRefinement.inclusion (previousScale e)) := by
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hn
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, by simpa only [originalTarget, Scheme.Hom.comp_apply, ha] using hq⟩

variable (E : Exterior d)

/-- The full whole step is unchanged wherever the original coefficient scale is invertible. -/
theorem Exterior.step_originalScale_isIso
    (g : E.whole ⟶ Spec (.of (WeierstrassIntegralChart.Coordinate W 2)))
    (hg : E.dividedChart ≫ g = toAffine d) :
    IsIso (E.stepContraction hπ e ∣_
      g ⁻¹ᵁ PrimeSpectrum.basicOpen
        (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) π)) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  rcases E.charts_cover z with ⟨p, hp⟩ | ⟨p, hp⟩
  · refine ⟨E.exteriorChart.opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (E.step_exterior_isPullback hπ e)
  · have hp' : toAffine d p ∈
        PrimeSpectrum.basicOpen (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) π) := by
      rw [← hg, Scheme.Hom.comp_apply, hp]
      exact hz
    obtain ⟨q, hq⟩ := mem_previousScaleTarget hπ d e p hp'
    refine ⟨(originalTarget hπ d e (previousScale e) ≫ E.dividedChart).opensRange,
      ⟨q, ?_⟩, ?_⟩
    · simpa only [Scheme.Hom.comp_apply, hq] using hp
    · exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
        (E.stepOriginal_isPullback hπ e (previousScale e) (previousScale_mem_center e))

end FLT.Mazur.WeierstrassDividedDepth
