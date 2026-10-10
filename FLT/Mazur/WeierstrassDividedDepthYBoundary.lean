/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthOriginalOpen
public import FLT.Mazur.WeierstrassDividedDepthAffine

/-!
# Original Y-boundary points avoid every normalized successive center

The original affine y coordinate pulls back to the scale times the divided
y coordinate. A point over D(y) therefore lies in the unchanged principal
y open of the actual preceding equation, after coefficient normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

/-- The actual preceding divided y coordinate before parameter normalization. -/
abbrev previousY :=
  WeierstrassDilatation.y W (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)

omit [IsDomain R] in
/-- This y coordinate belongs to the actual center of the successive modification. -/
theorem previousY_mem_center :
    previousY e ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6 :=
  Ideal.subset_span (by simp [previousY])

/-- Every divided-chart point over the original D(y) lies in an unchanged target open. -/
theorem mem_previousYTarget (p : chart d)
    (hp : toAffine d p ∈ PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 1)) :
    p ∈ Set.range (originalTarget hπ d e (previousY e)) := by
  let q := (previousChartIso hπ d e).inv p
  have hq : (previousChartIso hπ d e).hom q = p := by
    dsimp only [q]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hn : previousY e ∉ q.asIdeal := by
    intro hy
    apply hp
    change (WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6) (WeierstrassIntegralChart.coord W 2 1) ∈ p.asIdeal
    rw [WeierstrassDilatation.fromOriginal_y, ← hq]
    change (WeierstrassSuccessiveX.previousDepthEquiv π k hπ W d.b3 d.b4 d.b6
      e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6)
      (algebraMap R _ (π ^ k) * WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6) ∈ q.asIdeal
    simpa [WeierstrassSuccessiveX.previousDepthEquiv, previousY] using
      q.asIdeal.mul_mem_left (algebraMap R _ (π ^ k)) hy
  have hr : q ∈ Set.range (PrincipalAffineRefinement.inclusion (previousY e)) := by
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hn
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, by simpa only [originalTarget, Scheme.Hom.comp_apply, ha] using hq⟩

end FLT.Mazur.WeierstrassDividedDepth
