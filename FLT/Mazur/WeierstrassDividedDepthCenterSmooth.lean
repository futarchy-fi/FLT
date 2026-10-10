/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthYBoundary
public import FLT.Mazur.WeierstrassModificationCenterSmooth

/-!
# Successive centers miss the full original relative smooth locus

A point in a successive center has zero parameter and divided coordinates.
Its original coordinates and next-depth scale therefore vanish too, which
contradicts the original affine relative smooth criterion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
open WeierstrassIntegralChart
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k)
  (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)

/-- The normalized successive center cannot lie above an original smooth affine point. -/
theorem previousCenter_not_le_of_original_smooth (q : PrimeSpectrum A)
    (hq : toAffine d ((previousChartIso hπ d e).hom q) ∈ (chartStructure W 2).smoothLocus) :
    ¬ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6 ≤ q.asIdeal := by
  intro hc
  have hπq : algebraMap R A π ∈ q.asIdeal := hc (Ideal.subset_span (by simp))
  have hxq : WeierstrassDilatation.x W (π ^ k)
      (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) ∈ q.asIdeal :=
    hc (Ideal.subset_span (by simp))
  have hyq : previousY e ∈ q.asIdeal := hc (previousY_mem_center e)
  let v := WeierstrassSuccessiveX.previousDepthEquiv π k hπ W d.b3 d.b4 d.b6
    e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6
  have hn := smooth_avoids_modification_generators W (π ^ (k + 1)) e.b3 e.b4
    e.factor3 e.factor4 _ hq
  rcases hn with hs | hx | hy
  · apply hs
    change v ((WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6) (algebraMap R _ (π ^ (k + 1)))) ∈ q.asIdeal
    rw [AlgHom.commutes, AlgEquiv.commutes, map_pow]
    rw [pow_succ (algebraMap R A π) k]
    exact q.asIdeal.mul_mem_left _ hπq
  · apply hx
    change v ((WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6) (coord W 2 0)) ∈ q.asIdeal
    rw [WeierstrassDilatation.fromOriginal_x]
    simpa [v, WeierstrassSuccessiveX.previousDepthEquiv] using
      q.asIdeal.mul_mem_left (algebraMap R A (π ^ k)) hxq
  · apply hy
    change v ((WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6) (coord W 2 1)) ∈ q.asIdeal
    rw [WeierstrassDilatation.fromOriginal_y]
    simpa [v, WeierstrassSuccessiveX.previousDepthEquiv, previousY] using
      q.asIdeal.mul_mem_left (algebraMap R A (π ^ k)) hyq

/-- Every divided point over the original smooth open lies in a full unchanged principal open. -/
theorem mem_originalSmoothTarget (p : chart d)
    (hp : toAffine d p ∈ (chartStructure W 2).smoothLocus) :
    ∃ f, f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6 ∧
      p ∈ Set.range (originalTarget hπ d e f) := by
  let q := (previousChartIso hπ d e).inv p
  have he : (previousChartIso hπ d e).hom q = p := by
    dsimp only [q]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hn := previousCenter_not_le_of_original_smooth hπ d e q (by rwa [he])
  change ¬ ∀ f, f ∈ _ → f ∈ q.asIdeal at hn
  push Not at hn
  obtain ⟨f, hf, hq⟩ := hn
  refine ⟨f, hf, ?_⟩
  have hr : q ∈ Set.range (PrincipalAffineRefinement.inclusion f) := by
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hq
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, by simpa only [originalTarget, Scheme.Hom.comp_apply, ha] using he⟩

end FLT.Mazur.WeierstrassDividedDepth
