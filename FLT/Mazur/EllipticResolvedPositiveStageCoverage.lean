/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedPositiveExteriorCoverage
public import FLT.Mazur.EllipticResolvedZeroExteriorCover
public import FLT.Mazur.EllipticResolvedZeroBoundaryCoverage

/-!
# Complete arithmetic smooth-chart coverage at positive final stage

The first exterior closes the remaining atlas gap. Every smooth point of the
actual resolved fiber lies in an arithmetic component chart when depth is at least two.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "p" => resolvedSplitStructure A D
local notation "inc" => Scheme.Opens.ι (Scheme.Hom.smoothLocus (resolvedSplitStructure A D))
local notation "chart" => resolvedComponentChart A D r

/-- Every smooth point of the zero-depth exterior lies in an arithmetic component chart. -/
theorem resolvedComponentCharts_cover_zero_exterior (hk0 : 0 < depth / 2)
    (z : (p).smoothLocus.toScheme)
    (hz : inc z ∈ Set.range (resolvedRetainedExteriorChart A D 0 hk0)) :
    ∃ i, z ∈ Set.range (chart i) := by
  have h : inc z ∈ Set.range (resolvedRetainedBoundaryChart A D 0 hk0) ∪
      Set.range (resolvedRetainedIncidenceChart A D 0 hk0) := by
    rw [resolvedZeroExterior_smooth_boundary_cover A D 0 hk0 rfl]
    exact ⟨hz, z.property⟩
  rcases h with hb | ht
  · exact resolvedComponentCharts_cover_infinity A D r z
      (resolvedZeroBoundary_range_subset_infinity A D 0 hk0 rfl hb)
  · by_cases hn : 1 < depth / 2
    · rw [resolvedRetainedIncidenceChart_range_eq_next A D 0 hk0 hn] at ht
      exact resolvedComponentCharts_cover_retained A D r 1 (by omega) hn z ht
    · apply resolvedComponentCharts_cover_terminal A D r hk0 z
      rw [← resolvedTerminalTensorChart_range A D]
      exact resolvedLastIncidenceChart_range_subset_terminal A D 0 hk0 (by omega) ht

/-- The actual arithmetic component charts cover the whole smooth resolved fiber at depth ≥ 2. -/
theorem resolvedComponentCharts_cover_positive_stage (hk0 : 0 < depth / 2)
    (z : (p).smoothLocus.toScheme) : ∃ i, z ∈ Set.range (chart i) := by
  by_contra hz
  have h := resolvedComponentCharts_uncovered_zero_exterior A D r hk0 z hz
  have he := resolvedRetainedExteriorChart_range_index A D 0 hk0
    ⟨depth / 2 + 1, by omega⟩ (by
      change depth / 2 - (0 + 1) + 2 = depth / 2 + 1
      omega)
  rw [← he] at h
  exact hz (resolvedComponentCharts_cover_zero_exterior A D r hk0 z h)

end FLT.Mazur.WeierstrassDividedDepth
